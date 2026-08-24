{-# LANGUAGE
    ViewPatterns
  , OverloadedStrings
  , LambdaCase
  , TupleSections
  , ScopedTypeVariables
  , TypeApplications
  , RecordWildCards
#-}

module Control.Monad.CheckedExcept.Plugin.Defaulting
  ( mkDefaultingPlugin
  ) where

import GHC.Plugins hiding ((<>), DefaultingPlugin)
import GHC.Tc.Types (DefaultingPlugin (..), DefaultingProposal (..))
import GHC.Tc.Types.Constraint (WantedConstraints (..), Ct, Implication (..), ctPred)
import qualified GHC.Tc.Plugin as TC
import GHC.Tc.Plugin (tcPluginTrace)
import GHC.Tc.Utils.TcType (eqType, isMetaTyVarTy)
import GHC.Core.Predicate (getClassPredTys_maybe)
import GHC.Core.Class (Class, classKey)
import GHC.Types.Unique (hasKey)
import GHC.Builtin.Names (consDataConKey)
import GHC.Data.Bag (bagToList)
import Data.List (nubBy)
import qualified GHC.Driver.Plugins as DP

data Environment = Environment
  { containsClass :: Class
  , elemClass :: Class
  , nubTyFam :: TyCon
  , verbose :: Bool
  }

data MetaBounds = MetaBounds
  { lowerBounds :: [Type]
  , upperBounds :: [Type]
  , proposalCts :: [Ct]
  }

type BoundsMap = [(TcTyVar, MetaBounds)]

mkDefaultingPlugin :: DP.DefaultingPlugin
mkDefaultingPlugin opts = checkedExceptDefaultingPlugin opts

checkedExceptDefaultingPlugin :: DP.DefaultingPlugin
checkedExceptDefaultingPlugin opts = Just $ DefaultingPlugin
  { dePluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsClass <- lookupClass checkedExceptMod "Contains"
      elemClass <- lookupClass checkedExceptMod "Elem"
      nubTyFam <- lookupTyFam checkedExceptMod "Nub"
      let verbose = "verbose" `elem` opts
      pure Environment {..}
  , dePluginRun = runDefaulting
  , dePluginStop = const $ pure ()
  }

lookupCheckedExceptMod :: TC.TcPluginM Module
lookupCheckedExceptMod = do
  findResult <- TC.findImportedModule (mkModuleName "Control.Monad.CheckedExcept") NoPkgQual
  case findResult of
    TC.Found _ modCE -> pure modCE
    _ -> fail "checked-exceptions: could not find Control.Monad.CheckedExcept"

lookupClass :: Module -> String -> TC.TcPluginM Class
lookupClass modCE name = do
  name' <- TC.lookupOrig modCE (mkClsOcc name)
  TC.tcLookupClass name'

lookupTyFam :: Module -> String -> TC.TcPluginM TyCon
lookupTyFam modCE name = do
  name' <- TC.lookupOrig modCE (mkTcOcc name)
  TC.tcLookupTyCon name'

runDefaulting :: Environment -> WantedConstraints -> TC.TcPluginM [DefaultingProposal]
runDefaulting env@Environment {..} wc = do
  let cts = gatherCts wc
      givens = gatherGivens wc
      bounds = foldr (insertGiven env) (foldr (insertCt env) [] cts) givens
  proposals <- mapM (uncurry (mkProposal env)) bounds
  when verbose $ tcTrace "proposals" (length proposals)
  pure proposals

gatherCts :: WantedConstraints -> [Ct]
gatherCts wc =
  bagToList (wc_simple wc) ++ concatMap gatherImplCts (bagToList (wc_impl wc))

gatherImplCts :: Implication -> [Ct]
gatherImplCts implic = gatherCts (ic_wanted implic)

-- | Implication givens can mention the same exception-list metavariables as
-- wanteds in nested contexts.
gatherGivens :: WantedConstraints -> [EvVar]
gatherGivens wc = concatMap gatherImplGivens (bagToList (wc_impl wc))

gatherImplGivens :: Implication -> [EvVar]
gatherImplGivens implic =
  ic_given implic ++ concatMap gatherImplGivens (bagToList (wc_impl (ic_wanted implic)))

insertCt :: Environment -> Ct -> BoundsMap -> BoundsMap
insertCt env ct acc = insertFromPred env (Just ct) (ctPred ct) acc

insertGiven :: Environment -> EvVar -> BoundsMap -> BoundsMap
insertGiven env ev acc = insertFromPred env Nothing (varType ev) acc

insertFromPred :: Environment -> Maybe Ct -> Type -> BoundsMap -> BoundsMap
insertFromPred Environment {containsClass, elemClass} mct classPred acc =
  case getClassPredTys_maybe classPred of
    Just (cls, [es1, es2]) ->
      if classKey cls == classKey containsClass
        then foldr (addContainsBound mct es1 es2) acc (metaListVars es1 ++ metaListVars es2)
        else if classKey cls == classKey elemClass
        then foldr (addElemBound mct es1 es2) acc (metaListVars es2)
        else acc
    _ -> acc

lookupBounds :: TcTyVar -> BoundsMap -> MetaBounds
lookupBounds alpha bounds =
  case lookup alpha bounds of
    Just b -> b
    Nothing -> MetaBounds [] [] []

upsertBounds :: TcTyVar -> MetaBounds -> BoundsMap -> BoundsMap
upsertBounds alpha new bounds =
  case break ((== alpha) . fst) bounds of
    (_, (_, old) : rest) -> (alpha, mergeBounds old new) : rest
    (_, []) -> (alpha, new) : bounds

mergeBounds :: MetaBounds -> MetaBounds -> MetaBounds
mergeBounds old new =
  MetaBounds
    { lowerBounds = lowerBounds old <> lowerBounds new
    , upperBounds = upperBounds old <> upperBounds new
    , proposalCts = proposalCts old <> proposalCts new
    }

addContainsBound :: Maybe Ct -> Type -> Type -> TcTyVar -> BoundsMap -> BoundsMap
addContainsBound mct es1 es2 alpha acc =
  let old = lookupBounds alpha acc
      new =
        if isMetaTyVarTy es1
          then old {upperBounds = es2 : upperBounds old, proposalCts = maybeToList mct <> proposalCts old}
          else if isMetaTyVarTy es2
            then old {lowerBounds = es1 : lowerBounds old, proposalCts = maybeToList mct <> proposalCts old}
            else old
  in upsertBounds alpha new acc

addElemBound :: Maybe Ct -> Type -> Type -> TcTyVar -> BoundsMap -> BoundsMap
addElemBound mct ty _es alpha acc =
  let old = lookupBounds alpha acc
      singletonLi = mkPromotedListTy tYPEKind [ty]
      new = old {lowerBounds = singletonLi : lowerBounds old, proposalCts = maybeToList mct <> proposalCts old}
  in upsertBounds alpha new acc

maybeToList :: Maybe a -> [a]
maybeToList = maybe [] pure

metaListVars :: Type -> [TcTyVar]
metaListVars ty =
  case getTyVar_maybe ty of
    Just tv ->
      if isMetaTyVarTy ty && eqType (tyVarKind tv) (mkPromotedListTy tYPEKind [])
        then [tv]
        else []
    _ -> []

mkProposal ::
  Environment ->
  TcTyVar ->
  MetaBounds ->
  TC.TcPluginM DefaultingProposal
mkProposal Environment {nubTyFam, verbose} alpha MetaBounds {lowerBounds, upperBounds, proposalCts} = do
  zonkedLower <- traverse TC.zonkTcType lowerBounds
  zonkedUpper <- traverse TC.zonkTcType upperBounds
  let lowerElems = concatMap lowerBoundElems zonkedLower
      emptyLower = mkPromotedListTy tYPEKind []
      unionLower = uniquePromotedList lowerElems
      nubLower = mkTyConApp nubTyFam [unionLower]
      -- Only propose Nub union (not raw unionLower): an early non-nub default
      -- can fail the whole defaulting block before later bounds arrive.
      proposals =
        [ [(alpha, emptyLower)]
        , [(alpha, nubLower)]
        , [(alpha, ub) | ub <- zonkedUpper]
        ]
  when verbose $
    tcTrace "defaulting" (ppr alpha, ppr unionLower, length proposalCts)
  pure $
    DefaultingProposal
      { deProposals = proposals
      , deProposalCts = proposalCts
      }

uniquePromotedList :: [Type] -> Type
uniquePromotedList tys = mkPromotedListTy tYPEKind $ nubBy eqType tys

-- | Peel list elements from a promoted list, or @[]@ when @ty@ is still an
-- unresolved metavar (the plugin is re-run as more constraints land).
lowerBoundElems :: Type -> [Type]
lowerBoundElems ty =
  case extractMPromotedList ty of
    Just ts -> ts
    Nothing ->
      if isMetaTyVarTy ty
        then []
        else case splitTyConAppIgnoringKind ty of
          Just (tc, _, [t, ts]) ->
            if tc `hasKey` consDataConKey
              then t : lowerBoundElems ts
              else []
          Just (tc, _, []) ->
            if tc `hasKey` nilDataConKey then [] else []
          _ -> []

extractMPromotedList :: Type -> Maybe [Type]
extractMPromotedList = go
  where
    go listTy =
      case splitTyConAppIgnoringKind listTy of
        Just (tc, _, [t, ts]) ->
          assert (tc `hasKey` consDataConKey) $
            case go ts of
              Nothing -> Nothing
              Just ts' -> Just (t : ts')
        Just (tc, _, []) ->
          assert (tc `hasKey` nilDataConKey) $
            Just []
        _ -> Nothing

splitTyConAppIgnoringKind :: Type -> Maybe (TyCon, [Type], [Type])
splitTyConAppIgnoringKind ty = do
  (tyCon, tys) <- splitTyConApp_maybe ty
  let (invisTys, visTys) = partitionInvisibleTypes tyCon tys
  pure (tyCon, invisTys, visTys)

tcTrace :: Outputable a => String -> a -> TC.TcPluginM ()
tcTrace label x =
  tcPluginTrace ("[checked-exceptions] " <> label) (ppr x)

when :: Applicative f => Bool -> f () -> f ()
when p act = if p then act else pure ()
