{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}

module Control.Monad.CheckedExcept.Plugin.Bind
  ( bindPlugin
  , tcPrintLn
  , tcPrint
  , tcPrintOutputable
  , tcTraceLabel)
where

import GHC.Plugins hiding ((<>))
import GHC.Tc.Types.Constraint
import qualified GHC.Tc.Plugin as TC
import qualified GHC.Tc.Types as TC
import GHC.Tc.Types.Evidence (EvTerm (..), evCast, mkEvCast)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Tc.Plugin (tcPluginTrace)
import Data.List (nubBy)
import GHC.Core.Map.Type (deBruijnize)
import Data.Function (on)
import GHC.Types.Unique (hasKey)
import GHC.Builtin.Names (consDataConKey)
import GHC.Core.TyCo.Compare (eqType)
import qualified GHC.Tc.Solver.Solve as TS
import qualified GHC.Tc.Solver.Monad as TM
import Data.String (IsString)

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      elem'TyCon <- lookupElem' checkedExceptMod
      elemTyCon <- lookupElem checkedExceptMod
      pure Environment {..}
  , TC.tcPluginSolve = solveBind
  , TC.tcPluginStop = const $ pure ()
  , TC.tcPluginRewrite = \_ -> emptyUFM
  }

lookupCheckedExceptMod :: TC.TcPluginM Module
lookupCheckedExceptMod = do
   findResult <- TC.findImportedModule ( mkModuleName "Control.Monad.CheckedExcept" ) NoPkgQual -- ( Just "checked-exceptions" )
   case findResult of
     TC.Found _ modCE -> pure modCE
     _ -> error "Couldn't find Control.Monad.CheckedExcept"

lookupContains :: Module -> TC.TcPluginM TyCon
lookupContains modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Contains"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

lookupElem' :: Module -> TC.TcPluginM TyCon
lookupElem' modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Elem'"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

lookupElem :: Module -> TC.TcPluginM TyCon
lookupElem modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Elem"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

data Environment = Environment
  { containsTyCon :: TyCon
  , elem'TyCon :: TyCon
  , elemTyCon :: TyCon
  }

solveBind :: Environment -> TC.TcPluginSolver
solveBind _ _ _ [] = pure $ TC.TcPluginOk [] []
solveBind env@Environment{..} _envBinds _givens wanteds = do
  (unzip3 <$> traverse solve1Wanted wanteds) >>= \case
    (eg, _unsolved, newWanteds) -> do
      pure $ TC.TcPluginOk (mconcat eg) (mconcat newWanteds) -- todo: TcPluginContradiction when shit hits the fan
  where
  solve1Wanted ::
       Ct
    -> TC.TcPluginM
          ( [(EvTerm, Ct)] -- solved
          , [Ct] -- unsolved
          , [Ct] -- new work
          )
  solve1Wanted unzonkedWanted = 
    TC.zonkCt unzonkedWanted >>= \wanted ->
      let mkNewWanted newPred = do
            mkNonCanonical <$> TC.newWanted (ctLoc wanted) newPred

          transformConstraint label ctev_pred ty1Unzonked ty2Unzonked mkNewPred = do
            tcTraceLabel ("ctev_pred_" <> label) ctev_pred
            ty1 <- TC.zonkTcType ty1Unzonked
            ty2 <- TC.zonkTcType ty2Unzonked
            let newPred = mkNewPred ty1 ty2
            if not (isTyVarTy ty1) && not (isTyVarTy ty2)
            then do
              tcTraceLabel ("ctev_pred_" <> label <> "_tys") (ty1,ty2)
              pure mempty
            else do
              newWanted <- mkNewWanted newPred
              tcTraceLabel (label <> "_newWanted") (newWanted)
              pure
                ( [ ( evByFiat "checked-exceptions" (ctPred newWanted) (ctPred wanted)
                     , wanted
                     )
                  ]
                , []
                , [newWanted]
                )
      in
      case wanted of
        CIrredCan (IrredCt {ir_ev = CtWanted{..}}) -> do
          if
            | Just (tc, [tk, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tc == containsTyCon -- Check if it's `Contains`
            -> transformConstraint "contains" ctev_pred ty1Unzonked ty2Unzonked (mkContainsConstraint env tk)

            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon -- Check if it's `If (Elem'`
            -> do transformConstraint "if_1" ctev_pred ty1Unzonked ty2Unzonked (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Constraint env tcKind ty1 ty2, ifTrue, ifFalse])

            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon -- Check if it's `If (Elem'`
            -> do transformConstraint "if_2" ctev_pred ty1Unzonked ty2Unzonked (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Constraint env boolTy ty1 ty2, ifTrue, ifFalse])

            | Just (tcElem, [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon -- Check if it's `Elem`
            -> do transformConstraint "elem_1" ctev_pred ty1Unzonked ty2Unzonked (mkElemConstraint env tcKind)

            | Just (tcElem, [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon -- Check if it's `Elem`
            -> do transformConstraint "elem_2" ctev_pred ty1Unzonked ty2Unzonked (mkElemConstraint env constraintKind)

            | otherwise -> do
                tcTraceLabel "unwanted2" (ctKind wanted, wanted)
                pure ([], [wanted], [])

        _ -> do
          tcTraceLabel "unwanted" (ctKind wanted, wanted)
          pure ([], [wanted], [])

-- | The 'EvTerm' equivalent for 'Unsafe.unsafeCoerce'
evByFiat :: String -- ^ Name the coercion should have
         -> Type   -- ^ The LHS of the equivalence relation (~)
         -> Type   -- ^ The RHS of the equivalence relation (~)
         -> EvTerm
evByFiat name t1 t2 =
  EvExpr $ Coercion $ mkUnivCo (PluginProv name) Nominal t1 t2

ctKind :: Ct -> FastString
ctKind = \case 
  CDictCan     {} -> "CDictCan     "
  CIrredCan    {} -> "CIrredCan    "
  CEqCan       {} -> "CEqCan       "
  CQuantCan    {} -> "CQuantCan    "
  CNonCanonical{} -> "CNonCanonical"

-- Create the new Contains constraint with '[], or the weaker of the two types substituted for unsolved type variables
mkContainsConstraint :: Environment -> Type -> Type -> Type -> PredType
mkContainsConstraint Environment{..} tk ty1 ty2 =
    mkFamilyTyConApp containsTyCon [tk, ty1Defaulted, ty2Defaulted]
  where
    weakest = getWeakest ty1 ty2
    (ty1Defaulted, ty2Defaulted) =
      ( if isTyVarTy ty1 then emptyListKindTy else ty1
      , weakest
      )

emptyListKindTy :: Type
emptyListKindTy = mkPromotedListTy tYPEKind []

-- Create the new Elem' constraint with '[ty1] substituted for unsolved type variables
mkElem'Constraint :: Environment -> Type -> Type -> Type -> PredType
mkElem'Constraint Environment{..} tk ty1 ty2 = mkFamilyTyConApp elem'TyCon [tk, ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then mkPromotedListTy tYPEKind [ty1] else x

mkElemConstraint :: Environment -> Type -> Type -> Type -> PredType
mkElemConstraint Environment{..} tk ty1 ty2 = mkFamilyTyConApp elemTyCon [tk, ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then mkPromotedListTy tYPEKind [ty1] else x

getWeakest :: Type -> Type -> Type
getWeakest ty1 ty2 =
  let ty1Tys = if isTyVarTy ty1
               then []
               else case extractMPromotedList ty1 of
                 Nothing -> []
                 Just tys -> tys
      ty2Tys = if isTyVarTy ty2
               then []
               else case extractMPromotedList ty2 of
                 Nothing -> []
                 Just tys -> tys
  in mkPromotedListTy tYPEKind $ nubBy ((==) `on` deBruijnize) (ty1Tys <> ty2Tys)

tcPrintLn :: String -> TC.TcPluginM ()
tcPrintLn = TC.tcPluginIO . putStrLn

tcPrint :: String -> TC.TcPluginM ()
tcPrint = TC.tcPluginIO . putStr

tcPrintOutputable :: Outputable a => a -> TC.TcPluginM ()
tcPrintOutputable = tcPrintLn . showSDocUnsafe . ppr

tcTraceLabel :: Outputable a => String -> a -> TC.TcPluginM ()
tcTraceLabel label x = tcPluginTrace ("[CHECKED_EXCEPTIONS] " <> label) (ppr x)

-- | Extract the elements of a promoted list. Panics if the type is not a
-- promoted list
extractMPromotedList :: Type    -- ^ The promoted list
                    -> Maybe [Type]
extractMPromotedList tys = go tys
  where
    go list_ty
      | Just (tc, [_k, t, ts]) <- splitTyConApp_maybe list_ty
      = assert (tc `hasKey` consDataConKey) $
        case go ts of
          Nothing -> Nothing
          Just ts' -> Just $ t : ts'

      | Just (tc, [_k]) <- splitTyConApp_maybe list_ty
      = assert (tc `hasKey` nilDataConKey)
        Just []

      | otherwise
      = Nothing
