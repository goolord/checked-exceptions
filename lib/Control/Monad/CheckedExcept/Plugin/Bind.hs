{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Control.Monad.CheckedExcept.Plugin.Bind
  ( bindPlugin
  -- disable unused warnings
  , tcPrintLn
  , tcPrint
  , tcPrintOutputable
  , tcTraceLabel
  , evByFiat
  )
where

import GHC.Plugins hiding ((<>))
import GHC.Tc.Types.Constraint
import qualified GHC.Tc.Plugin as TC
import qualified GHC.Tc.Types as TC
import GHC.Tc.Types.Evidence (EvTerm (..), evCast)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Tc.Plugin (tcPluginTrace)
import Data.List (nubBy)
import GHC.Core.Map.Type (deBruijnize)
import Data.Function (on)
import GHC.Types.Unique (hasKey)
import GHC.Builtin.Names (consDataConKey)
import GHC.Core.Predicate (Pred(..), classifyPredType)
import Data.Maybe (mapMaybe)
import Data.Bifunctor (second)

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      (elem'TyCon, elem'Name) <- lookupElem' checkedExceptMod
      elemTyCon <- lookupElem checkedExceptMod
      checkedExceptTTyCon <- lookupCheckedExceptT checkedExceptMod
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

lookupElem' :: Module -> TC.TcPluginM (TyCon, Name)
lookupElem' modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Elem'"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  (, myTyFam_Name) <$> TC.tcLookupTyCon myTyFam_Name

lookupElem :: Module -> TC.TcPluginM TyCon
lookupElem modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Elem"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

lookupCheckedExceptT :: Module -> TC.TcPluginM TyCon
lookupCheckedExceptT modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "CheckedExceptT"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

data Environment = Environment
  { containsTyCon :: TyCon
  , elem'TyCon :: TyCon
  , elem'Name :: Name
  , elemTyCon :: TyCon
  , checkedExceptTTyCon :: TyCon
  }

concatUnzip3 :: [([a],[b],[c])] -> ([a],[b],[c])
concatUnzip3 xs = (concat a, concat b, concat c)
    where (a,b,c) = unzip3 xs

solveBind :: Environment -> TC.TcPluginSolver
solveBind _ _ _ [] = pure $ TC.TcPluginOk [] []
solveBind env@Environment{..} _envBinds _givens wanteds = do
  (solved, insoluable, newCt) <- concatUnzip3 <$> traverse solve1Wanted wanteds
  tcTraceLabel "insoluable" insoluable
  pure TC.TcPluginSolveResult
    { tcPluginInsolubleCts = insoluable
    , tcPluginSolvedCts = solved
    , tcPluginNewCts = newCt
    }
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
      let noNewWork _ _ = False
          yesNewWork _ _ = True

          newWorkIfVar ty1 ty2 = not (isUnified ty1 && isUnified ty2)

          defWork = yesNewWork

          transformConstraint label ir_ev ir_reason ty1Unzonked ty2Unzonked hasNewWork mkNewPred = do
            tcTraceLabel (label <> "_ir_ev") ir_ev
            tcTraceLabel (label <> "_ir_reason") ir_reason
            mtys <- disambiguateTypeVarsUsingReturnType env wanted ty1Unzonked ty2Unzonked
            let mkNewWanted ty1 ty2 newPred = do
                  if hasNewWork ty1 ty2
                  then mkNonCanonical <$> TC.newWanted (ctLoc wanted) newPred
                  else pure $ mkNonCanonical (setCtEvPredType ir_ev $ newPred)
            case mtys of
              Nothing -> do
                let newWanted = mkNonCanonical (ctEvidence wanted)
                pure
                  ( [ ( trustMeBro "checked-exceptions" (ctEvExpr $ ctEvidence newWanted) (ctPred newWanted) (ctPred wanted)
                      , wanted
                      )
                    ]
                  , []
                  , []
                  )
              Just (ty1, ty2) -> do
                let newPred = mkNewPred ty1 ty2
                newWanted <- mkNewWanted ty1 ty2 $ substituteTypeVar ty2Unzonked ty2 newPred
                tcTraceLabel (label <> "_wanted") (wanted, newWanted, newPred)
                tcTraceLabel (label <> "_newWanted") newWanted
                pure
                  ( [ ( trustMeBro "checked-exceptions" (ctEvExpr $ ctEvidence newWanted) (ctPred newWanted) (ctPred wanted)
                       , wanted
                       )
                    ]
                  , []
                  , if hasNewWork ty1 ty2 then [newWanted] else []
                  )
      in
      case wanted of
        CIrredCan (IrredCt {ir_ev = ir_ev@CtWanted{..}, ir_reason}) -> do
          if
            -- Check if it's `Contains`
            | Just (tc, [tk, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tc == containsTyCon
            -> transformConstraint "contains" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (mkContainsPred env tk)

            -- Check if it's `If (Elem'`
            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_1" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> mkFamilyTyConApp tcIf [ifKind, mkElem'Type env tcKind ty1 ty2, ifTrue, ifFalse])

            -- Check if it's `If (Elem'`
            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_2" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> mkFamilyTyConApp tcIf [ifKind, mkElem'Type env boolTy ty1 ty2, ifTrue, ifFalse])

            -- Check if it's `Elem`
            | Just (tcElem, [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon
            -> do transformConstraint "elem_1" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (mkElemPred env tcKind)

            -- Check if it's `Elem`
            | Just (tcElem, [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon
            -> do transformConstraint "elem_2" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (mkElemPred env constraintKind)

            | otherwise -> do
                tcTraceLabel "unwanted2" (ctKind wanted, wanted)
                pure ([], [wanted], [])
        CNonCanonical ev -> do
          -- Ask GHC to attempt to solve the CNonCanonical wanted
          let predType = ctEvPred ev
          case classifyPredType predType of
            ClassPred{} -> do
              tcTraceLabel "noncanon" (fsLit "ClassPred")
              pure mempty
            EqPred _ ty1 ty2 -> do
              tcTraceLabel "noncanon" (fsLit "EqPred", splitTyConApp_maybe ty1, predType)
              if
                | Just (tcElem, [_, tcElemTy1, tcElemTy2]) <- splitTyConApp_maybe ty1
                , tcElem == elem'TyCon
                , Just tcElemTy2List <- extractMPromotedList tcElemTy2 -> do
                  if deBruijnize tcElemTy1 `elem` fmap deBruijnize tcElemTy2List
                  then
                    pure
                      ( [(evByFiat "checked-exceptions" ty1 ty2, wanted)]
                      , []
                      , []
                      )
                  else do -- TODO: this clobbers the custom error message
                    pure
                      ( []
                      , []
                      , []
                      )
                | otherwise -> pure mempty
            IrredPred{} -> do
              tcTraceLabel "noncanon" (fsLit "IrredPred")
              pure mempty
            ForAllPred{} -> do
              tcTraceLabel "noncanon" (fsLit "ForAllPred")
              pure mempty
        _ -> do
          tcTraceLabel "unwanted" (ctKind wanted, wanted)
          pure ([], [wanted], [])

-- elem'ToElem :: Environment -> Type -> Type
-- elem'ToElem Environment{..} ty = if
--   | Just (tcElem, tys) <- splitTyConApp_maybe ty
--   , tcElem == elem'TyCon
--   , Just tyErr <- deepUserTypeError_maybe (mkTyConApp elemTyCon tys)
--   -> tyErr
--   | otherwise -> ty

-- Function to substitute type variable in ifFalse
substituteTypeVar :: Type -> Type -> Type -> Type
substituteTypeVar ty2Unzonked ty2 ifFalse =
  case getTyVar_maybe ty2Unzonked of
    Nothing -> ifFalse
    Just ty2UnzonkedVar -> substTyWith [ty2UnzonkedVar] [ty2] ifFalse

-- | The 'EvTerm' equivalent for 'Unsafe.unsafeCoerce'
evByFiat :: String -- ^ Name the coercion should have
         -> Type   -- ^ The LHS of the equivalence relation (~)
         -> Type   -- ^ The RHS of the equivalence relation (~)
         -> EvTerm
evByFiat name t1 t2 =
  EvExpr $ Coercion $ mkUnivCo (PluginProv name) Nominal t1 t2

trustMeBro :: String -- ^ Name the coercion should have
         -> Expr CoreBndr
         -> Type   -- ^ The LHS of the equivalence relation (~)
         -> Type   -- ^ The RHS of the equivalence relation (~)
         -> EvTerm
trustMeBro name expr t1 t2 =
  evCast expr $ mkUnivCo (PluginProv name) Nominal t1 t2

ctKind :: Ct -> FastString
ctKind = \case
  CDictCan     {} -> "CDictCan     "
  CIrredCan    {} -> "CIrredCan    "
  CEqCan       {} -> "CEqCan       "
  CQuantCan    {} -> "CQuantCan    "
  CNonCanonical{} -> "CNonCanonical"

-- Create the new Contains constraint with '[], or the weaker of the two types substituted for unsolved type variables
mkContainsPred :: Environment -> Type -> Type -> Type -> PredType
mkContainsPred Environment{..} tk ty1 ty2 =
    mkFamilyTyConApp containsTyCon [tk, ty1Defaulted, ty2Defaulted]
  where
    (ty1Defaulted, ty2Defaulted) =
      ( if isTyVarTy ty1 then emptyListKindTy else ty1
      , ty2
      )

-- Create the new Elem' constraint with '[ty1] substituted for unsolved type variables
mkElem'Type :: Environment -> Type -> Type -> Type -> Type
mkElem'Type Environment{..} tk ty1 ty2 = mkFamilyTyConApp elem'TyCon [tk, ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then mkPromotedListTy tYPEKind [] else x

mkElemPred :: Environment -> Type -> Type -> Type -> PredType
mkElemPred Environment{..} tk ty1 ty2 = mkFamilyTyConApp elemTyCon [tk, ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then mkPromotedListTy tYPEKind [] else x

emptyListKindTy :: Type
emptyListKindTy = mkPromotedListTy tYPEKind []

uniquePromotedList :: [Type] -> Type
uniquePromotedList tys = mkPromotedListTy tYPEKind $ nubBy ((==) `on` deBruijnize) tys

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

-- Function to disambiguate type variables using the return type of the function from which the wanted constraint arises
disambiguateTypeVarsUsingReturnType :: Environment -> Ct -> Type -> Type -> TC.TcPluginM (Maybe (Type, Type))
disambiguateTypeVarsUsingReturnType Environment {..} wanted ty1 ty2 = do
  retType <- lookupReturnType (ctLocEnv (ctLoc wanted))
  tcTraceLabel "retType" retType
  esType <- do
      let retTyArgs = getRuntimeArgTysOrTy retType
          ts = mapMaybe (\(st,_) -> do
                (tc, ts1) <- splitTyConApp_maybe $ irrelevantMult st
                if tc == checkedExceptTTyCon
                then do
                  esType <- case ts1 of
                    [esType, _, _] -> Just esType
                    [_, esType, _, _] -> Just esType
                    _ -> Nothing
                  extractMPromotedList esType
                else Nothing
            ) retTyArgs
      if not (null ts)
      then uniquePromotedList <$> traverse TC.zonkTcType (mconcat ts)
      else do
        tcTraceLabel "retTyArgs" retTyArgs
        failWithTrace "impossibru"
  tcTraceLabel "esType" esType
  if isUnified ty1 && isUnified ty2
  then pure Nothing
  else do
    zonkedTy1 <- TC.zonkTcType ty1
    zonkedTy2 <- TC.zonkTcType ty2
    let disambiguatedTy1 = if isUnified zonkedTy1 then zonkedTy1 else esType
        disambiguatedTy2 = if isUnified zonkedTy2 then zonkedTy2 else esType
    tcTraceLabel "ambiguous    " (ty1, ty2)
    tcTraceLabel "disambiguated" (disambiguatedTy1, disambiguatedTy2)
    pure $ Just (disambiguatedTy1, disambiguatedTy2)

isUnified :: Type -> Bool
isUnified ty =
     isTauTy ty
  && isConcreteType ty
  && (not $ isTyVarTy ty)

-- Function to lookup the return type from the environment
lookupReturnType :: CtLocEnv -> TC.TcPluginM (Type, Arity)
lookupReturnType env = case ctl_bndrs env of
  ts@(TC.TcIdBndr tcid _:_) -> do
      tcTraceLabel "lookupReturnType" ts
      pure $ (idType tcid, idArity tcid)
  [] -> failWithTrace "No return type found in environment"
  _ -> failWithTrace "Unresolved return type"

failWithTrace :: forall x. String -> TC.TcPluginM x
failWithTrace s = do
  tcTraceLabel "fail" (mkFastString s)
  fail s

getRuntimeArgTysOrTy :: (Type, Arity) -> [(Scaled Type, Maybe FunTyFlag)]
getRuntimeArgTysOrTy (ty, arity) = case arity of
  0 -> [(unrestricted ty, Nothing)]
  _ -> fmap (second Just) (getRuntimeArgTys ty)
