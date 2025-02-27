{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedRecordDot #-}

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

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      elem'TyCon <- lookupElem' checkedExceptMod
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
  , elemTyCon :: TyCon
  , checkedExceptTTyCon :: TyCon
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

          noNewWork _ _ = False

          newWorkIfVar ty1 ty2 = isTyVarTy ty1 || isTyVarTy ty2

          transformConstraint label ir_ev ir_reason ty1Unzonked ty2Unzonked hasNewWork mkNewPred = do
            tcTraceLabel (label <> "_ir_ev") ir_ev
            tcTraceLabel (label <> "_ir_reason") ir_reason
            tcTraceLabel (label <> "_ctev_loc") (ctl_origin $ ctev_loc ir_ev)
            (ty1, ty2) <- disambiguateTypeVarsUsingReturnType env wanted ty1Unzonked ty2Unzonked
            let newPred = mkNewPred ty1 ty2
            if not (isTyVarTy ty1) && not (isTyVarTy ty2)
            then do
              tcTraceLabel ("ctev_pred_" <> label <> "_tys") (ty1,ty2)
              pure mempty
            else do
              newWanted <- mkNewWanted newPred
              tcTraceLabel (label <> "_newWanted") (newWanted)
              pure
                ( [ ( if hasNewWork ty1 ty2
                      then trustMeBro "checked-exceptions" (ctEvExpr $ ctEvidence wanted) (ctPred wanted) (ctPred newWanted)
                      else evByFiat "checked-exceptions" (ctPred wanted) newPred
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
            -> transformConstraint "contains" ir_ev ir_reason ty1Unzonked ty2Unzonked noNewWork (mkContainsPred env tk)

            -- Check if it's `If (Elem'`
            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_1" ir_ev ir_reason ty1Unzonked ty2Unzonked newWorkIfVar (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Type env tcKind ty1 ty2, ifTrue, ifFalse])

            -- Check if it's `If (Elem'`
            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_2" ir_ev ir_reason ty1Unzonked ty2Unzonked newWorkIfVar (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Type env boolTy ty1 ty2, ifTrue, ifFalse])

            -- Check if it's `Elem`
            | Just (tcElem, [tcKind, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon
            -> do transformConstraint "elem_1" ir_ev ir_reason ty1Unzonked ty2Unzonked newWorkIfVar (mkElemPred env tcKind)

            -- Check if it's `Elem`
            | Just (tcElem, [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
            , tcElem == elemTyCon
            -> do transformConstraint "elem_2" ir_ev ir_reason ty1Unzonked ty2Unzonked newWorkIfVar (mkElemPred env constraintKind)

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
    weakest = getWeakest ty1 ty2
    (ty1Defaulted, ty2Defaulted) =
      ( if isTyVarTy ty1 then emptyListKindTy else ty1
      , weakest
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

-- Function to disambiguate type variables using the return type of the function from which the wanted constraint arises
disambiguateTypeVarsUsingReturnType :: Environment -> Ct -> Type -> Type -> TC.TcPluginM (Type, Type)
disambiguateTypeVarsUsingReturnType Environment {..} wanted ty1 ty2 = do
  retType <- lookupReturnType (ctLocEnv (ctLoc wanted))
  tcTraceLabel "retType" retType
  esType <-
    if
      | Just (tc, [esType, _, _]) <-  splitTyConApp_maybe retType
      , tc == checkedExceptTTyCon
      -> pure esType
      | otherwise -> fail "impossibru"
  tcTraceLabel "esType" esType
  ty1' <- TC.zonkTcType ty1
  ty2' <- TC.zonkTcType ty2
  let disambiguatedTy1 = if isTyVarTy ty1' then esType else ty1'
      disambiguatedTy2 = if isTyVarTy ty2' then esType else ty2'
  pure (disambiguatedTy1, disambiguatedTy2)

-- Function to lookup the return type from the environment
lookupReturnType :: CtLocEnv -> TC.TcPluginM Type
lookupReturnType env = case ctl_bndrs env of
  [t] -> case t of
    TC.TcIdBndr tcid _ -> pure $ idType tcid
    _ -> fail "Unresolved return type"
  [] -> fail "No return type found in environment"
  _ -> fail "Ambiguous return type"
