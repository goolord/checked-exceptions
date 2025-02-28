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
  fam <- TC.getFamInstEnvs
  tcTraceLabel "fam" fam
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
      let noNewWork _ _ = False
          yesNewWork _ _ = True

          newWorkIfVar ty1 ty2 = not (isUnified ty1) || not (isUnified ty2)

          defWork = yesNewWork

          transformConstraint label ir_ev ir_reason ty1Unzonked ty2Unzonked hasNewWork mkNewPred = do
            tcTraceLabel (label <> "_ir_ev") ir_ev
            tcTraceLabel (label <> "_ir_reason") ir_reason
            mtys <- disambiguateTypeVarsUsingReturnType env wanted ty1Unzonked ty2Unzonked
            case mtys of
              Nothing -> do
                tcTraceLabel "unambiguous" (ty1Unzonked, ty2Unzonked)
                pure mempty
              Just (ty1, ty2) -> do
                let mkNewWanted newPred = do
                      if hasNewWork ty1 ty2
                      then mkNonCanonical <$> TC.newWanted (ctLoc wanted) newPred
                      else pure $ mkNonCanonical (setCtEvPredType ir_ev $ newPred)
                newWanted <- mkNewWanted $ mkNewPred ty1 ty2
                tcTraceLabel (label <> "_newWanted") (newWanted)
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
            -> do transformConstraint "if_1" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Type env tcKind ty1 ty2, ifTrue, ifFalse])

            -- Check if it's `If (Elem'`
            | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', [ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_2" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> mkTyConApp tcIf [ifKind, mkElem'Type env boolTy ty1 ty2, ifTrue, ifFalse])

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
          tcTraceLabel "noncanon" predType
          case classifyPredType predType of
            ClassPred{} -> do
              tcTraceLabel "noncanon" (fsLit "ClassPred")
              pure mempty
            EqPred _ ty1Unzonked ty2Unzonked -> do
              (ty1, ty2) <- (,) <$> TC.zonkTcType ty1Unzonked <*> TC.zonkTcType ty2Unzonked
              tcTraceLabel "noncanon" (fsLit "EqPred", ty1, ty2)
              pure 
                ( [ (evByFiat "checked-exceptions" ty2 ty1,wanted) ]
                , []
                , []
                )
            IrredPred{} -> do
              tcTraceLabel "noncanon" (fsLit "IrredPred")
              pure mempty
            ForAllPred{} -> do
              tcTraceLabel "noncanon" (fsLit "ForAllPred")
              pure mempty
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
disambiguateTypeVarsUsingReturnType :: Environment -> Ct -> Type -> Type -> TC.TcPluginM (Maybe (Type, Type))
disambiguateTypeVarsUsingReturnType Environment {..} wanted ty1 ty2 = do
  retType <- lookupReturnType (ctLocEnv (ctLoc wanted))
  tcTraceLabel "retType" retType
  esType <-
    if
      | Just (tc, [esType, _, _]) <-  splitTyConApp_maybe retType
      , tc == checkedExceptTTyCon
      -> pure esType
      | otherwise -> failWithTrace "impossibru"
  tcTraceLabel "esType" esType
  if isUnified ty1 && isUnified ty2
  then pure Nothing
  else do
    zonkedTy1 <- TC.zonkTcType ty1
    zonkedTy2 <- TC.zonkTcType ty2
    let disambiguatedTy1 = if isTyVarTy zonkedTy1 then esType else zonkedTy1
        disambiguatedTy2 = if isTyVarTy zonkedTy2 then esType else zonkedTy2
    pure $ Just (disambiguatedTy1, disambiguatedTy2)

isUnified :: Type -> Bool
isUnified ty =
     isTauTy ty
  && isConcreteType ty

-- Function to lookup the return type from the environment
lookupReturnType :: CtLocEnv -> TC.TcPluginM Type
lookupReturnType env = case ctl_bndrs env of
  [t] -> case t of
    TC.TcIdBndr tcid _ -> pure $ idType tcid
    _ -> failWithTrace "Unresolved return type"
  [] -> failWithTrace "No return type found in environment"
  _ -> failWithTrace "Ambiguous return type"

failWithTrace :: forall x. String -> TC.TcPluginM x
failWithTrace s = do
  tcTraceLabel "fail" (mkFastString s)
  fail s
