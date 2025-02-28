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
import GHC.Types.Unique (hasKey)
import GHC.Builtin.Names (consDataConKey)
import Data.Maybe (mapMaybe)
import Data.Bifunctor (second)
import GHC.Core.Reduction (Reduction(..))
import GHC.Tc.Utils.TcType (eqType)

{-
    ************************************************************
    *                                                          *
    *                  Plugin initialization                   *
    *                                                          *
    ************************************************************
-}

data Environment = Environment
  { containsTyCon :: TyCon
  , elem'TyCon :: TyCon
  , elemTyCon :: TyCon
  , checkedExceptTTyCon :: TyCon
  , notElemTypeErrorTyCon :: TyCon
  }

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      elem'TyCon <- lookupElem' checkedExceptMod
      elemTyCon <- lookupElem checkedExceptMod
      checkedExceptTTyCon <- lookupCheckedExceptT checkedExceptMod
      notElemTypeErrorTyCon <- lookupNotElemTypeError checkedExceptMod
      pure Environment {..}
  , TC.tcPluginSolve = solveBind
  , TC.tcPluginStop = const $ pure ()
  , TC.tcPluginRewrite = mkRewriter
  }

lookupTyConWithMod :: String -> Module -> TC.TcPluginM TyCon
lookupTyConWithMod name modCE = do
  let tyCo_OccName = mkTcOcc name
  tyCo <- TC.lookupOrig modCE tyCo_OccName
  TC.tcLookupTyCon tyCo

lookupCheckedExceptMod :: TC.TcPluginM Module
lookupCheckedExceptMod = do
   findResult <- TC.findImportedModule ( mkModuleName "Control.Monad.CheckedExcept" ) NoPkgQual -- ( Just "checked-exceptions" )
   case findResult of
     TC.Found _ modCE -> pure modCE
     _ -> error "Couldn't find Control.Monad.CheckedExcept"

lookupContains :: Module -> TC.TcPluginM TyCon
lookupContains = lookupTyConWithMod "Contains"

lookupElem' :: Module -> TC.TcPluginM TyCon
lookupElem' = lookupTyConWithMod "Elem'"

lookupElem :: Module -> TC.TcPluginM TyCon
lookupElem = lookupTyConWithMod "Elem"

lookupCheckedExceptT :: Module -> TC.TcPluginM TyCon
lookupCheckedExceptT modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "CheckedExceptT"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

lookupNotElemTypeError :: Module -> TC.TcPluginM TyCon
lookupNotElemTypeError = lookupTyConWithMod "NotElemTypeError"

{-
    ************************************************************
    *                                                          *
    *     Control.Monad.CheckedExcept constraint solver        *
    *                                                          *
    ************************************************************
-}

solveBind :: Environment -> TC.TcPluginSolver
solveBind _ _ _ [] = pure $ TC.TcPluginOk [] []
solveBind env@Environment{..} _evBinds _givens wanteds = do
  (solved, insoluable, newCt) <- concatUnzip3 <$> traverse solve1Wanted wanteds
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

          -- not quite right, since we do substitutions...
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
                pure mempty -- catch this in the rewriter
              Just (ty1, ty2) -> do
                let newPred = substituteTypeVars [(ty1Unzonked, ty1), (ty2Unzonked, ty2)] $ mkNewPred ty1 ty2
                newWanted <- mkNewWanted ty1 ty2 newPred
                pure
                  ( [ ( trustMeBro ("checked-exceptions:" <> label <> ":ambiguous") (ctEvExpr $ ctEvidence newWanted) (ctPred newWanted) (ctPred wanted)
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
            | Just (tc, [tk], [ty1Unzonked, ty2Unzonked]) <- splitTyConAppIgnoringKind ctev_pred
            , tc == containsTyCon
            -> transformConstraint "contains" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> substContains env tk ty1 ty2 ctev_pred)

            -- Check if it's `If (Elem'`
            | Just (tcIf, _, [elemTf, _, _]) <- splitTyConAppIgnoringKind ctev_pred
            , getOccName tcIf == mkTcOcc "If"
            , Just (tcElem', _, [ty1Unzonked, ty2Unzonked]) <- splitTyConAppIgnoringKind elemTf
            , tcElem' == elem'TyCon
            -> do transformConstraint "if_1" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> substElem' env ty1 ty2 ctev_pred)

            -- Check if it's `Elem`
            | Just (tcElem, _, [ty1Unzonked, ty2Unzonked]) <- splitTyConAppIgnoringKind ctev_pred
            , tcElem == elemTyCon
            -> do transformConstraint "elem_2" ir_ev ir_reason ty1Unzonked ty2Unzonked defWork (\ty1 ty2 -> substElem env ty1 ty2 ctev_pred)

            | otherwise -> do
                tcTraceLabel "unwanted2" (ctKind wanted, wanted)
                pure ([], [wanted], [])

        _ -> do
          tcTraceLabel "unwanted" (ctKind wanted, wanted)
          pure ([], [wanted], [])

substContains :: Environment -> Type -> Type -> Type -> PredType -> PredType
substContains _env _tk ty1 _ty2 predTy =
  case getTyVar_maybe ty1 of
    Nothing -> predTy
    Just ty1Var -> substTyWith [ty1Var] [emptyListKindTy] predTy

substElem' :: Environment -> Type -> Type -> PredType -> PredType
substElem' _env _ty1 ty2 predTy =
  case getTyVar_maybe ty2 of
    Nothing -> predTy
    Just ty2Var -> substTyWith [ty2Var] [emptyListKindTy] predTy

substElem :: Environment -> Type -> Type -> PredType -> PredType
substElem _env _ty1 ty2 predTy =
  case getTyVar_maybe ty2 of
    Nothing -> predTy
    Just ty2Var -> substTyWith [ty2Var] [emptyListKindTy] predTy

-- Function to disambiguate type variables using the return type of the function from which the wanted constraint arises
disambiguateTypeVarsUsingReturnType :: Environment -> Ct -> Type -> Type -> TC.TcPluginM (Maybe (Type, Type))
disambiguateTypeVarsUsingReturnType Environment {..} wanted ty1 ty2 = do
  retType <- lookupReturnType (ctLocEnv (ctLoc wanted))
  tcTraceLabel "retType" retType
  esType <- do
      let retTyArgs = getRuntimeArgTysOrTy retType
          ts = mapMaybe (\(st,_) -> do
                (tc, _, ts1) <- splitTyConAppIgnoringKind $ irrelevantMult st
                if tc == checkedExceptTTyCon
                then do
                  esType <- case ts1 of
                    [esType, _, _] -> Just esType
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

-- Function to lookup the return type from the environment
lookupReturnType :: CtLocEnv -> TC.TcPluginM (Type, Arity)
lookupReturnType env = case ctl_bndrs env of
  ts@(TC.TcIdBndr tcid _:_) -> do
      tcTraceLabel "lookupReturnType" ts
      pure $ (idType tcid, idArity tcid)
  [] -> failWithTrace "No return type found in environment"
  _ -> failWithTrace "Unresolved return type"

{-
    ************************************************************
    *                                                          *
    *     Control.Monad.CheckedExcept type family rewriter     *
    *                                                          *
    ************************************************************
-}

mkRewriter :: Environment -> UniqFM TyCon TC.TcPluginRewriter
mkRewriter env@Environment{..} = listToUFM 
  [ (elem'TyCon, rewriteElem' env)
  , (elemTyCon, rewriteElem env)
  , (containsTyCon, rewriteContains env)
  ]

rewriteElem' :: Environment -> TC.TcPluginRewriter
rewriteElem' env@Environment{..} = rewriteBothElem trueCase falseCase env
  where
  trueCase = mkTyConApp promotedTrueDataCon []
  falseCase _ ty1 ty2 = mkTyConApp notElemTypeErrorTyCon [ty1, ty2]

rewriteElem :: Environment -> TC.TcPluginRewriter
rewriteElem env@Environment{..} = rewriteBothElem trueCase falseCase env
  where
  trueCase = mkConstraintTupleTy []
  falseCase _tk ty1 ty2 = mkTyConApp notElemTypeErrorTyCon [ty1, ty2]

rewriteBothElem :: Applicative f => Type -> (Type -> Type -> Type -> Type) -> Environment -> p1 -> p2 -> [Type] -> f TC.TcPluginRewriteResult
rewriteBothElem trueCase falseCase Environment{..} _rewriteEnv _givens [tk, ty, tys] =
  case extractMPromotedList tys of
    Nothing -> pure TC.TcPluginNoRewrite
    Just tyList -> do
      let result = if any (eqType ty) tyList
                   then trueCase
                   else falseCase tk ty tys
      let coercion = mkUnivCo (PluginProv "checked-exceptions") Nominal (mkTyConApp elem'TyCon [ty, tys]) result
      pure $ TC.TcPluginRewriteTo (Reduction coercion result) []
rewriteBothElem _ _ _ _ _ _ = pure TC.TcPluginNoRewrite

rewriteContains :: Environment -> TC.TcPluginRewriter
rewriteContains Environment{..} _rewriteEnv _givens [tk, tys1, tys2] = do
  case extractMPromotedList tys1 of
    Just tyList1 -> do
      let mkElemConstraint x = mkTyConApp elemTyCon [tk, x, tys2]
          result = mkConstraintTupleTy $ fmap mkElemConstraint tyList1
      let coercion = mkUnivCo (PluginProv "checked-exceptions") Nominal (mkTyConApp elem'TyCon [tys1, tys2]) result
      pure $ TC.TcPluginRewriteTo (Reduction coercion result) []
    _ -> pure TC.TcPluginNoRewrite
rewriteContains _ _ _ _ = do
  pure TC.TcPluginNoRewrite

{-
    ************************************************************
    *                                                          *
    *                    Utility functions                     *
    *                                                          *
    ************************************************************
-}

concatUnzip3 :: [([a],[b],[c])] -> ([a],[b],[c])
concatUnzip3 xs = (concat a, concat b, concat c)
    where (a,b,c) = unzip3 xs

failWithTrace :: forall x. String -> TC.TcPluginM x
failWithTrace s = do
  tcTraceLabel "fail" (mkFastString s)
  fail s

tcPrintLn :: String -> TC.TcPluginM ()
tcPrintLn = TC.tcPluginIO . putStrLn

tcPrint :: String -> TC.TcPluginM ()
tcPrint = TC.tcPluginIO . putStr

tcPrintOutputable :: Outputable a => a -> TC.TcPluginM ()
tcPrintOutputable = tcPrintLn . showSDocUnsafe . ppr

tcTraceLabel :: Outputable a => String -> a -> TC.TcPluginM ()
tcTraceLabel label x = tcPluginTrace ("[checked-exceptions] " <> label) (ppr x)

isUnified :: Type -> Bool
isUnified ty =
     isTauTy ty
  && isConcreteType ty
  && (not $ isTyVarTy ty)

emptyListKindTy :: Type
emptyListKindTy = mkPromotedListTy tYPEKind []

uniquePromotedList :: [Type] -> Type
uniquePromotedList tys = mkPromotedListTy tYPEKind $ nubBy eqType tys

-- | Extract the elements of a promoted list, returns Nothing if not a promoted list
extractMPromotedList :: Type -> Maybe [Type]
extractMPromotedList tys = go tys
  where
    go list_ty
      | Just (tc, _, [t, ts]) <- splitTyConAppIgnoringKind list_ty
      = assert (tc `hasKey` consDataConKey) $
        case go ts of
          Nothing -> Nothing
          Just ts' -> Just $ t : ts'

      | Just (tc, _, []) <- splitTyConAppIgnoringKind list_ty
      = assert (tc `hasKey` nilDataConKey)
        Just []

      | otherwise
      = Nothing

ctKind :: Ct -> FastString
ctKind = \case
  CDictCan     {} -> "CDictCan     "
  CIrredCan    {} -> "CIrredCan    "
  CEqCan       {} -> "CEqCan       "
  CQuantCan    {} -> "CQuantCan    "
  CNonCanonical{} -> "CNonCanonical"

-- | The 'EvTerm' equivalent for 'Unsafe.unsafeCoerce'
evByFiat :: String -- ^ Name the coercion should have
         -> Type   -- ^ The LHS of the equivalence relation (~)
         -> Type   -- ^ The RHS of the equivalence relation (~)
         -> EvTerm
evByFiat name t1 t2 = EvExpr $ Coercion $ mkUnivCo (PluginProv name) Nominal t1 t2

-- a *slightly* more safe version of evByFiat that will succeed even when
-- the new wanted's core expr is not emitted
trustMeBro :: String -- ^ Name the coercion should have
         -> Expr CoreBndr
         -> Type   -- ^ The LHS of the equivalence relation (~)
         -> Type   -- ^ The RHS of the equivalence relation (~)
         -> EvTerm
trustMeBro name expr t1 t2 = evCast expr $ mkUnivCo (PluginProv name) Nominal t1 t2

-- accepts a map of types to substitute if they are type variables
-- and performs those substitutions on the tyUnsubbed argument
substituteTypeVars :: [(Type,Type)] -> Type -> Type
substituteTypeVars tyMap tyUnsubbed =
  let (tyVars,concTys) =
        unzip $ mapMaybe
          (\(tyVarTy,tyRepl) -> do
              tyVar <- getTyVar_maybe tyVarTy
              pure (tyVar, tyRepl)
          )
          tyMap
  in substTyWith tyVars concTys tyUnsubbed

splitTyConAppIgnoringKind :: Type -> Maybe (TyCon, [Type], [Type])
splitTyConAppIgnoringKind ty = do
  (tyCon, tys) <- splitTyConApp_maybe ty
  let (invisTys, visTys) = partitionInvisibleTypes tyCon tys
  pure (tyCon, invisTys, visTys)

-- getRunTimeArgTys can decompose certain types of arity 0 (like newtypes)
-- so we have to check the arity ourselves
getRuntimeArgTysOrTy :: (Type, Arity) -> [(Scaled Type, Maybe FunTyFlag)]
getRuntimeArgTysOrTy (ty, arity) = case arity of
  0 -> [(unrestricted ty, Nothing)]
  _ -> fmap (second Just) (getRuntimeArgTys ty)
