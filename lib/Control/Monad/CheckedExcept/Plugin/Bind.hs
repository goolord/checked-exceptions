{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}

module Control.Monad.CheckedExcept.Plugin.Bind 
  ( bindPlugin
  )
where

import GHC.Plugins hiding ((<>))
import GHC.Tc.Types.Constraint
import qualified GHC.Tc.Plugin as TC
import qualified GHC.Tc.Types as TC
import GHC.Tc.Types.Evidence (EvTerm (..), evCast)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Tc.Plugin (tcPluginTrace)

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      pure Environment {..}
  , TC.tcPluginSolve = solveBind
  , TC.tcPluginStop = const $ pure ()
  , TC.tcPluginRewrite = mempty
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

data Environment = Environment
  { containsTyCon :: TyCon
  }

solveBind :: Environment -> TC.TcPluginSolver
solveBind _ _ _ [] = pure $ TC.TcPluginOk [] []
solveBind env@Environment{..} _envBinds _givens wanteds = do
  (unzip3 <$> traverse solve1Wanted wanteds) >>= \case
    (eg,  w, newWork) -> do
      tcTraceLabel "eg: " (mconcat eg)
      tcTraceLabel "newWork: " (mconcat newWork)
      pure $ TC.TcPluginOk (mconcat eg) (mconcat w <> mconcat newWork) -- todo: TcPluginContradiction when shit hits the fan
  where
  solve1Wanted ::
       Ct 
    -> TC.TcPluginM 
          ( [(EvTerm, Ct)] -- solved
          , [Ct] -- unsolved
          , [Ct] -- new work
          )
  solve1Wanted unzonkedWanted = TC.zonkCt unzonkedWanted >>= \wanted -> case wanted of
    CIrredCan (IrredCt {ir_ev = ir_ev@CtWanted{..}}) -> do
      if
        | Just (tc, [_, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe ctev_pred
        , tc == containsTyCon -- Check if it's `Contains`
        -> do
          ty1 <- TC.zonkTcType ty1Unzonked
          ty2 <- TC.zonkTcType ty2Unzonked
          let newWanted = mkNonCanonical (setCtEvPredType ir_ev $ mkContainsConstraint env ty1 ty2)
          pure
            ( [ (  evCast (ctEvExpr $ ctEvidence newWanted) $ 
                   mkUnivCo (PluginProv "checked-exceptions") Phantom (ctPred newWanted) (ctPred wanted)
                 , wanted
                 )
              ]
            , []
            , [newWanted]
            )
        | otherwise -> pure ([], [wanted], [])
    _ -> do
      tcTraceLabel "unsolved: " wanted
      pure ([], [wanted], [])


emptyListKindTy :: Type
emptyListKindTy = mkPromotedListTy tYPEKind []

-- Create the new Contains constraint with '[] substituted for unsolved type variables
mkContainsConstraint :: Environment -> Type -> Type -> PredType
mkContainsConstraint Environment{..} ty1 ty2 = mkTyConApp containsTyCon [tYPEKind, defaultTypeVar ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then emptyListKindTy else x

tcPrintLn :: String -> TC.TcPluginM ()
tcPrintLn = TC.tcPluginIO . putStrLn

tcPrint :: String -> TC.TcPluginM ()
tcPrint = TC.tcPluginIO . putStr

tcPrintOutputable :: Outputable a => a -> TC.TcPluginM ()
tcPrintOutputable = tcPrintLn . showSDocUnsafe . ppr

tcTraceLabel :: Outputable a => String -> a -> TC.TcPluginM ()
tcTraceLabel label x = tcPluginTrace ("[CHECKED_EXCEPTIONS] " <> label) (ppr x)
