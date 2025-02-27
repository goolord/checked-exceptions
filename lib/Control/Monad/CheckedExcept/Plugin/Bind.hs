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

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = do
      checkedExceptMod <- lookupCheckedExceptMod
      containsTyCon <- lookupContains checkedExceptMod
      elemTyCon <- lookupElem checkedExceptMod
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

lookupDataTypeBoolMod :: TC.TcPluginM Module
lookupDataTypeBoolMod = do
   findResult <- TC.findImportedModule ( mkModuleName "GHC.Internal.Data.Type.Bool" ) NoPkgQual
   case findResult of
     TC.Found _ modCE -> pure modCE
     _ -> error "Couldn't find Data.Type.Bool"


lookupContains :: Module -> TC.TcPluginM TyCon
lookupContains modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Contains"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

lookupElem :: Module -> TC.TcPluginM TyCon
lookupElem modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "Elem'"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

data Environment = Environment
  { containsTyCon :: TyCon
  , elemTyCon :: TyCon
  }

solveBind :: Environment -> TC.TcPluginSolver
solveBind _ _ _ [] = pure $ TC.TcPluginOk [] []
solveBind env@Environment{..} envBinds _givens wanteds = do
  (unzip3 <$> traverse solve1Wanted wanteds) >>= \case
    (eg,  w, newWork) -> do
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
        | Just (tcIf, [ifKind, elemTf, ifTrue, ifFalse]) <- splitTyConApp_maybe ctev_pred
        , getOccName tcIf == mkTcOcc "If"
        , Just (tcElem, [_, ty1Unzonked, ty2Unzonked]) <- splitTyConApp_maybe elemTf
        , tcElem == elemTyCon -- Check if it's `Elem'`
        -> do
          ty1 <- TC.zonkTcType ty1Unzonked
          ty2 <- TC.zonkTcType ty2Unzonked
          let newWanted = mkNonCanonical (setCtEvPredType ir_ev $ mkTyConApp tcIf [ifKind, mkElemConstraint env ty1 ty2, ifTrue, ifFalse])
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
      pure ([], [wanted], [])

-- Create the new Contains constraint with '[], or the weaker of the two types substituted for unsolved type variables
mkContainsConstraint :: Environment -> Type -> Type -> PredType
mkContainsConstraint Environment{..} ty1 ty2 = mkTyConApp containsTyCon [tYPEKind, ty1Defaulted, ty2Defaulted]
  where
    weakest = getWeakest ty1 ty2
    (ty1Defaulted, ty2Defaulted) = (weakest, weakest)
    -- defaultTypeVar x = if isTyVarTy x then emptyListKindTy else x

-- Create the new Elem constraint with '[ty1] substituted for unsolved type variables
mkElemConstraint :: Environment -> Type -> Type -> PredType
mkElemConstraint Environment{..} ty1 ty2 = mkTyConApp elemTyCon [tYPEKind, ty1, defaultTypeVar ty2]
  where
    defaultTypeVar x = if isTyVarTy x then mkPromotedListTy tYPEKind [ty1] else x

getWeakest :: Type -> Type -> Type
getWeakest ty1 ty2 =
  let ty1Tys = if isTyVarTy ty1
               then []
               else case splitTyConApp_maybe ty1 of
                 Nothing -> []
                 Just (_,ty) -> ty
      ty2Tys = if isTyVarTy ty1
               then []
               else case splitTyConApp_maybe ty2 of
                 Nothing -> []
                 Just (_,ty) -> ty
  in mkPromotedListTy tYPEKind $ nubBy ((==) `on` deBruijnize) (ty1Tys <> ty2Tys)

tcPrintLn :: String -> TC.TcPluginM ()
tcPrintLn = TC.tcPluginIO . putStrLn

tcPrint :: String -> TC.TcPluginM ()
tcPrint = TC.tcPluginIO . putStr

tcPrintOutputable :: Outputable a => a -> TC.TcPluginM ()
tcPrintOutputable = tcPrintLn . showSDocUnsafe . ppr

tcTraceLabel :: Outputable a => String -> a -> TC.TcPluginM ()
tcTraceLabel label x = tcPluginTrace ("[CHECKED_EXCEPTIONS] " <> label) (ppr x)
