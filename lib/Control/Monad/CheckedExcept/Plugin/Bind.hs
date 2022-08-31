{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Control.Monad.CheckedExcept.Plugin.Bind where

import qualified Data.Set as S
import GHC.IORef (newIORef, IORef)
import GHC.Plugins
import GHC.Tc.Types.Constraint
import qualified GHC.Tc.Plugin as TC
import qualified GHC.Tc.Types as TC

bindPlugin :: TcPlugin
bindPlugin _ = Just $ TC.TcPlugin
  { TC.tcPluginInit = pure ()
  , TC.tcPluginSolve = const solveBind
  , TC.tcPluginStop = const $ pure ()
  , TC.tcPluginRewrite = mempty
  }

thePlugin :: TC.TcPluginM ()
thePlugin = pure ()

lookupCheckedExceptMod :: TC.TcPluginM Module
lookupCheckedExceptMod = do
   findResult <- TC.findImportedModule ( mkModuleName "Control.Monad.CheckedExcept" ) NoPkgQual -- ( Just "checked-exceptions" )
   case findResult of
     TC.Found _ modCE -> pure modCE
     _ -> error "Couldn't find Control.Monad.CheckedExcept"

lookupElem :: Module -> TC.TcPluginM TyCon
lookupElem modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "MyFam"
  myTyFam_Name <- TC.lookupOrig modCE myTyFam_OccName
  TC.tcLookupTyCon myTyFam_Name

solveBind :: TC.TcPluginSolver
solveBind _ _ [] = pure $ TC.TcPluginOk [] []
solveBind given _ wanted = do
  fuckingTraceString "given: "
  fuckingTraceOutputable given
  fuckingTraceString "wanted: "
  fuckingTraceOutputable wanted
  pure $ TC.TcPluginOk [] []

fuckingTraceString :: String -> TC.TcPluginM ()
fuckingTraceString = TC.tcPluginIO . putStrLn

fuckingTraceOutputable :: Outputable a => a -> TC.TcPluginM ()
fuckingTraceOutputable = fuckingTraceString . showSDocUnsafe . ppr

-- data ElemConstraint = ElemConstraint
--   { loc        :: CtLoc
--   , l1         :: Type  -- ^ @State@
--   , effect     :: Type  -- ^ @State s@
--   , row        :: Type  -- ^ @r@
--   }
