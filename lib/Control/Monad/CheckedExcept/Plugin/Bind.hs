{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Control.Monad.CheckedExcept.Plugin.Bind where

import qualified Data.Set as S
import GHC.IORef (newIORef, IORef)
import GHC.Tc.Types
import GHC.Plugins (Module, TyCon, OccName, SDoc, mkModuleName, mkTcOcc, Outputable (ppr), showSDocUnsafe)
import GHC.Tc.Types.Constraint
import GHC.Tc.Plugin

bindPlugin :: TcPlugin
bindPlugin = TcPlugin
  { tcPluginInit = pure ()
  , tcPluginSolve = solveBind
  , tcPluginStop = const $ pure ()
  }

thePlugin :: TcPluginM ()
thePlugin = pure ()

lookupCheckedExceptMod :: TcPluginM Module
lookupCheckedExceptMod = do
   findResult <- findImportedModule ( mkModuleName "Control.Monad.CheckedExcept" ) ( Just "checked-exceptions" )
   case findResult of
     Found _ modCE -> pure modCE
     _ -> error "Couldn't find Control.Monad.CheckedExcept"

lookupElem :: Module -> TcPluginM TyCon
lookupElem modCE = do
  let
    myTyFam_OccName :: OccName
    myTyFam_OccName = mkTcOcc "MyFam"
  myTyFam_Name <- lookupOrig modCE myTyFam_OccName
  tcLookupTyCon myTyFam_Name

solveBind
    :: ()
    -> [Ct]
    -> [Ct]
    -> [Ct]
    -> TcPluginM TcPluginResult
solveBind _ _ _ [] = pure $ TcPluginOk [] []
solveBind () given _ wanted = do
  fuckingTraceString "given: "
  fuckingTraceOutputable given
  fuckingTraceString "wanted: "
  fuckingTraceOutputable wanted
  pure $ TcPluginOk [] []

fuckingTraceString :: String -> TcPluginM ()
fuckingTraceString = tcPluginIO . putStrLn

fuckingTraceOutputable :: Outputable a => a -> TcPluginM ()
fuckingTraceOutputable = fuckingTraceString . showSDocUnsafe . ppr

-- data ElemConstraint = ElemConstraint
--   { loc        :: CtLoc
--   , l1         :: Type  -- ^ @State@
--   , effect     :: Type  -- ^ @State s@
--   , row        :: Type  -- ^ @r@
--   }
