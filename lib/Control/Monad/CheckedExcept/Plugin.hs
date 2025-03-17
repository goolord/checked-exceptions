{-# LANGUAGE
    CPP
  , PackageImports
  , RecordWildCards
#-}

-- | type checking plugin to assist with unification of weakened exceptions
module Control.Monad.CheckedExcept.Plugin (plugin) where

import "ghc" GHC.Plugins
import "ghc" GHC.Tc.Types
import qualified "ghc-lib" GHC.Plugins as GHCLIB
import qualified "ghc-lib" GHC.Tc.Types as GHCLIB
import Control.Monad.CheckedExcept.Plugin.Bind

-- | help resolve ambiguous type variables resulting from the
-- very general type of "Control.Monad.CheckedExcept.QualifiedDo".'Control.Monad.CheckedExcept.QualifiedDo.>>='
plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = \args -> case bindPlugin args of
        Just GHCLIB.TcPlugin{..} -> Just TcPlugin{..}
        Nothing -> Nothing
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile  = purePlugin
#endif
    }
