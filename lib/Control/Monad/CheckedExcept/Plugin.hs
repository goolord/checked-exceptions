{-# LANGUAGE CPP #-}

-- | type checking plugin to assist with unification of weakened exceptions
module Control.Monad.CheckedExcept.Plugin (plugin) where

import GHC.Plugins
import Control.Monad.CheckedExcept.Plugin.Bind

-- | help resolve ambiguous type variables resulting from the
-- very general type of "Control.Monad.CheckedExcept.QualifiedDo".'Control.Monad.CheckedExcept.QualifiedDo.>>='
plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = bindPlugin
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile  = purePlugin
#endif
    }

