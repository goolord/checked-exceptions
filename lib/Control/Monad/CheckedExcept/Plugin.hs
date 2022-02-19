{-# LANGUAGE CPP #-}

module Control.Monad.CheckedExcept.Plugin (plugin) where

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
#else
import GhcPlugins
#endif

import Control.Monad.CheckedExcept.Plugin.Bind

plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = const $ Just bindPlugin
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile  = purePlugin
#endif
    }

