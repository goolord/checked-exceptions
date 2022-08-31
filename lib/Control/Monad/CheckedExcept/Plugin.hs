{-# LANGUAGE CPP #-}

module Control.Monad.CheckedExcept.Plugin (plugin) where

import GHC.Plugins
import Control.Monad.CheckedExcept.Plugin.Bind

plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = bindPlugin
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile  = purePlugin
#endif
    }

