{-# LANGUAGE CPP #-}

-- | Type checking plugin to assist with unification of weakened exceptions.
module Control.Monad.CheckedExcept.Plugin (plugin) where

import GHC.Plugins
import Control.Monad.CheckedExcept.Plugin.Defaulting (mkDefaultingPlugin)

-- | Help resolve ambiguous exception-set metavariables in
-- 'Control.Monad.CheckedExcept.QualifiedDo'.'Control.Monad.CheckedExcept.QualifiedDo.>>='.
--
-- Uses 'defaultingPlugin' only (@tcPlugin@ is disabled; the old rewrite/solve
-- path is removed — code that relied on fiat coercions must use defaulting).
plugin :: Plugin
plugin =
  defaultPlugin
    { -- Defaulting proposals only; GHC verifies each assignment.
      tcPlugin = const Nothing
    , defaultingPlugin = mkDefaultingPlugin
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile = purePlugin
#endif
    }
