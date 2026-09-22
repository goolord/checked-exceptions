{-# LANGUAGE CPP #-}

-- | Type checking plugin to assist with unification of weakened exceptions.
module Control.Monad.CheckedExcept.Plugin (plugin) where

import GHC.Plugins
import Control.Monad.CheckedExcept.Plugin.Defaulting (mkDefaultingPlugin)
import Control.Monad.CheckedExcept.Plugin.Elem (mkElemPlugin)

-- | Help resolve ambiguous exception-set metavariables in
-- 'Control.Monad.CheckedExcept.QualifiedDo'.'Control.Monad.CheckedExcept.QualifiedDo.>>='.
--
-- The 'defaultingPlugin' proposes exception lists; GHC verifies each
-- assignment. The @tcPlugin@ solves 'Control.Monad.CheckedExcept.Elem'
-- constraints that instance resolution leaves stuck, with real index evidence
-- (see "Control.Monad.CheckedExcept.Plugin.Elem").
plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = Just . mkElemPlugin
    , defaultingPlugin = mkDefaultingPlugin
#if __GLASGOW_HASKELL__ >= 806
    , pluginRecompile = purePlugin
#endif
    }
