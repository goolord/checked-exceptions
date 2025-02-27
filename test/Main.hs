{-# OPTIONS_GHC
    -fno-warn-orphans
#-}

{-# LANGUAGE
    MagicHash
  , TemplateHaskell
  , TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
  , QualifiedDo
#-}

module Main where

import Test.Tasty
-- import Test.Tasty.HUnit
import Control.Monad.CheckedExcept

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [
  ]

unwrap :: Either a b -> b
unwrap = either (error "unwrap") id
