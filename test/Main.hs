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
import Test.Tasty.HUnit
import CompTest
import Control.Exception (try, SomeException(..))
import Control.Monad.CheckedExcept
import Data.Either (isRight)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "testCE" $ do
      testCERes <- try @SomeException $ runCheckedExceptT $ runCheckedExceptStack testCE
      assertBool "testCE does not throw SomeException" (isRight testCERes)
  ]

unwrap :: Either a b -> b
unwrap = either (error "unwrap") id
