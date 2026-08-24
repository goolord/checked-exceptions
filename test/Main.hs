{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeApplications, DataKinds, QualifiedDo #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import CompTest
import NegTest
import RuntimeTest
import Control.Exception (try, SomeException(..))
import Control.Monad.CheckedExcept
import Data.Either (isRight)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "checked-exceptions"
    [ unitTests
    , runtimeTests
    , negativeTests
    ]

unitTests :: TestTree
unitTests =
  testGroup
    "compile-time"
    [ testCase "testCE runs without SomeException" $ do
        testCERes <- try @SomeException $ runCheckedExceptT $ runCheckedExceptStack testCE
        assertBool "testCE does not throw SomeException" (isRight testCERes)
    ]

runtimeTests :: TestTree
runtimeTests =
  testGroup
    "runtime"
    [ testCase "weakenExceptions widens exception set" $
        case weakened of
          Left e -> withOneOf @Int e $ \n -> assertEqual "weakened int" (99 :: Int) n
          Right _ -> assertFailure "expected Left"
    , testCase "withOneOf catches matching type" $
        assertEqual "withOneOf" "got: h" withOneOfTest
    , testCase "caseException full coverage" $
        assertEqual "caseException full" "int: 7" caseExceptionFull
    , testCase "caseException CaseAny" $
        assertEqual "caseException any" "'x'" caseExceptionAny
    , testCase "catchSomeException wraps IO errors" $ do
        ok <- catchSomeTest
        assertBool "caught SomeException" ok
    ]

negativeTests :: TestTree
negativeTests =
  testGroup
    "deferred type errors"
    [ testCase "bad throw throws TypeError at runtime" $ do
        result <- try @SomeException runBadThrowCharDeferred
        case result of
          Left se -> assertBool "deferred TypeError" (isDeferredTypeError se)
          Right () -> assertFailure "expected deferred type error"
    , testCase "bad bind throws TypeError at runtime" $ do
        result <- try @SomeException runBadBindChar
        case result of
          Left se -> assertBool "deferred TypeError" (isDeferredTypeError se)
          Right _ -> assertFailure "expected deferred type error"
    ]
