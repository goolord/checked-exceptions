{-# LANGUAGE 
    MagicHash 
  , TemplateHaskell
  , TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
#-}

{-# OPTIONS_GHC
    -fno-warn-orphans
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

type TestExceptions = '[(), Int]

test :: CheckedExcept TestExceptions () -> IO ()
test ce = case runCheckedExcept ce of
  Left e -> do 
    applyAll (putStrLn . encodeException) e
    -- or
    withOneOf @() e $ \() -> putStrLn "()"
    withOneOf @Int e $ \n -> print $ n + 1
  Right () -> putStrLn "Right"

{- 
-- doens't compile
test2 :: CheckedExcept '[] () -> IO ()
test2 ce = 
  case runCheckedExcept ce of
    Left (OneOf e) -> do 
      caseException (Proxy @'[]) e Nil
    Right () -> putStrLn "Right"
-}

