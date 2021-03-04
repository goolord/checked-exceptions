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

type TestExceptions = '[(), Int, Bool, String]

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int
deriving via (ShowException Bool) instance CheckedException Bool

test :: CheckedExcept TestExceptions () -> IO ()
test ce = case runCheckedExcept ce of
  Left e -> do 
    applyAll (putStrLn . encodeException) e
    -- or
    withOneOf @() e $ \() -> putStrLn "()"
    withOneOf @Int e $ \n -> print $ n + 1
    withOneOf @Bool e $ \_ -> pure ()
    -- or
    caseException e
      (  (\() -> putStrLn "()")
      <: (\n -> print $ n + 1)
      <: RecAny (\x -> putStrLn $ encodeException x)
      -- or: RecNil
      )
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

