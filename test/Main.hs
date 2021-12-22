{-# LANGUAGE 
    MagicHash 
  , TemplateHaskell
  , TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
  , QualifiedDo
#-}

{-# OPTIONS_GHC
    -fno-warn-orphans
#-}

module Main where

import Test.Tasty
-- import Test.Tasty.HUnit
import Control.Monad.CheckedExcept
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.CheckedExcept.QualifiedDo as CheckedExcept

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

type TestExceptions = '[(), Int, Bool, String, ()]

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int
deriving via (ShowException Bool) instance CheckedException Bool

-- doesn't work boo
-- testCE :: CheckedExceptT TestExceptions IO ()
-- testCE = CheckedExcept.do
--   () <- testCE1
--   () <- testCE2
--   () <- testCE3
--   () <- testCE4
--   pure ()
-- 
-- testCE1 :: CheckedExceptT '[()] IO ()
-- testCE1 = CheckedExcept.do
--   lift $ putStrLn "1"
--   pure ()
-- 
-- testCE2 :: CheckedExceptT '[Int] IO ()
-- testCE2 = CheckedExcept.do
--   lift $ putStrLn "2"
--   throwCheckedException 1
--   pure ()
-- 
-- testCE3 :: CheckedExceptT '[Bool] IO ()
-- testCE3 = CheckedExcept.do
--   lift $ putStrLn "3"
--   throwCheckedException False
--   pure ()
-- 
-- testCE4 :: CheckedExceptT '[String] IO ()
-- testCE4 = CheckedExcept.do
--   lift $ putStrLn "4"
--   throwCheckedException "err"
--   pure ()

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
      -- <: (\b -> putStrLn "bool")
      -- <: (\s -> putStrLn "string")
      -- <: RecNil
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

