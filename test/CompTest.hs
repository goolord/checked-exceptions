{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin Control.Monad.CheckedExcept.Plugin #-}

{-# LANGUAGE
    TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
  , QualifiedDo
  , FlexibleInstances
#-}

module CompTest where

import Control.Monad.CheckedExcept
import Data.Typeable (Typeable)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.CheckedExcept.QualifiedDo as CheckedExcept

-- Single-exception helpers use plain @do@ (signature fixes @es@). Only the
-- composing @testCE@ block needs @CheckedExcept.do@ to union exception sets.
testCE1 :: CheckedExceptT '[()] IO ()
testCE1 = do
  lift $ putStrLn "1"
  pure ()

testCE2 :: CheckedExceptT '[Int] IO ()
testCE2 = do
  lift $ putStrLn "2"
  throwCheckedException (1 :: Int)
  pure ()

testCE3 :: CheckedExceptT '[Bool] IO ()
testCE3 = do
  lift $ putStrLn "3"
  throwCheckedException False
  pure ()

testCE4 :: CheckedExceptT '[String] IO ()
testCE4 = do
  lift $ putStrLn "4"
  throwCheckedException "err"
  pure ()

testCE5 :: CheckedExceptT '[Char] IO ()
testCE5 = do
  lift $ putStrLn "5"
  throwCheckedException 'c'
  pure ()

testCE :: CheckedExceptStack ()
testCE =
  CheckedExceptStack $
    (CheckedExcept.do
      () <- testCE1
      () <- testCE2
      () <- testCE3
      () <- testCE4
      -- () <- testCE5 -- doesn't compile
      pure () :: CheckedExceptT TestExceptions IO ())

test :: CheckedExcept TestExceptions () -> IO ()
test ce = case runCheckedExcept ce of
  Left e -> do
    applyAll (putStrLn . encodeException) e
    withOneOf @() e $ \() -> putStrLn "()"
    withOneOf @Int e $ \n -> print $ n + 1
    withOneOf @Bool e $ \_ -> pure ()
    caseException e
      (  (\() -> putStrLn "()")
      <: (\n -> print $ n + 1)
      <: (\_b -> putStrLn "bool")
      <: (\_s -> putStrLn "string")
      <: CaseEnd
      )
    caseException e
      (  (\() -> putStrLn "()")
      <: CaseAny (\x -> putStrLn $ encodeException x)
      )
  Right () -> putStrLn "Right"

type TestExceptions = '[(), Int, Bool, String]

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int
deriving via (ShowException Bool) instance CheckedException Bool
deriving via (ShowException String) instance CheckedException [Char]
deriving via (ShowException Char) instance CheckedException Char

newtype CheckedExceptStack a = CheckedExceptStack { runCheckedExceptStack :: CheckedExceptT TestExceptions IO a }

-- An exception type with a metavariable (@E a@) must still unify with the
-- declared @E Int@ when the block has a signature.
newtype E a = E a
deriving via (ShowException (E a)) instance Typeable a => CheckedException (E a)
instance Show (E a) where show _ = "E"

polyCE :: CheckedExceptT '[E a] IO ()
polyCE = pure ()

testPolyCE :: CheckedExceptT '[E Int, Int] IO ()
testPolyCE = CheckedExcept.do
  polyCE
  testCE2

-- Declared exceptions can be in any order ...
testReordered :: CheckedExceptT '[Int, ()] IO ()
testReordered = CheckedExcept.do
  testCE1
  testCE2

-- ... and may include exceptions that are never thrown.
testWidened :: CheckedExceptT '[Bool, Int, ()] IO ()
testWidened = CheckedExcept.do
  testCE2
  testCE1
