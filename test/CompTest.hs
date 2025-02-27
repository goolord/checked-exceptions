{-# OPTIONS_GHC
    -fno-warn-orphans
#-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file
#-}
{-# OPTIONS_GHC -fplugin Control.Monad.CheckedExcept.Plugin -fplugin-opt Control.Monad.CheckedExcept.Plugin:verbose  #-}

{-# LANGUAGE
    MagicHash
  , TemplateHaskell
  , TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
  , QualifiedDo
  , FlexibleInstances
#-}

module CompTest where

-- import Test.Tasty.HUnit
import Control.Monad.CheckedExcept
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.CheckedExcept.QualifiedDo as CheckedExcept

testCE1 :: CheckedExceptT '[()] IO ()
testCE1 = CheckedExcept.do
  lift $ putStrLn "1"
  lift $ putStrLn "2"
  pure ()

-- testCE2 :: CheckedExceptT '[Int] IO ()
-- testCE2 = CheckedExcept.do
--   lift $ putStrLn "2"
--   throwCheckedException (1 :: Int)
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
--   throwCheckedException (2 :: Int)
--   pure ()
--
-- testCE :: CheckedExceptT TestExceptions IO ()
-- testCE = CheckedExcept.do
--   () <- testCE1
--   () <- testCE2
--   -- () <- testCE3
--   -- () <- testCE4
--   pure ()

--
-- test :: CheckedExcept TestExceptions () -> IO ()
-- test ce = case runCheckedExcept ce of
--   Left e -> do 
--     applyAll (putStrLn . encodeException) e
--     -- or
--     withOneOf @() e $ \() -> putStrLn "()"
--     withOneOf @Int e $ \n -> print $ n + 1
--     withOneOf @Bool e $ \_ -> pure ()
--     -- or
--     caseException e
--       (  (\() -> putStrLn "()")
--       <: (\n -> print $ n + 1)
--       <: RecAny (\x -> putStrLn $ encodeException x)
--       -- <: (\b -> putStrLn "bool")
--       -- <: (\s -> putStrLn "string")
--       -- <: RecNil
--       )
--   Right () -> putStrLn "Right"

{- 
-- doens't compile
test2 :: CheckedExcept '[] () -> IO ()
test2 ce = 
  case runCheckedExcept ce of
    Left (OneOf e) -> do 
      caseException (Proxy @'[]) e Nil
    Right () -> putStrLn "Right"
-}

type TestExceptions = '[(), Int, Bool, String, ()]

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int
deriving via (ShowException Bool) instance CheckedException Bool
deriving via (ShowException String) instance CheckedException [Char]
