{-# LANGUAGE
    TypeApplications
  , ScopedTypeVariables
  , LambdaCase
#-}

module Control.Monad.CheckedExcept.QualifiedDo
  ( (>>=)
  , (>>)
  , pure
  , return
  , fail
  ) where

import Control.Monad.CheckedExcept
import Prelude hiding (Monad(..), Applicative(..), MonadFail(..))
import qualified Prelude

-- | Bind operator for 'CheckedExceptT' that allows chaining computations
-- that may expand the exception set.
(>>=) :: forall exceptions1 exceptions2 exceptions3 m a.
  ( Contains exceptions1 exceptions3
  , Contains exceptions2 exceptions3
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m a
  -> (a -> CheckedExceptT exceptions2 m a)
  -> CheckedExceptT exceptions3 m a
m >>= f = do
  CheckedExceptT $ do
    runCheckedExceptT m Prelude.>>= \case
      Left e -> Prelude.pure $ Left (weakenOneOf @exceptions1 @exceptions3 e)
      Right a -> runCheckedExceptT (weakenExceptions (f a))

-- | 'pure' function for 'CheckedExceptT'.
pure :: Prelude.Monad m => a -> CheckedExceptT es m a
pure = Prelude.pure

-- | 'return' function for 'CheckedExceptT'.
return :: Prelude.Monad m => a -> CheckedExceptT es m a
return = Prelude.return

-- | Sequentially compose two actions, discarding any value produced by the first.
(>>) :: forall exceptions1 exceptions2 exceptions3 m a x.
  ( Contains exceptions1 exceptions3
  , Contains exceptions2 exceptions3
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m x
  -> CheckedExceptT exceptions2 m a
  -> CheckedExceptT exceptions3 m a
a >> b = weakenExceptions a Prelude.>> weakenExceptions b

-- | 'fail' function for 'CheckedExceptT'.
fail :: Prelude.MonadFail m => String -> CheckedExceptT es m a
fail = Prelude.fail

{-
Example usage:

module CompTest where

import Control.Monad.CheckedExcept
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.CheckedExcept.QualifiedDo as CheckedExcept

testCE1 :: CheckedExceptT '[()] IO ()
testCE1 = CheckedExcept.do
  lift $ putStrLn "1"
  lift $ pure ()
  pure ()

testCE2 :: CheckedExceptT '[Int] IO ()
testCE2 = CheckedExcept.do
  lift $ putStrLn "2"
  throwCheckedException (1 :: Int)
  pure ()

testCE3 :: CheckedExceptT '[Bool] IO ()
testCE3 = CheckedExcept.do
  lift $ putStrLn "3"
  throwCheckedException False
  pure ()

testCE4 :: CheckedExceptT '[String] IO ()
testCE4 = CheckedExcept.do
  lift $ putStrLn "4"
  throwCheckedException "err"
  pure ()

testCE5 :: CheckedExceptT '[Char] IO ()
testCE5 = CheckedExcept.do
  lift $ putStrLn "5"
  throwCheckedException 'c'
  pure ()

testCE :: CheckedExceptT '[(), Int, Bool, String] IO ()
testCE = CheckedExcept.do
  () <- testCE1
  () <- testCE2
  () <- testCE3
  () <- testCE4
  -- () <- testCE5 -- doesn't compile
  pure ()

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
      <: CaseAny (\x -> putStrLn $ encodeException x)
      -- <: (\b -> putStrLn "bool")
      -- <: (\s -> putStrLn "string")
      -- <: CaseEnd
      )
  Right () -> putStrLn "Right"

type TestExceptions = '[(), Int, Bool, String]

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int
deriving via (ShowException Bool) instance CheckedException Bool
deriving via (ShowException String) instance CheckedException [Char]
deriving via (ShowException Char) instance CheckedException Char
-}
