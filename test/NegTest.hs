{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin Control.Monad.CheckedExcept.Plugin #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

{-# LANGUAGE DataKinds, TypeApplications, QualifiedDo #-}

module NegTest where

import Control.Exception (SomeException(..), displayException)
import Control.Monad.CheckedExcept
import qualified Control.Monad.CheckedExcept.QualifiedDo as CheckedExcept
import CompTest (testCE1, testCE2, testCE3, testCE4, testCE5)

badThrowChar :: CheckedExceptT '[Int] IO ()
badThrowChar = throwCheckedException 'c'

badBindChar :: CheckedExceptT '[(), Int, Bool, String] IO ()
badBindChar = CheckedExcept.do
  () <- testCE1
  () <- testCE2
  () <- testCE3
  () <- testCE4
  () <- testCE5
  pure ()

runBadBindChar :: IO (Either (OneOf '[(), Int, Bool, String]) ())
runBadBindChar = runCheckedExceptT badBindChar

-- Regression for bad throw: deferred 'Elem Char '[Int]' fires at this
-- consumption site (not at 'throwCheckedException'), because the throw itself
-- type-checks under -fdefer-type-errors.
runBadThrowCharDeferred :: IO ()
runBadThrowCharDeferred = do
  mr <- runCheckedExceptT badThrowChar
  case mr of
    Left o -> useBadThrow o
    Right () -> pure ()
  where
    useBadThrow :: Elem Char '[Int] => OneOf '[Int] -> IO ()
    useBadThrow o = withOneOf @Char o (\c -> c `seq` pure ())

isDeferredTypeError :: SomeException -> Bool
isDeferredTypeError se = deferredTypeErrorInMsg (displayException se)

-- Match the rendered deferred error text, not bare "Elem"/"TypeError" substrings.
deferredTypeErrorInMsg :: String -> Bool
deferredTypeErrorInMsg msg =
  (" is not a member of " `isInfixOf` msg)
    || ("Unsatisfiable" `isInfixOf` msg && "NotElemTypeError" `isInfixOf` msg)
    || ("deferred type error" `isInfixOf` msg)

isInfixOf :: String -> String -> Bool
isInfixOf needle haystack = any (needle `isPrefixOf`) (tails haystack)

isPrefixOf :: String -> String -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (a : as) (b : bs) = a == b && isPrefixOf as bs

tails :: [a] -> [[a]]
tails [] = []
tails xs = xs : tails (drop 1 xs)
