{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DataKinds, TypeApplications, QualifiedDo, DerivingVia, StandaloneDeriving #-}

module RuntimeTest where

import Control.Exception (SomeException(..))
import Control.Monad.CheckedExcept
import Control.Monad.IO.Class (liftIO)
import CompTest ()

weakened :: Either (OneOf '[Int, String]) ()
weakened = runCheckedExcept $ weakenExceptions weakenAction
  where
    weakenAction :: CheckedExcept '[Int] ()
    weakenAction = throwCheckedException (99 :: Int)

withOneOfTest :: String
withOneOfTest =
  let e = oneOf @Char @'[Char] 'h'
  in withOneOf @Char e (\c -> "got: " <> [c])

caseExceptionFull :: String
caseExceptionFull =
  let e = oneOf @Int @'[Int] (7 :: Int)
  in caseException e ((\n -> "int: " <> show n) <: CaseEnd)

caseExceptionAny :: String
caseExceptionAny =
  let e = oneOf @Char @'[Char] 'x'
  in caseException e (CaseAny (\c -> encodeException c))

catchSomeTest :: IO Bool
catchSomeTest = do
  me <-
    runCheckedExceptT $
      catchSomeException $
        (CheckedExceptT $ liftIO (error "boom") :: CheckedExceptT '[SomeException] IO ())
  pure $
    case me of
      Left _ -> True
      _ -> False
