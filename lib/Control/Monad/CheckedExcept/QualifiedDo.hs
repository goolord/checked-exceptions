{-# LANGUAGE
    TypeApplications
  , ScopedTypeVariables
  , LambdaCase
#-}

module Control.Monad.CheckedExcept.QualifiedDo where

import Control.Monad.CheckedExcept
import Prelude hiding (Monad(..), Applicative(..))
import qualified Prelude

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

pure :: Prelude.Monad m => a -> CheckedExceptT es m a
pure = Prelude.pure

return :: Prelude.Monad m => a -> CheckedExceptT es m a
return = Prelude.return

(>>) :: forall exceptions1 exceptions2 exceptions3 m a x.
  ( Contains exceptions1 exceptions3
  , Contains exceptions2 exceptions3
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m x
  -> CheckedExceptT exceptions2 m a
  -> CheckedExceptT exceptions3 m a
a >> b = weakenExceptions a Prelude.>> weakenExceptions b

fail :: Prelude.MonadFail m => String -> CheckedExceptT es m a
fail = Prelude.fail
