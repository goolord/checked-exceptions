{-# LANGUAGE ViewPatterns #-}

-- | @do@ blocks for 'CheckedExceptT' that compose exceptions.
--
-- Requires @-fplugin Control.Monad.CheckedExcept.Plugin@ so ambiguous
-- exception-list metavariables (e.g. from 'pure' / 'return' in a block) can
-- default to @'[]@ or a 'Nub' union of accumulated bounds.
module Control.Monad.CheckedExcept.QualifiedDo  ( (>>=)
  , (>>)
  , pure
  , return
  , fail
  ) where

import Control.Monad.CheckedExcept
import Prelude hiding (Monad(..), Applicative(..), MonadFail(..))
import qualified Prelude

type UnionExceptions es1 es2 = Nub (es1 ++ es2)

(>>=) :: forall exceptions1 exceptions2 m a b.
  ( Contains exceptions1 (UnionExceptions exceptions1 exceptions2)
  , Contains exceptions2 (UnionExceptions exceptions1 exceptions2)
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m a
  -> (a -> CheckedExceptT exceptions2 m b)
  -> CheckedExceptT (UnionExceptions exceptions1 exceptions2) m b
m >>= f = do
  CheckedExceptT $ do
    runCheckedExceptT m Prelude.>>= \case
      Left e ->
        Prelude.pure $
          Left (weakenOneOf @(exceptions1) @(UnionExceptions exceptions1 exceptions2) e)
      Right a ->
        runCheckedExceptT (weakenExceptions @(exceptions2) @(UnionExceptions exceptions1 exceptions2) (f a))

-- | Leaves @es@ free; empty 'do' blocks need the type-checker plugin to default
-- @es@ (see module header).
pure :: Prelude.Monad m => a -> CheckedExceptT es m a
pure = Prelude.pure

-- | Same caveat as 'pure'.
return :: Prelude.Monad m => a -> CheckedExceptT es m a
return = Prelude.return

(>>) :: forall exceptions1 exceptions2 m a x.
  ( Contains exceptions1 (UnionExceptions exceptions1 exceptions2)
  , Contains exceptions2 (UnionExceptions exceptions1 exceptions2)
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m x
  -> CheckedExceptT exceptions2 m a
  -> CheckedExceptT (UnionExceptions exceptions1 exceptions2) m a
a >> b =
  weakenExceptions @(exceptions1) @(UnionExceptions exceptions1 exceptions2) a
    Prelude.>> weakenExceptions @(exceptions2) @(UnionExceptions exceptions1 exceptions2) b

fail :: Prelude.MonadFail m => String -> CheckedExceptT es m a
fail = Prelude.fail
