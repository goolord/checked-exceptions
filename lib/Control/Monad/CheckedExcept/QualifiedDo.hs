{-# LANGUAGE DataKinds, TypeFamilies #-}
-- 'InferExceptions' has no methods: it is only there to drive inference.
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

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
import Data.Kind (Type)
import Prelude hiding (Monad(..), Applicative(..), MonadFail(..))
import qualified Prelude

type UnionExceptions es1 es2 = Nub (es1 ++ es2)

-- | Fixes the result exceptions of a bind when they are still being inferred:
-- they become the union of both sides. When they are already known (e.g. from
-- a signature) nothing is forced; 'Contains' checks each side fits, in any
-- order.
class InferExceptions (es1 :: [Type]) (es2 :: [Type]) (exceptions :: [Type])

instance {-# INCOHERENT #-} exceptions ~ UnionExceptions es1 es2 => InferExceptions es1 es2 exceptions

instance InferExceptions es1 es2 (e ': es)

instance InferExceptions es1 es2 '[]

(>>=) :: forall exceptions1 exceptions2 exceptions m a b.
  ( InferExceptions exceptions1 exceptions2 exceptions
  , Contains exceptions1 exceptions
  , Contains exceptions2 exceptions
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m a
  -> (a -> CheckedExceptT exceptions2 m b)
  -> CheckedExceptT exceptions m b
m >>= f =
  weakenExceptions @exceptions1 @exceptions m
    Prelude.>>= (weakenExceptions @exceptions2 @exceptions . f)
{-# INLINE (>>=) #-}

-- | Leaves @es@ free; empty 'do' blocks need the type-checker plugin to default
-- @es@ (see module header).
pure :: Prelude.Monad m => a -> CheckedExceptT es m a
pure = Prelude.pure

-- | Same caveat as 'pure'.
return :: Prelude.Monad m => a -> CheckedExceptT es m a
return = Prelude.return

(>>) :: forall exceptions1 exceptions2 exceptions m a x.
  ( InferExceptions exceptions1 exceptions2 exceptions
  , Contains exceptions1 exceptions
  , Contains exceptions2 exceptions
  , Prelude.Monad m
  )
  => CheckedExceptT exceptions1 m x
  -> CheckedExceptT exceptions2 m a
  -> CheckedExceptT exceptions m a
a >> b = a >>= \_ -> b
{-# INLINE (>>) #-}

fail :: Prelude.MonadFail m => String -> CheckedExceptT es m a
fail = Prelude.fail
