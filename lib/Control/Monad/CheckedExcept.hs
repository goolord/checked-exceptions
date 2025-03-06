{-# LANGUAGE
    KindSignatures
  , TypeFamilies
  , DataKinds
  , TypeOperators
  , UndecidableInstances
  , GADTs
  , TypeApplications
  , ScopedTypeVariables
  , RankNTypes
  , StandaloneDeriving
  , DefaultSignatures
  , DerivingVia
  , PolyKinds
  , LambdaCase
  , MultiParamTypeClasses
  , AllowAmbiguousTypes
  , ConstraintKinds
  , PatternSynonyms
  , FlexibleContexts
#-}

-- | Basic API of t'CheckedExceptT'
module Control.Monad.CheckedExcept
  ( -- * Types
    CheckedExceptT(..)
  , CheckedExcept
  , CaseException(..)
  , (<:)
  , pattern CaseEnd
  , OneOf
  , Union(..)
  , ShowException(..)
  , ExceptionException(..)
  -- * Typeclass
  , CheckedException(..)
  -- * Utility functions
  , runCheckedExcept
  , throwCheckedException
  , weakenExceptions
  , withOneOf
  , applyAll
  , caseException
  , catchSomeException
  -- * Type families / constraints
  , Contains
  , IsMember
  , NonEmpty
  , Nub
  , Remove
  , type (++)
  , NotElemTypeError
  ) where

import Data.Functor ((<&>))
import Control.Exception (Exception(..), SomeException)
import Control.Monad.Except
import Data.Functor.Identity
import Data.Kind
import GHC.TypeLits
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans (..))
import Control.Monad.Catch (MonadCatch (..))
import Data.WorldPeace

data IsCheckedException x where
  IsCheckedException :: CheckedException x => x -> IsCheckedException x

type OneOf es = Union IsCheckedException es

-- | Isomorphic to t'ExceptT' over our open-union exceptions type @t'OneOf' es@.
-- Because many effects systems have an t'ExceptT' analogue, this would be pretty simple to port to any effects system.
-- See "Control.Monad.CheckedExcept.QualifiedDo" for example usages.
newtype CheckedExceptT (exceptions :: [Type]) m a
  = CheckedExceptT { runCheckedExceptT :: m (Either (OneOf exceptions) a) }
  deriving (Monad, Applicative, Functor, MonadFail, MonadIO, MonadError (OneOf exceptions)) via (ExceptT (OneOf exceptions) m)
  deriving (MonadTrans) via (ExceptT (OneOf exceptions))

-- | Pure checked exceptions.
type CheckedExcept es a = CheckedExceptT es Identity a

-- | See 'weakenOneOf'.
weakenExceptions :: forall exceptions1 exceptions2 m a.
     Functor m
  => Contains exceptions1 exceptions2
  => CheckedExceptT exceptions1 m a
  -> CheckedExceptT exceptions2 m a
weakenExceptions (CheckedExceptT ma) = CheckedExceptT $ do
  ma <&> \case
    Left e -> Left $ relaxUnion @exceptions1 @exceptions2 e
    Right a -> Right a

-- | Get the error from t'CheckedExcept'.
runCheckedExcept :: CheckedExcept es a -> Either (OneOf es) a
runCheckedExcept ce = runIdentity (runCheckedExceptT ce)

-- | The class for checked exceptions.
class CheckedException e where
  -- | Encode an exception to 'String'. Defaults to 'displayException' when available.
  encodeException :: e -> String

  default encodeException :: Exception e => e -> String
  encodeException = displayException

-- | DerivingVia newtype wrapper to derive 'Control.Monad.CheckedExcept.CheckedException' from a 'Show' instance declaration.
-- Useful for prototyping, but I wouldn't recommend this for serious work.
newtype ShowException a = ShowException a

instance (Show a) => CheckedException (ShowException a) where
  encodeException (ShowException x) = show x

-- | DerivingVia newtype wrapper to derive 'Control.Monad.CheckedExcept.CheckedException' from 'Exception'.
newtype ExceptionException a = ExceptionException a

instance (Show a, Exception a) => CheckedException (ExceptionException a) where
  encodeException (ExceptionException e) = displayException e

deriving via (ExceptionException SomeException) instance CheckedException SomeException

-- | Throw a checked exception @e@ that is a member of the exception set @es@.
throwCheckedException :: forall e es m a. (IsMember e es, CheckedException e, Applicative m) => e -> CheckedExceptT es m a
throwCheckedException e = do
  CheckedExceptT $ pure $ Left $ unionLift (IsCheckedException e)

-- | Apply a function @f@ over a checked exception, using methods from the 'Control.Monad.CheckedExcept.CheckedException' typeclass.
applyAll :: forall es b. (forall e. CheckedException e => e -> b) -> OneOf es -> b
applyAll f oneOf = go oneOf
  where
  go :: forall xs. OneOf xs -> b
  go (This (IsCheckedException e)) = f e
  go (That newOneOf) = go newOneOf

-- | Catch an exception or @mempty@ (think @pure ()@ or @Nothing@).
withOneOf :: (IsMember e es, Monoid a, CheckedException e) => OneOf es -> (e -> a) -> a
withOneOf e f = case unionMatch e of
  Just (IsCheckedException e') -> f e'
  Nothing -> mempty

-- | Remove duplicates from a type-level list.
type family Nub xs where
  Nub '[] = '[]
  Nub (x ': xs) = x ': Nub (Remove x xs)

-- | Type-level list concatenation.
infixr 5 ++
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

-- | Type-level proof that a list is non-empty, used for constraining 'caseException' so that you don't
-- pointlessly throw @'error'@.
type family NonEmpty xs :: Constraint where
  NonEmpty '[] = TypeError ('Text "type level list must be non-empty")
  NonEmpty _ = () :: Constraint

-- | Data type used for constructing a coverage checked case-like `catch`.
data CaseException x es where
  CaseEndWith :: x -> CaseException x '[]
  CaseCons :: (e -> x) -> CaseException x es -> CaseException x (e ': es)
  CaseAny :: (forall e. CheckedException e => (e -> x)) -> CaseException x es

-- | Pattern synonym for @CaseEndWith (error "impossible")@.
-- This should never be evaluated since 'caseException' does not accept empty lists.
pattern CaseEnd :: forall x. CaseException x '[]
pattern CaseEnd <- _ where
  CaseEnd = CaseEndWith (error "impossible")

-- | Infix 'CaseCons' with proper fixity.
infixr 7 <:
(<:) :: (e -> x) -> CaseException x es -> CaseException x (e : es)
(<:) = CaseCons

-- TODO: (Nub es) in CaseException
-- | Case on a checked exception with coverage checking. Note: while @es@ may not be a set,
-- the 'CaseException' you supply must be.
caseException :: NonEmpty (Nub es) => OneOf es -> CaseException x es -> x
caseException oneOf = go oneOf
  where
  go :: OneOf as -> CaseException x as -> x
  go (This (IsCheckedException a)) (CaseCons f _)  = f a
  go (That u)                      (CaseCons _ p)  = go u p
  go (This (IsCheckedException a)) (CaseAny f)     = f a
  go (That u)                      (CaseAny f)     = go u (CaseAny f)

-- | Add 'SomeException' to the exceptions set. Preferably, call this before catching the checked
-- exceptions so there are no surprising exceptions.
catchSomeException :: (Monad m, MonadCatch m, IsMember SomeException es) => CheckedExceptT es m a -> CheckedExceptT es m a
catchSomeException ce = do
  me <- lift $ catch (Right <$> runCheckedExceptT ce) (pure . Left)
  case me of
    Right a -> CheckedExceptT $ pure a
    Left e -> throwCheckedException (e :: SomeException)

-- | Type error for when @'Elem' e es'@ fails to hold.
type NotElemTypeError x xs = TypeError ('ShowType x ':<>: 'Text " is not a member of " ':<>: 'ShowType xs)
