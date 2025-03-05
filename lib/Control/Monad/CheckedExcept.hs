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
#-}
{-# LANGUAGE PatternSynonyms #-}

-- | Basic API of t'CheckedExceptT'
module Control.Monad.CheckedExcept
  ( -- * Types
    CheckedExceptT(..)
  , CheckedExcept
  , OneOf(..)
  , CaseException(..)
  , pattern CaseEnd
  , ShowException(..)
  , ExceptionException(..)
  -- * Typeclass
  , CheckedException(..)
  -- * Utility functions
  , runCheckedExcept
  , throwCheckedException
  , applyAll
  , weakenExceptions
  , weakenOneOf
  , withOneOf
  , withOneOf'
  , caseException
  , (<:)
  , catchSomeException
  -- * Type families / constraints
  , Contains
  , Elem
  , Elem'
  , NonEmpty
  , NotElemTypeError
  , Nub
  , Remove
  , type (++)
  ) where

import Data.Functor ((<&>))
import Control.Exception (Exception(..), SomeException)
import Control.Monad.Except
import Data.Functor.Identity
import Data.Kind
import Data.Type.Bool
import GHC.TypeLits
import Data.Constraint
import Data.Typeable (Typeable, cast, eqT)
import Data.Type.Equality
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans (..))
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Control.Monad.Catch (MonadCatch (..))

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
    Left e -> Left $ weakenOneOf @exceptions1 @exceptions2 e
    Right a -> Right a

-- | Given a proof that @exceptions1@ is a subset of @exceptions2@,
-- reconstruct the value of the @t'OneOf' exceptions1@ open union to be part of the larger
-- @t'OneOf' exceptions2@ open union. This allows us to compose t'Control.Monad.CheckedExcept.CheckedExceptT' stacks
-- with differing exception sets.
weakenOneOf :: forall exceptions1 exceptions2.
     Contains exceptions1 exceptions2
  => OneOf exceptions1
  -> OneOf exceptions2
weakenOneOf (OneOf e') = weakenE e'
  where
  weakenE :: forall e.
      ( Elem e exceptions1
      , CheckedException e
      , Typeable e
      )
    => e
    -> OneOf exceptions2
  weakenE e = do
    -- I don't know how to safely prove this, but the `Contains` constraint guarantees this is true/safe.
    let dict1 :: Dict (Elem e exceptions2)
        dict1 = proveElem @exceptions1 @exceptions2 @e
    OneOf e \\ dict1

-- | Prove that if @e@ is an element of @exceptions1@ and @exceptions1@ is a subset of @exceptions2@,
-- then @e@ is an element of @exceptions2@.
proveElem :: forall exceptions1 exceptions2 e.
  ( Contains exceptions1 exceptions2
  , Elem e exceptions1
  ) => Dict (Elem e exceptions2)
proveElem = withDict (unsafeCoerceConstraint :: (Elem e exceptions1, Contains exceptions1 exceptions2) :- (Elem e exceptions2)) Dict

-- | Get the error from t'CheckedExcept'.
runCheckedExcept :: CheckedExcept es a -> Either (OneOf es) a
runCheckedExcept ce = runIdentity (runCheckedExceptT ce)

-- | The class for checked exceptions.
class Typeable e => CheckedException e where
  -- | Encode an exception to 'String'. Defaults to 'displayException' when available.
  encodeException :: e -> String
  -- | Reify the exception. Defaults to @'withOneOf\'' e cast@.
  fromOneOf :: forall es. OneOf es -> Maybe e

  default encodeException :: Exception e => e -> String
  encodeException = displayException

  default fromOneOf :: Typeable e => OneOf es -> Maybe e
  fromOneOf e = withOneOf' e cast

-- | DerivingVia newtype wrapper to derive 'Control.Monad.CheckedExcept.CheckedException' from a 'Show' instance declaration.
-- Useful for prototyping, but I wouldn't recommend this for serious work.
newtype ShowException a = ShowException a

instance (Show a, Typeable a) => CheckedException (ShowException a) where
  encodeException (ShowException x) = show x

-- | DerivingVia newtype wrapper to derive 'Control.Monad.CheckedExcept.CheckedException' from 'Exception'.
newtype ExceptionException a = ExceptionException a

instance (Show a, Typeable a, Exception a) => CheckedException (ExceptionException a) where
  encodeException (ExceptionException e) = displayException e

deriving via (ExceptionException SomeException) instance CheckedException SomeException

-- | A sort of pseudo-open union that is easy to construct but difficult to
-- deconstruct. In lieu of singletons we opt for 'Typeable' to prove the type
-- of the existentially quantified exception @e@ in the set @es@.
data OneOf (es :: [Type]) where
  OneOf :: forall e es. (Elem e es, CheckedException e, Typeable e) => !e -> OneOf es

-- | Data type used for constructing a coverage checked case-like `catch`.
data CaseException x es where
  CaseEndWith :: x -> CaseException x '[]
  CaseCons :: Typeable e => (e -> x) -> CaseException x es -> CaseException x (e ': es)
  CaseAny :: (forall e. CheckedException e => (e -> x)) -> CaseException x es

-- | Pattern synonym for @CaseEndWith (error "impossible")@.
-- This should never be evaluated since 'caseException' does not accept empty lists.
pattern CaseEnd :: forall x. CaseException x '[]
pattern CaseEnd <- _ where
  CaseEnd = CaseEndWith (error "impossible")

-- | Infix 'CaseCons' with proper fixity.
infixr 7 <:
(<:) :: Typeable e => (e -> x) -> CaseException x es -> CaseException x (e : es)
(<:) = CaseCons

-- | Throw a checked exception @e@ that is a member of the exception set @es@.
throwCheckedException :: forall e es m a. (Elem e es, CheckedException e, Applicative m) => e -> CheckedExceptT es m a
throwCheckedException e = do
  let oneOf :: OneOf es
      oneOf = OneOf e
  CheckedExceptT $ pure $ Left oneOf

-- | Apply a function @f@ over a checked exception, using methods from the 'Control.Monad.CheckedExcept.CheckedException' typeclass.
applyAll :: (forall e. CheckedException e => e -> b) -> OneOf es -> b
applyAll f (OneOf e) = f e

-- | Catch an exception or @mempty@ (think @pure ()@ or @Nothing@).
withOneOf :: (Elem e es, Monoid a, CheckedException e) => OneOf es -> (e -> a) -> a
withOneOf e f = case fromOneOf e of
  Just x -> f x
  Nothing -> mempty

-- | Catch an exception, totally.
withOneOf' :: OneOf es -> (forall e. (Elem e es, CheckedException e, Typeable e) => e -> a) -> a
withOneOf' (OneOf e) f = f e

-- | Remove duplicates from a type-level list.
type family Nub xs where
  Nub '[] = '[]
  Nub (x ': xs) = x ': Nub (Remove x xs)

-- | Type-level list concatenation.
infixr 5 ++
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

-- | Remove element from a type-level list.
type family Remove x xs where
  Remove x '[]       = '[]
  Remove x (x ': ys) =      Remove x ys
  Remove x (y ': ys) = y ': Remove x ys

-- | Is @x@ present in the list @xs@?
type family Elem' x xs where
  Elem' x '[] = 'False
  Elem' x (x ': xs) = 'True
  Elem' x (y ': xs) = Elem' x xs

-- TODO: Sometimes causes weird type errors when it doesn't propagate correctly.
-- | @ type Elem x xs = Elem' x xs ~ 'True @
type family Elem x xs :: Constraint where
  Elem x xs =
    If (Elem' x xs)
      (() :: Constraint)
      (NotElemTypeError x xs)

-- | Type error for when @'Elem' e es'@ fails to hold.
type NotElemTypeError x xs = TypeError ('ShowType x ':<>: 'Text " is not a member of " ':<>: 'ShowType xs)

-- | Constraint that the list @as@ is a subset of list @bs@.
type family Contains (as :: [k]) (bs :: [k]) :: Constraint where
  Contains '[] _ = ()
  Contains as as = ()
  Contains (a ': as) bs = (Elem' a bs ~ 'True, Contains as bs)

-- | Type-level proof that a list is non-empty, used for constraining 'caseException' so that you don't
-- pointlessly throw @'error'@.
type family NonEmpty xs :: Constraint where
  NonEmpty '[] = TypeError ('Text "type level list must be non-empty")
  NonEmpty _ = () :: Constraint

-- TODO: Exceptions can show up more than once in the list, which we handle with
-- 'Nub', but the error message we give to the user for trying to catch an exception
-- twice is really bad.
--
-- | Case on a checked exception with coverage checking. Note: while @es@ may not be a set,
-- the 'CaseException' you supply must be.
caseException :: NonEmpty es => OneOf es -> CaseException x (Nub es) -> x
caseException (OneOf e') = go e'
  where
  test :: (Typeable e1, Typeable e2) => e2 -> (e1 -> x) -> Maybe (e1 :~: e2)
  test _ _ = eqT
  go :: (CheckedException e, Typeable e) => e -> CaseException x es -> x
  go e (CaseCons f rec) = case test e f of
    Just Refl -> f e
    Nothing -> go e rec
  go e (CaseAny f) = f e
  go _ (CaseEndWith x) = x

-- | Add 'SomeException' to the exceptions set. Preferably, call this before catching the checked
-- exceptions so there are no surprising exceptions.
catchSomeException :: (Monad m, MonadCatch m, Elem SomeException es) => CheckedExceptT es m a -> CheckedExceptT es m a
catchSomeException ce = do
  me <- lift $ catch (Right <$> runCheckedExceptT ce) (pure . Left)
  case me of
    Right a -> CheckedExceptT $ pure a
    Left e -> throwCheckedException (e :: SomeException)
