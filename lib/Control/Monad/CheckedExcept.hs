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

module Control.Monad.CheckedExcept 
  ( -- types
    CheckedExceptT(..)
  , CheckedExcept
  , OneOf(..)
  , Rec(..)
  , ShowException(..)
  -- type families / constraints
  , Contains
  , Elem
  , Nub
  , Remove
  , type (++)
  -- typeclass
  , CheckedException(..)
  -- utility functions
  , runCheckedExcept
  , throwCheckedException
  , applyAll
  , weakenExceptions
  , weakenOneOf
  , withOneOf
  , caseException
  , (<:)
  ) where

import Data.Functor ((<&>))
import Control.Exception (Exception(..))
import Control.Monad.Except
import Data.Functor.Identity
import Data.Kind
import Data.Type.Bool
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)
import Data.Constraint
import Data.Typeable (Typeable, cast, eqT)
import Data.Type.Equality
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans)

newtype CheckedExceptT (exceptions :: [Type]) m a 
  = CheckedExceptT { runCheckedExceptT :: m (Either (OneOf exceptions) a) }
  deriving (Monad, Applicative, Functor, MonadFail, MonadIO) via (ExceptT (OneOf exceptions) m)
  deriving (MonadTrans) via (ExceptT (OneOf exceptions))

type CheckedExcept es a = CheckedExceptT es Identity a

weakenExceptions :: forall exceptions1 exceptions2 m a. 
     Functor m
  => Contains exceptions1 exceptions2 
  => CheckedExceptT exceptions1 m a
  -> CheckedExceptT exceptions2 m a
weakenExceptions (CheckedExceptT ma) = CheckedExceptT $ do
  ma <&> \case
    Left e -> Left $ weakenOneOf @exceptions1 @exceptions2 e
    Right a -> Right a

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
    -- idk how to safely prove this, but the `Contains` constraint guarentees this is true/safe
    let dict1 :: Dict (Elem e exceptions2)
        dict1 = unsafeCoerce (Dict @(Elem e exceptions1))
    OneOf e \\ dict1

runCheckedExcept :: CheckedExcept es a -> Either (OneOf es) a
runCheckedExcept ce = runIdentity (runCheckedExceptT ce)

class Typeable e => CheckedException e where
  encodeException :: e -> String
  fromOneOf :: forall es. OneOf es -> Maybe e

  default encodeException :: Exception e => e -> String
  encodeException = displayException

  default fromOneOf :: Typeable e => OneOf es -> Maybe e
  fromOneOf (OneOf e) = cast e

newtype ShowException a = ShowException a

instance (Show a, Typeable a) => CheckedException (ShowException a) where
  encodeException (ShowException x) = show x

data OneOf (es :: [Type]) where 
  OneOf :: forall e es. (Elem e es, CheckedException e, Typeable e) => !e -> OneOf es

data Rec x es where
  RecNil :: Rec x '[]
  RecCons :: Typeable e => (e -> x) -> Rec x es -> Rec x (e ': es)
  RecAny :: (forall e. CheckedException e => (e -> x)) -> Rec x es

-- | infix RecCons with proper fixity
infixr 7 <:
(<:) :: Typeable e => (e -> x) -> Rec x es -> Rec x (e : es)
(<:) = RecCons

throwCheckedException :: forall e es m a. (Elem e es, CheckedException e, Applicative m) => e -> CheckedExceptT es m a
throwCheckedException e = do
  let oneOf :: OneOf es
      oneOf = OneOf e
  CheckedExceptT $ pure $ Left oneOf

applyAll :: (forall e. CheckedException e => e -> b) -> OneOf es -> b
applyAll f (OneOf e) = f e

withOneOf :: (Elem e es, Monoid a, CheckedException e) => OneOf es -> (e -> a) -> a
withOneOf e f = case fromOneOf e of
  Just x -> f x
  Nothing -> mempty

-- | Remove duplicates from a type-level list.
type family Nub xs where
  Nub '[] = '[]
  Nub (x ': xs) = x ': Nub (Remove x xs)

infixr 5 ++
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[]       ++ ys = ys
    (x ': xs) ++ ys = x ': xs ++ ys

-- | Remove element from a type-level list.
type family Remove x xs where
  Remove x '[]       = '[]
  Remove x (x ': ys) =      Remove x ys
  Remove x (y ': ys) = y ': Remove x ys

type family Elem' x xs where
  Elem' x '[] = 'False
  Elem' x (x ': xs) = 'True
  Elem' x (y ': xs) = Elem' x xs

-- type Elem x xs = Elem' x xs ~ 'True
-- sometimes causes weird type errors when it doesn't propagate correctly ??
type family Elem x xs :: Constraint where
  Elem x xs = 
    If (Elem' x xs)
      (() :: Constraint)
      (TypeError ('ShowType x ':<>: 'Text " is not a member of " ':<>: 'ShowType xs))

type family Contains (as :: [k]) (bs :: [k]) :: Constraint where
  Contains '[] _ = ()
  Contains as as = ()
  Contains (a ': as) bs = (Elem' a bs ~ 'True, Contains as bs)

type family NonEmpty xs :: Constraint where
  NonEmpty '[] = TypeError ('Text "type level list must be non-empty")
  NonEmpty _ = () :: Constraint

-- todo: exceptions can show up more than once in the list..
caseException :: NonEmpty es => OneOf es -> Rec x (Nub es) -> x
caseException (OneOf e') = go e'
  where
  test :: (Typeable e1, Typeable e2) => e2 -> (e1 -> x) -> Maybe (e1 :~: e2)
  test _ _ = eqT
  go :: (CheckedException e, Typeable e) => e -> Rec x es -> x
  go e (RecCons f rec) = case test e f of
    Just Refl -> f e
    Nothing -> go e rec
  go e (RecAny f) = f e
  go _ RecNil = error "impossible"
