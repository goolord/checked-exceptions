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
#-}

module Control.Monad.CheckedExcept 
  ( -- types
    CheckedExceptT(..)
  , CheckedExcept
  , OneOf(..)
  -- type families / constraints
  , Contains
  , Elem
  -- typeclass
  , CheckedException(..)
  -- utility functions
  , runCheckedExcept
  , throwCheckedException
  , applyAll
  , weakenExceptions
  , weakenOneOf
  , withOneOf
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
import Data.Typeable (Typeable, cast)

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

deriving via (ShowException ()) instance CheckedException ()
deriving via (ShowException Int) instance CheckedException Int

data OneOf (es :: [Type]) where 
  OneOf :: forall e es. (Elem e es, CheckedException e, Typeable e) => !e -> OneOf es

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

type family Elem' x xs where
  Elem' x '[] = 'False
  Elem' x (x ': xs) = 'True
  Elem' x (y ': xs) = Elem' x xs

type family Elem x xs :: Constraint where
  Elem x xs = 
    If (Elem' x xs) 
      (() :: Constraint)
      (TypeError ('ShowType x ':<>: 'Text " is not a member of " ':<>: 'ShowType xs))

type family Contains (as :: [k]) (bs :: [k]) :: Constraint where
  Contains '[] _ = ()
  Contains (a ': as) bs = (Elem a bs, Contains as bs)

