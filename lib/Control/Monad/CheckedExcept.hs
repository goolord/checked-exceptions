{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

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
  , FlexibleInstances
  , FlexibleContexts
  , IncoherentInstances
#-}

-- | Basic API of t'CheckedExceptT'
module Control.Monad.CheckedExcept
  ( -- * Types
    CheckedExceptT(..)
  , CheckedExcept
  , OneOf
  , oneOf
  , ElemIx(..)
  , Subset(..)
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
  , weakenExceptionsWith
  , weakenOneOf
  , weakenOneOfWith
  , withOneOf
  , withOneOf'
  , caseException
  , (<:)
  , catchSomeException
  , containsRefl
  , lookupSubset
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
import GHC.TypeLits
import GHC.TypeError (Unsatisfiable, unsatisfiable)
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans (..))
import Data.Constraint (Dict (..), withDict)
import Control.Monad.Catch (MonadCatch (..))

-- | Isomorphic to t'ExceptT' over our open-union exceptions type @t'OneOf' es@.
newtype CheckedExceptT (exceptions :: [Type]) m a
  = CheckedExceptT { runCheckedExceptT :: m (Either (OneOf exceptions) a) }
  deriving (Monad, Applicative, Functor, MonadFail, MonadIO, MonadError (OneOf exceptions)) via (ExceptT (OneOf exceptions) m)
  deriving (MonadTrans) via (ExceptT (OneOf exceptions))

-- | Pure checked exceptions.
type CheckedExcept es a = CheckedExceptT es Identity a

-- | Reflexive subset witness for abstract exception lists.
containsRefl :: Subset es es
containsRefl = SubRefl

-- | See 'weakenOneOfWith'.
weakenExceptions :: forall exceptions1 exceptions2 m a.
     Functor m
  => Contains exceptions1 exceptions2
  => CheckedExceptT exceptions1 m a
  -> CheckedExceptT exceptions2 m a
weakenExceptions ce = weakenExceptionsWith subset ce

-- | Weaken using an explicit subset witness.
weakenExceptionsWith ::
     Functor m
  => Subset exceptions1 exceptions2
  -> CheckedExceptT exceptions1 m a
  -> CheckedExceptT exceptions2 m a
weakenExceptionsWith s (CheckedExceptT ma) = CheckedExceptT $ do
  ma <&> \case
    Left e -> Left $ weakenOneOfWith s e
    Right a -> Right a

-- | See 'weakenOneOfWith'.
weakenOneOf :: forall exceptions1 exceptions2.
     Contains exceptions1 exceptions2
  => OneOf exceptions1
  -> OneOf exceptions2
weakenOneOf e = weakenOneOfWith subset e

-- | Reconstruct a @t'OneOf' exceptions1@ as part of a larger @t'OneOf' exceptions2@.
weakenOneOfWith :: Subset exceptions1 exceptions2 -> OneOf exceptions1 -> OneOf exceptions2
weakenOneOfWith s (MkOneOf ix e) = MkOneOf (lookupSubset s ix) e

-- | Get the error from t'CheckedExcept'.
runCheckedExcept :: CheckedExcept es a -> Either (OneOf es) a
runCheckedExcept ce = runIdentity (runCheckedExceptT ce)

-- | The class for checked exceptions.
class Typeable e => CheckedException e where
  encodeException :: e -> String
  -- | Reify an exception from a 'OneOf' when its runtime type matches @e@.
  -- Custom instances should preserve this contract: @'Just'@ only when the
  -- payload type equals @e@ (same rule as the default 'eqT' witness path).
  fromOneOf :: forall es. OneOf es -> Maybe e

  default encodeException :: Exception e => e -> String
  encodeException = displayException

  default fromOneOf :: forall es. OneOf es -> Maybe e
  fromOneOf o = withOneOf' o match
    where
      match :: forall e'. Typeable e' => e' -> Maybe e
      match x = case eqT @e @e' of
        Just Refl -> Just x
        Nothing -> Nothing

-- | DerivingVia newtype wrapper to derive 'CheckedException' from a 'Show' instance.
newtype ShowException a = ShowException a

instance (Show a, Typeable a) => CheckedException (ShowException a) where
  encodeException (ShowException x) = show x
  fromOneOf o = withOneOf' o $ \(x :: e') -> case eqT @a @e' of
    Just Refl -> Just (ShowException x)
    Nothing -> Nothing

-- | DerivingVia newtype wrapper to derive 'CheckedException' from 'Exception'.
newtype ExceptionException a = ExceptionException a

instance (Typeable a, Exception a) => CheckedException (ExceptionException a) where
  encodeException (ExceptionException e) = displayException e
  fromOneOf o = withOneOf' o $ \(x :: e') -> case eqT @a @e' of
    Just Refl -> Just (ExceptionException x)
    Nothing -> Nothing

deriving via (ExceptionException SomeException) instance CheckedException SomeException

-- | Witness that @e@ occurs at a specific position in @es@.
data ElemIx (e :: Type) (es :: [Type]) where
  Here :: ElemIx e (e ': es)
  There :: !(ElemIx e es) -> ElemIx e (f ': es)

-- | Witness that every element of @es1@ is contained in @es2@.
data Subset (es1 :: [Type]) (es2 :: [Type]) where
  SubRefl :: Subset es es
  SubNil :: Subset '[] es2
  SubCons :: !(ElemIx e es2) -> !(Subset es1 es2) -> Subset (e ': es1) es2

-- | Translate a membership index along a subset witness.
lookupSubset :: Subset es1 es2 -> ElemIx e es1 -> ElemIx e es2
lookupSubset SubRefl ix = ix
lookupSubset (SubCons ix _) Here = ix
lookupSubset (SubCons _ s) (There ix) = lookupSubset s ix
lookupSubset SubNil ix = case ix of {}

-- | Recover an 'Elem' dictionary from a membership index.
elemDictFromIx :: forall e es. ElemIx e es -> Dict (Elem e es)
elemDictFromIx Here = Dict
elemDictFromIx (There ix) = withDict (elemDictFromIx ix) Dict

-- | Membership in a type-level list, backed by a value-level index.
--
-- Duplicate types in @es@ are not supported: the incoherent tail instance
-- picks the first index, so prefer @'Nub' es@ (or a duplicate-free list) at
-- the kind level.
class Elem (e :: Type) (es :: [Type]) where
  elemIx :: ElemIx e es

instance {-# OVERLAPPING #-} Elem e (e ': es) where
  elemIx = Here

instance {-# INCOHERENT #-} Elem e es => Elem e (x ': es) where
  elemIx = There (elemIx @e @es)

instance Unsatisfiable (NotElemTypeError e '[]) => Elem e '[] where
  elemIx = unsatisfiable

-- | @es1@ is a subset of @es2@.
--
-- There is no reflexive instance for abstract @es@: use 'containsRefl' or
-- 'weakenExceptionsWith' when @es1@ and @es2@ are the same type variable.
class Contains (es1 :: [Type]) (es2 :: [Type]) where
  subset :: Subset es1 es2

instance Contains '[] es2 where
  subset = SubNil

instance (Elem e es2, Contains es1 es2) => Contains (e ': es1) es2 where
  subset = SubCons (elemIx @e @es2) (subset @es1 @es2)

-- | A sort of pseudo-open union backed by membership witnesses.
data OneOf (es :: [Type]) where
  MkOneOf :: forall e es. (CheckedException e, Typeable e) => !(ElemIx e es) -> !e -> OneOf es

{-# COMPLETE MkOneOf #-}

-- | Construct a checked exception value.
oneOf :: forall e es. (Elem e es, CheckedException e) => e -> OneOf es
oneOf e = MkOneOf (elemIx @e @es) e

-- | Data type used for constructing a coverage checked case-like @catch@.
data CaseException x es where
  CaseEndWith :: x -> CaseException x '[]
  CaseCons :: Typeable e => (e -> x) -> CaseException x es -> CaseException x (e ': es)
  CaseAny :: (forall e. CheckedException e => (e -> x)) -> CaseException x es

pattern CaseEnd :: forall x. CaseException x '[]
pattern CaseEnd <- _ where
  CaseEnd = CaseEndWith (error "impossible")

infixr 7 <:
(<:) :: Typeable e => (e -> x) -> CaseException x es -> CaseException x (e : es)
(<:) = CaseCons

throwCheckedException :: forall e es m a. (Elem e es, CheckedException e, Applicative m) => e -> CheckedExceptT es m a
throwCheckedException e = CheckedExceptT $ pure $ Left (oneOf e)

applyAll :: (forall e. CheckedException e => e -> b) -> OneOf es -> b
applyAll f (MkOneOf _ e) = f e

-- | Run @f@ when the payload type equals @e@; otherwise return 'mempty'.
--
-- Uses an @eqT@ witness (like the default 'fromOneOf'), not a custom
-- 'fromOneOf' instance — a custom 'fromOneOf' returning 'Nothing' does not
-- affect this function.
withOneOf :: forall e es a. (Monoid a, CheckedException e) => OneOf es -> (e -> a) -> a
withOneOf o f = withOneOf' o $ \(x :: e') -> case eqT @e @e' of
  Just Refl -> f x
  Nothing -> mempty

withOneOf' :: OneOf es -> (forall e. (Elem e es, CheckedException e, Typeable e) => e -> a) -> a
withOneOf' (MkOneOf ix e) f = withDict (elemDictFromIx ix) (f e)

type family Nub xs where
  Nub '[] = '[]
  Nub (x ': xs) = x ': Nub (Remove x xs)

infixr 5 ++
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': xs ++ ys

type family Remove x xs where
  Remove x '[] = '[]
  Remove x (x ': ys) = Remove x ys
  Remove x (y ': ys) = y ': Remove x ys

type family Elem' x xs where
  Elem' x '[] = 'False
  Elem' x (x ': xs) = 'True
  Elem' x (y ': xs) = Elem' x xs

type NotElemTypeError x xs =
  TypeError ('ShowType x ':<>: 'Text " is not a member of " ':<>: 'ShowType xs)

type family NonEmpty xs :: Constraint where
  NonEmpty '[] = TypeError ('Text "type level list must be non-empty")
  NonEmpty _ = () :: Constraint

caseException :: OneOf es -> CaseException x (Nub es) -> x
caseException (MkOneOf _ e') = go e'
  where
  -- Dispatch uses the case-arm type (@eCase@, from @f@'s domain), not runtime
  -- inspection beyond @eqT@. Safe while 'CaseCons' keeps this typing; revisit
  -- if 'CaseCons' is ever generalized.
  branch :: forall eVal eCase x'. (Typeable eVal, Typeable eCase) => eVal -> (eCase -> x') -> Maybe x'
  branch x f = case eqT @eCase @eVal of
    Just Refl -> Just (f x)
    Nothing -> Nothing
  go :: CheckedException e => e -> CaseException x es -> x
  go e (CaseCons f rec) = case branch e f of
    Just x -> x
    Nothing -> go e rec
  go e (CaseAny f) = f e
  go _ (CaseEndWith x) = x

catchSomeException :: (Monad m, MonadCatch m, Elem SomeException es) => CheckedExceptT es m a -> CheckedExceptT es m a
catchSomeException ce = do
  me <- lift $ catch (Right <$> runCheckedExceptT ce) (pure . Left)
  case me of
    Right a -> CheckedExceptT $ pure a
    Left e -> throwCheckedException (e :: SomeException)
