{-# LANGUAGE UndecidableInstances #-}
-- | Some fundamental type families and types.
module HordeAd.Core.Types
  ( -- * Kinds of the functors that determine the structure of a tensor type
    TensorType, RankedTensorType, ShapedTensorType, TensorToken(..)
    -- * Some fundamental constraints
  , GoodScalar, HasSingletonDict, Differentiable, IfDifferentiable(..)
    -- * Type families that tensors will belong to
  , RankedOf, ShapedOf, HVectorOf, PrimalOf, DualOf, DummyDual(..)
    -- * Generic types of indexes used in tensor operations
  , IntOf, IndexOf, IntSh, IndexSh
    -- * Generic types of booleans used in tensor operations
  , SimpleBoolOf, Boolean(..)
    -- * Definitions to help express and manipulate type-level natural numbers
  , SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat
  ) where

import Prelude

import           Control.DeepSeq (NFData (..))
import qualified Data.Array.Shape as Sh
import           Data.Boolean (Boolean (..))
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import           GHC.TypeLits
  (KnownNat, Nat, SNat, fromSNat, pattern SNat, withSomeSNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Type.Reflection (Typeable)

import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Internal.TensorFFI
import HordeAd.Util.ShapedList (ShapedList, ShapedNat)
import HordeAd.Util.SizedIndex

-- * Types of types of tensors

type TensorType ty = Type -> ty -> Type

type RankedTensorType = TensorType Nat

type ShapedTensorType = TensorType [Nat]

type role TensorToken nominal
data TensorToken (g :: TensorType ty) = TensorToken

type GoodScalarConstraint r =
  ( Show r, Ord r, Numeric r, Num r, Num (Vector r), RowSum r, Typeable r
  , IfDifferentiable r, NFData r )


-- * Some fundamental constraints

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
-- As a side effect, this avoids ImpredicativeTypes.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

type HasSingletonDict :: ty -> Constraint
type family HasSingletonDict (y :: ty) where
  HasSingletonDict '() = ()
  HasSingletonDict n = KnownNat n
  HasSingletonDict sh = Sh.Shape sh

type Differentiable r = (RealFloat r, RealFloat (Vector r))

-- We white-list all types on which we permit differentiation (e.g., SGD)
-- to work. This is for technical typing purposes and imposes updates
-- (and buggy omissions) when new scalar types are added, but it has
-- the advantage of giving more control and visiblity. As of the time
-- of writing, this is the only place underlying scalars are enumerated.
class IfDifferentiable r where
  ifDifferentiable :: (Differentiable r => a) -> a -> a

instance {-# OVERLAPPABLE #-} IfDifferentiable r where
  ifDifferentiable _ a = a

-- The white-listed differentiable types.
instance IfDifferentiable Double where
  ifDifferentiable ra _ = ra
instance IfDifferentiable Float where
  ifDifferentiable ra _ = ra


-- * Type families that tensors will belong to

-- ty is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family RankedOf (f :: TensorType ty) :: RankedTensorType

type family ShapedOf (f :: TensorType ty) :: ShapedTensorType

type family HVectorOf (f :: RankedTensorType) :: Type

type family PrimalOf (f :: TensorType ty) :: TensorType ty

type family DualOf (f :: TensorType ty) :: TensorType ty

type role DummyDual representational nominal
type DummyDual :: TensorType ty
data DummyDual r (y :: ty) = DummyDual


-- * Generic types of integer indexes used in tensor operations

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: TensorType ty) = RankedOf (PrimalOf f) Int64 0

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf (f :: TensorType ty) n = Index n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IntSh (f :: TensorType ty) (n :: Nat) = ShapedNat n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh (f :: TensorType ty) (sh :: [Nat]) = ShapedList sh (IntOf f)


-- * Generic types of booleans used in tensor operations

type family SimpleBoolOf (t :: ty) :: Type


-- * Definitions to help express and manipulate type-level natural numbers

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
withSNat i f = withSomeSNat (fromIntegral i) $ \msnat -> case msnat of
  Just snat@SNat -> f snat
  Nothing -> error "withSNat: negative argument"

sNatValue :: forall n i. Num i => SNat n -> i
{-# INLINE sNatValue #-}
sNatValue = fromInteger . fromSNat

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy
