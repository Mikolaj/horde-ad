{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Some fundamental kinds, type families and types.
module HordeAd.Core.Types
  ( -- * Kinds of the functors that determine the structure of a tensor type
    TensorKind, RankedTensorKind, ShapedTensorKind
    -- * Some fundamental constraints
  , GoodScalar, HasSingletonDict, Differentiable, IfDifferentiable(..)
    -- * Type definitions for dynamic tensors and tensor collections
  , DynamicExists(..), Domains, DomainsOD, sizeDomainsOD, sameShapesDomainsOD
    -- * Type families that tensors will belong to
  , RankedOf, ShapedOf, DynamicOf, DomainsOf, PrimalOf, DualOf, DummyDual(..)
    -- * Generic types of indexes used in tensor operations
  , IntOf, IndexOf, IntSh, IndexSh
    -- * Generic types of booleans used in tensor operations
  , SimpleBoolOf, Boolean(..)
    -- * Definitions to help express and manipulate type-level natural numbers
  , SNat(..), withSNat, sNatValue, proxyFromSNat
  ) where

import Prelude

import           Control.DeepSeq (NFData (..))
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.Internal.Shape as OS
import           Data.Boolean (Boolean (..))
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, SomeNat (..), natVal, someNatVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Type.Reflection (Typeable)

import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Internal.TensorFFI
import HordeAd.Util.ShapedList (ShapedList, ShapedNat)
import HordeAd.Util.SizedIndex

-- * Kinds of the functors that determine the structure of a tensor type

type TensorKind k = Type -> k -> Type

type RankedTensorKind = TensorKind Nat

type ShapedTensorKind = TensorKind [Nat]

type GoodScalarConstraint r =
  ( Show r, Ord r, Numeric r, Num r, Num (Vector r), RowSum r, Typeable r
  , IfDifferentiable r, NFData r )


-- * Some fundamental constraints

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
-- As a side effect, this avoids ImpredicativeTypes.
class GoodScalarConstraint r => GoodScalar r
instance GoodScalarConstraint r => GoodScalar r

type HasSingletonDict :: k -> Constraint
type family HasSingletonDict (y :: k) where
  HasSingletonDict '() = ()
  HasSingletonDict n = KnownNat n
  HasSingletonDict sh = OS.Shape sh

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


-- * Type definitions for dynamic tensors and tensor collections

-- Warning: r is an existential variable, a proper specialization needs
-- to be picked explicitly at runtime.
data DynamicExists :: (Type -> Type) -> Type where
  DynamicExists :: forall r dynamic. GoodScalar r
                => dynamic r -> DynamicExists dynamic
deriving instance (forall r. GoodScalar r => Show (dynamic r))
                  => Show (DynamicExists dynamic)
instance (forall r. NFData r => NFData (dynamic r))
         => NFData (DynamicExists dynamic) where
  rnf (DynamicExists x) = rnf x

-- When r is Ast, this is used for domains composed of variables only,
-- to adapt them into more complex types and back again. This is not used
-- for vectors of large terms, since they'd share values, so we'd need
-- AstDomainsLet, but these would make adapting the vector costly.
-- DomainsOf is used for that and the only reasons DomainsOf exists
-- is to prevent mixing up the two (and complicating the definition
-- below with errors in the AstDomainsLet case).
type Domains dynamic = Data.Vector.Vector (DynamicExists dynamic)

type DomainsOD = Domains OD.Array

sizeDomainsOD :: DomainsOD -> Int
sizeDomainsOD d = let f (DynamicExists t) = OD.size t
                  in V.sum (V.map f d)

sameShapesDomainsOD :: DomainsOD -> DomainsOD -> Bool
sameShapesDomainsOD v1 v2 =
  let sameExShape (DynamicExists arr1, DynamicExists arr2) =
        OD.shapeL arr1 == OD.shapeL arr2
  in V.all sameExShape $ V.zip v1 v2


-- * Type families that tensors will belong to

-- k is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family RankedOf (f :: TensorKind k) :: RankedTensorKind

type family ShapedOf (f :: TensorKind k) :: ShapedTensorKind

type family DynamicOf (f :: TensorKind k) :: Type -> Type

type family DomainsOf (f :: TensorKind k) :: Type

type family PrimalOf (f :: TensorKind k) :: TensorKind k

type family DualOf (f :: TensorKind k) :: TensorKind k

data DummyDual a (b :: k) = DummyDual


-- * Generic types of integer indexes used in tensor operations

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: TensorKind k) = RankedOf (PrimalOf f) Int64 0

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf (f :: TensorKind k) n = Index n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IntSh (f :: TensorKind k) (n :: Nat) = ShapedNat n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh (f :: TensorKind k) (sh :: [Nat]) = ShapedList sh (IntOf f)


-- * Generic types of booleans used in tensor operations

type family SimpleBoolOf (t :: k) :: Type


-- * Definitions to help express and manipulate type-level natural numbers

-- TODO: Use SNat from base once we use GHC >= 9.6 exclusively.
-- | Sizes of tensor dimensions, of batches, etc., packed for passing
-- between functions as witnesses of type variable values.
data SNat (n :: Nat) where
  SNat :: KnownNat n => SNat n

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
withSNat i f = case someNatVal $ toInteger $ abs i of
  Just (SomeNat @n _) -> f (SNat @n)
  Nothing -> error "withSNat: impossible"

sNatValue :: forall n i. (KnownNat n, Num i) => SNat n -> i
{-# INLINE sNatValue #-}
sNatValue = fromInteger . natVal

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy
