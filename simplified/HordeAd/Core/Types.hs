{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Some fundamental kinds, type families and types.
module HordeAd.Core.Types
  ( TensorKind, RankedTensorKind, ShapedTensorKind
  , GoodScalar, HasSingletonDict, IfDifferentiable(..)
  , DynamicExists(..), Domains, DomainsOD, sizeDomainsOD
  , RankedOf, ShapedOf, PrimalOf, DualOf, IntOf, IndexOf, IntSh, IndexSh
  , DummyDual(..)
  , BoolOf, Boolean(..), IfF(..), EqF(..), OrdF(..), minF, maxF
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.Internal.Shape as OS
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Boolean (Boolean (..))
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Type.Reflection (Typeable)

import HordeAd.Core.ShapedList (ShapedList, ShapedNat)
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorOps

type TensorKind k = Type -> k -> Type

type RankedTensorKind = TensorKind Nat

type ShapedTensorKind = TensorKind [Nat]

type GoodScalarConstraint r =
  ( Show r, Ord r, Numeric r, Num r, Num (Vector r), RowSum r, Typeable r
  , IfDifferentiable r )

-- Attempted optimization via storing one pointer to a class dictionary
-- in existential datatypes instead of six pointers. No effect, strangely.
-- As a side effect, this avoids ImpredicativeTypes.
class (GoodScalarConstraint r, Floating r => Floating (Vector r))
      => GoodScalar r
instance
      (GoodScalarConstraint r, Floating r => Floating (Vector r))
      => GoodScalar r

type HasSingletonDict :: k -> Constraint
type family HasSingletonDict (y :: k) where
  HasSingletonDict '() = ()
  HasSingletonDict n = KnownNat n
  HasSingletonDict sh = OS.Shape sh

-- We white-list all types on which we permit differentiation (e.g., SGD)
-- to work. This is for technical typing purposes and imposes updates
-- (and buggy omissions) when new scalar types are added, but it has
-- the advantage of giving more control and visiblity.
class IfDifferentiable r where
  ifDifferentiable :: (RealFloat r => a) -> a -> a

instance {-# OVERLAPPABLE #-} IfDifferentiable r where
  ifDifferentiable _ a = a

-- The white-listed differentiable types.
instance IfDifferentiable Double where
  ifDifferentiable ra _ = ra
instance IfDifferentiable Float where
  ifDifferentiable ra _ = ra

data DynamicExists :: (Type -> Type) -> Type where
  DynamicExists :: forall r dynamic. GoodScalar r
                => dynamic r -> DynamicExists dynamic
deriving instance (forall r. GoodScalar r => Show (dynamic r))
                  => Show (DynamicExists dynamic)

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

-- k is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family RankedOf (f :: TensorKind k) :: RankedTensorKind

type family ShapedOf (f :: TensorKind k) :: ShapedTensorKind

type family PrimalOf (f :: TensorKind k) :: TensorKind k

type family DualOf (f :: TensorKind k) :: TensorKind k

-- This is used only in indexing and similar contexts.
-- If used as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.
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

data DummyDual a (b :: k) = DummyDual

-- This and below is inspired by https://hackage.haskell.org/package/Boolean,
-- but renamed so that it does not conflict with it nor with Applicative
-- and modified to depend on the tensor structure functor only,
-- not on the type resulting from applying the functor to the underlying
-- scalar and rank/shape.
type family BoolOf (t :: k) :: Type

class Boolean (BoolOf f) => IfF (f :: TensorKind k) where
  ifF :: (GoodScalar r, HasSingletonDict y)
      => BoolOf f -> f r y -> f r y -> f r y

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: TensorKind k) where
  (==.), (/=.) :: (GoodScalar r, HasSingletonDict y)
               => f r y -> f r y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: TensorKind k) where
  (<.), (<=.), (>.), (>=.) :: (GoodScalar r, HasSingletonDict y)
                           => f r y -> f r y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u

minF :: (IfF f, OrdF f, GoodScalar r, HasSingletonDict y)
     => f r y -> f r y -> f r y
minF u v = ifF (u <=. v) u v

maxF :: (IfF f, OrdF f, GoodScalar r, HasSingletonDict y)
     => f r y -> f r y -> f r y
maxF u v = ifF (u >=. v) u v


-- * Boolean instances

type instance BoolOf (Flip OR.Array) = Bool

instance IfF (Flip OR.Array) where
  ifF b v w = if b then v else w

instance EqF (Flip OR.Array) where
  (==.) = (==)
  (/=.) = (/=)

instance OrdF (Flip OR.Array) where
  (<.) = (<)
  (<=.) = (<=)
  (>.) = (>)
  (>=.) = (>=)

type instance BoolOf (Flip OS.Array) = Bool

instance IfF (Flip OS.Array) where
  ifF b v w = if b then v else w

instance EqF (Flip OS.Array) where
  (==.) = (==)
  (/=.) = (/=)

instance OrdF (Flip OS.Array) where
  (<.) = (<)
  (<=.) = (<=)
  (>.) = (>)
  (>=.) = (>=)
