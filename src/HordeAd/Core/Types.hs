{-# LANGUAGE AllowAmbiguousTypes, ImpredicativeTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Some fundamental type families and types.
module HordeAd.Core.Types
  ( -- * Kinds of the functors that determine the structure of a tensor type
    TensorType, RankedTensorType, ShapedTensorType
    -- * Some fundamental constraints
  , GoodScalar, HasSingletonDict, Differentiable, IfDifferentiable(..)
    -- * Type families that tensors will belong to
  , IntOf, RankedOf, ShapedOf, HVectorOf, HFunOf, PrimalOf, DualOf, DummyDual(..)
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..)
  , IfF(..), EqF(..), OrdF(..), minF, maxF
    -- * Definitions to help express and manipulate type-level natural numbers
  , SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat
    -- * Definitions for type-level list shapes
  , ShS(..), KnownShS(..), shapeT, shapeP, sizeT, sizeP
  , sshapeKnown, slistKnown, sixKnown, knownShR, knownListR
  , withShapeP, sameShape, matchingRank
  , lemShapeFromKnownShS, lemKnownNatRank, lemKnownNatSize
  , Dict(..), PermC
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Boolean (Boolean (..))
import Data.Int (Int64)
import Data.Kind (Constraint, Type)
import GHC.TypeLits (KnownNat, Nat, type (+))
import Numeric.LinearAlgebra (Numeric, Vector)
import Type.Reflection (Typeable)

import qualified Data.Array.Mixed.Internal.Arith as Nested.Internal.Arith
import           Data.Array.Mixed.Types (Dict (..))
import           Data.Array.Nested
  (IxS (..), KnownShS (..), ListR (..), ListS (..), ShR (..), ShS (..))
import qualified Data.Array.Nested as Nested
import qualified Data.Array.Nested.Internal.Shaped as Nested.Internal

import HordeAd.Internal.OrthotopeOrphanInstances
import HordeAd.Internal.TensorFFI

sshapeKnown :: ShS sh -> Dict KnownShS sh
sshapeKnown ZSS = Dict
sshapeKnown (SNat :$$ sh) | Dict <- sshapeKnown sh = Dict

slistKnown :: ListS sh i -> Dict KnownShS sh
slistKnown ZS = Dict
slistKnown (_ ::$ sh) | Dict <- slistKnown sh = Dict

sixKnown :: IxS sh i -> Dict KnownShS sh
sixKnown ZIS = Dict
sixKnown (_ :.$ sh) | Dict <- sixKnown sh = Dict

knownNatSucc :: KnownNat n => Dict KnownNat (n + 1)
knownNatSucc = Dict

knownShR :: ShR n i -> Dict KnownNat n
knownShR ZSR = Dict
knownShR (_ :$: (l :: ShR m i)) | Dict <- knownShR l = knownNatSucc @m

knownListR :: ListR n i -> Dict KnownNat n
knownListR ZR = Dict
knownListR (_ ::: (l :: ListR m i)) | Dict <- knownListR l = knownNatSucc @m

-- * Types of types of tensors

type TensorType ty = Type -> ty -> Type

type RankedTensorType = TensorType Nat

type ShapedTensorType = TensorType [Nat]

type GoodScalarConstraint r =
  ( Show r, Ord r, Numeric r, Num r, Num (Vector r), RowSum r, Typeable r
  , IfDifferentiable r, NFData r, Nested.PrimElt r, Nested.Elt r, Nested.Internal.Arith.NumElt r, forall sh. Show (Nested.Mixed sh r), forall sh. Eq (Nested.Mixed sh r), forall sh. NFData (Nested.Mixed sh r), Ord (Nested.Mixed '[] r) )


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
  HasSingletonDict sh = KnownShS sh

type Differentiable r =
  (RealFloat r, RealFloat (Vector r), Nested.Internal.Arith.FloatElt r)

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

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: TensorType ty) = RankedOf (PrimalOf f) Int64 0

-- ty is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family RankedOf (f :: TensorType ty) :: RankedTensorType

type family ShapedOf (f :: TensorType ty) :: ShapedTensorType

type HVectorOf :: RankedTensorType -> Type
type family HVectorOf f = result | result -> f

-- | The type family is defined in order to give a special instance
-- for AST that preservs sharing and, even more importantly, keeps
-- the computation of dervative functions lazy. See the definition
-- of 'AstLambda' and the code that processes it, maintaining laziness.
--
-- The type family can't easily be made injective, because the @ADVal f@
-- instance is independent of @f@.
type family HFunOf (f :: RankedTensorType) :: Type

type family PrimalOf (f :: TensorType ty) :: TensorType ty

type family DualOf (f :: TensorType ty) :: TensorType ty

type role DummyDual representational nominal
type DummyDual :: TensorType ty
data DummyDual r (y :: ty) = DummyDual


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: ty) :: Type

class Boolean (BoolOf f) => IfF (f :: TensorType ty) where
  ifF :: (GoodScalar r, HasSingletonDict y)
      => BoolOf f -> f r y -> f r y -> f r y

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: TensorType ty) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (==.), (/=.) :: (GoodScalar r, HasSingletonDict y)
               => f r y -> f r y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: TensorType ty) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
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
