{-# LANGUAGE UndecidableInstances #-}
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
  , SShape(..), KnownShape(..)
  ) where

import Prelude

import           Control.DeepSeq (NFData (..))
import qualified Data.Array.Shape as Sh
import           Data.Boolean (Boolean (..))
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import           GHC.TypeLits
  (KnownNat, Nat, SNat, fromSNat, natSing, pattern SNat, withSomeSNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Type.Reflection (Typeable)

import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Internal.TensorFFI

-- * Types of types of tensors

type TensorType ty = Type -> ty -> Type

type RankedTensorType = TensorType Nat

type ShapedTensorType = TensorType [Nat]

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


-- * Definitions for type-level list shapes

-- Below, copied with modification from ox-arrays.

-- | The shape of a shape-typed array given as a list of 'SNat' values.
type role SShape nominal
data SShape sh where
  ShNil :: SShape '[]
  ShCons :: Sh.Shape sh => SNat n -> SShape sh -> SShape (n : sh)
deriving instance Show (SShape sh)
infixr 5 `ShCons`

-- | A statically-known shape of a shape-typed array.
class KnownShape sh where knownShape :: SShape sh
instance KnownShape '[] where knownShape = ShNil
instance (KnownNat n, KnownShape sh, Sh.Shape sh)
         => KnownShape (n : sh) where knownShape = ShCons natSing knownShape
