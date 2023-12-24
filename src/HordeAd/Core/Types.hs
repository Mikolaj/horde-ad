{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
-- | Some fundamental kinds, type families and types.
module HordeAd.Core.Types
  ( -- * Kinds of the functors that determine the structure of a tensor type
    TensorKind, RankedTensorKind, ShapedTensorKind, TensorFunctor(..)
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
    -- * ADShare definition
  , AstVarId, intToAstVarId
  , AstBindingsD, ADShareD
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare, varInADShare, nullADShare
  ) where

import Prelude

import           Control.DeepSeq (NFData (..))
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.Shape as Sh
import           Data.Boolean (Boolean (..))
import           Data.Int (Int64)
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Constraint, Type)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, SomeNat (..), natVal, someNatVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)
import           Type.Reflection (Typeable)

import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Internal.TensorFFI
import HordeAd.Util.ShapedList (ShapedList, ShapedNat)
import HordeAd.Util.SizedIndex

-- * Kinds of the functors that determine the structure of a tensor type

type TensorKind k = Type -> k -> Type

type RankedTensorKind = TensorKind Nat

type ShapedTensorKind = TensorKind [Nat]

type role TensorFunctor nominal
data TensorFunctor (g :: TensorKind k) = TensorFunctor

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


-- * Type definitions for dynamic tensors and tensor collections

-- Warning: r is an existential variable, a proper specialization needs
-- to be picked explicitly at runtime.
type role DynamicExists representational  -- TODO: safe enough?
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

type role DummyDual representational nominal
type DummyDual :: forall {k}. TensorKind k
data DummyDual r (y :: k) = DummyDual


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
type role SNat nominal
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


-- * ADShare definition

-- We avoid adding a phantom type denoting the tensor functor,
-- because it can't be easily compared (even fully applies) and so the phantom
-- is useless. We don't add the underlying scalar nor the rank/shape,
-- because some collections differ in those too, e.g., domain,
-- e.g. in AstLetDomainsS. We don't add a phantom span, because
-- carrying around type constructors that need to be applied to span
-- complicates the system greatly for moderate type safety gain
-- and also such a high number of ID types induces many conversions.
newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

type AstBindingsD :: (Type -> Type) -> Type
type AstBindingsD dynamic = [(AstVarId, DynamicExists dynamic)]

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- Data invariant: the list is reverse-sorted wrt keys.
-- This permits not inspecting too long a prefix of the list, usually,
-- which is crucial for performance. The strictness is crucial for correctness
-- in the presence of impurity for generating fresh variables.
-- The first integer field permits something akin to pointer equality
-- but with less false negatives, because it's stable.
--
-- The r variable is existential, but operations that depends on it instance
-- are rarely called and relatively cheap, so no picking specializations
-- at runtime is needed.
type role ADShareD nominal
type ADShareD :: (Type -> Type) -> Type
data ADShareD d = ADShareNil
                | forall r. GoodScalar r
                  => ADShareCons Int AstVarId (d r) (ADShareD d)
deriving instance (forall r. GoodScalar r => Show (d r)) => Show (ADShareD d)

emptyADShare :: ADShareD d
emptyADShare = ADShareNil

insertADShare :: forall r d. GoodScalar r
              => AstVarId -> d r -> ADShareD d -> ADShareD d
insertADShare !key !t !s =
  -- The Maybe over-engineering ensures that we never refresh an id
  -- unnecessarily. In theory, when merging alternating equal lists
  -- with different ids, this improves runtime from quadratic to linear,
  -- but we apparently don't have such tests or they are too small,
  -- so this causes a couple percent overhead instead.
  let insertAD :: ADShareD d -> Maybe (ADShareD d)
      insertAD ADShareNil = Just $ ADShareCons (- fromEnum key) key t ADShareNil
      insertAD l2@(ADShareCons _id2 key2 t2 rest2) =
        case compare key key2 of
          EQ -> Nothing
                  -- the lists only ever grow and only in fresh/unique way,
                  -- so identical key means identical payload
          LT -> case insertAD rest2 of
            Nothing -> Nothing
            Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> Just $ freshInsertADShare key t l2
  in fromMaybe s (insertAD s)

freshInsertADShare :: GoodScalar r
                   => AstVarId -> d r -> ADShareD d -> ADShareD d
{-# NOINLINE freshInsertADShare #-}
freshInsertADShare !key !t !s = unsafePerformIO $ do
  id0 <- unsafeGetFreshId
  return $! ADShareCons id0 key t s

mergeADShare :: ADShareD d -> ADShareD d -> ADShareD d
mergeADShare !s1 !s2 =
  let mergeAD :: ADShareD d -> ADShareD d -> Maybe (ADShareD d)
      mergeAD ADShareNil ADShareNil = Nothing
      mergeAD l ADShareNil = Just l
      mergeAD ADShareNil l = Just l
      mergeAD l1@(ADShareCons id1 key1 t1 rest1)
              l2@(ADShareCons id2 key2 t2 rest2) =
        if id1 == id2
        then -- This assert is quadratic, so can only be enabled when debugging:
             -- assert (_lengthADShare l1 == _lengthADShare l2) $
             Nothing
               -- the lists only ever grow and only in fresh/unique way,
               -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> case mergeAD rest1 rest2 of
             Nothing -> Nothing
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          LT -> case mergeAD l1 rest2 of
             Nothing -> Just l2
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> case mergeAD rest1 l2 of
             Nothing -> Just l1
             Just l3 -> Just $ freshInsertADShare key1 t1 l3
  in fromMaybe s1 (mergeAD s1 s2)

-- The result type is not as expected. The result is as if assocsADShare
-- was applied to the expected one.
subtractADShare :: ADShareD d -> ADShareD d -> AstBindingsD d
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShareD d -> ADShareD d -> AstBindingsD d
      subAD !l ADShareNil = assocsADShare l
      subAD ADShareNil _ = []
      subAD l1@(ADShareCons id1 key1 t1 rest1)
            l2@(ADShareCons id2 key2 _ rest2) =
        if id1 == id2
        then []  -- the lists only ever grow and only in fresh/unique way,
                 -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> subAD rest1 rest2
          LT -> subAD l1 rest2
          GT -> (key1, DynamicExists t1) : subAD rest1 l2
  in subAD s1 s2

flattenADShare :: [ADShareD d] -> ADShareD d
flattenADShare = foldl' mergeADShare emptyADShare

assocsADShare :: ADShareD d -> AstBindingsD d
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) =
  (key, DynamicExists t) : assocsADShare rest

_lengthADShare :: Int -> ADShareD d -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest

varInADShare :: (forall r. AstVarId -> d r -> Bool)
                -> AstVarId -> ADShareD d
                -> Bool
{-# INLINE varInADShare #-}
varInADShare _ _ ADShareNil = False
varInADShare varInAstDynamic var (ADShareCons _ _ d rest) =
  varInAstDynamic var d || varInADShare varInAstDynamic var rest
    -- TODO: for good Core, probably a local recursive 'go' is needed

nullADShare :: ADShareD d -> Bool
{-# INLINE nullADShare #-}
nullADShare ADShareNil = True
nullADShare ADShareCons{} = False
