{-# LANGUAGE AllowAmbiguousTypes, ImpredicativeTypes, UndecidableInstances,
             UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Some fundamental type families and types.
module HordeAd.Core.Types
  ( -- * Definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat
    -- * Definitions for type-level list shapes
  , ShS(..), KnownShS(..)
  , sshapeKnown, slistKnown, sixKnown, knownShR
  , shapeT, shapeP, sizeT, sizeP
  , withShapeP, sameShape, matchingRank, lemKnownNatRank
  , Dict(..), PermC, trustMeThisIsAPermutation
    -- * Kinds of the functors that determine the structure of a tensor type
  , TensorType, RankedTensorType, ShapedTensorType, MixedTensorType
  , TensorKindType (..), STensorKindType(..), TensorKind(..)
  , lemTensorKindOfS, sameTensorKind, sameTK
  , BuildTensorKind, lemTensorKindOfBuild
    -- * Some fundamental constraints
  , GoodScalar, HasSingletonDict, Differentiable, IfDifferentiable(..)
  , ADTensorKind, lemTensorKindOfAD, lemBuildOfAD
    -- * Type families that tensors will belong to
  , IntOf, RankedOf, ShapedOf, MixedOf
  , HFunOf, PrimalOf, DualOf, ShareOf
  , DummyDual(..)
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..)
  , IfF(..), EqF(..), OrdF(..), minF, maxF
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Array.Internal (valueOf)
import Data.Boolean (Boolean (..))
import Data.Int (Int64)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import GHC.TypeLits
  (KnownNat, Nat, SNat, fromSNat, pattern SNat, type (+), withSomeSNat)
import Type.Reflection (TypeRep, Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (KnownShX (..), StaticShX (..))
import Data.Array.Mixed.Types (Dict (..), unsafeCoerceRefl)
import Data.Array.Nested
  (IxS (..), KnownShS (..), ListS (..), Rank, ShR (..), ShS (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shsToList)

-- * Definitions to help express and manipulate type-level natural numbers

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
withSNat i f = withSomeSNat (fromIntegral i) $ \case
  Just snat@SNat -> f snat
  Nothing -> error "withSNat: negative argument"

sNatValue :: forall n. SNat n -> Int
{-# INLINE sNatValue #-}
sNatValue = fromInteger . fromSNat

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy

-- * Definitions for type-level list shapes

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

shapeT :: forall sh. KnownShS sh => [Int]
shapeT = shsToList (knownShS @sh)

shapeP :: forall sh. KnownShS sh => Proxy sh -> [Int]
shapeP _ = shsToList (knownShS @sh)

sizeT :: forall sh. KnownShS sh => Int
sizeT = product $ shapeT @sh

sizeP :: forall sh. KnownShS sh => Proxy sh -> Int
sizeP _ = sizeT @sh

withShapeP :: [Int] -> (forall sh. KnownShS sh => Proxy sh -> r) -> r
withShapeP [] f = f (Proxy @('[] :: [Nat]))
withShapeP (n : ns) f = withSNat n $ \(SNat @n) ->
  withShapeP ns (\(Proxy @ns) -> f (Proxy @(n : ns)))

sameShape :: forall sh1 sh2. (KnownShS sh1, KnownShS sh2)
          => Maybe (sh1 :~: sh2)
sameShape = if shapeT @sh1 == shapeT @sh2
            then Just (unsafeCoerce Refl :: sh1 :~: sh2)
            else Nothing

matchingRank :: forall sh1 n2. (KnownShS sh1, KnownNat n2)
             => Maybe (Rank sh1 :~: n2)
matchingRank =
  if length (shapeT @sh1) == valueOf @n2
  then Just (unsafeCoerce Refl :: Rank sh1 :~: n2)
  else Nothing

lemKnownNatRank :: ShS sh -> Dict KnownNat (Rank sh)
lemKnownNatRank ZSS = Dict
lemKnownNatRank (_ :$$ sh) | Dict <- lemKnownNatRank sh = Dict

class Permutation.IsPermutation is => PermC is
instance Permutation.IsPermutation is => PermC is

trustMeThisIsAPermutationDict :: forall is. Dict PermC is
trustMeThisIsAPermutationDict = unsafeCoerce (Dict :: Dict PermC '[])

trustMeThisIsAPermutation :: forall is r. (PermC is => r) -> r
trustMeThisIsAPermutation r = case trustMeThisIsAPermutationDict @is of
  Dict -> r


-- * Types of types of tensors

type TensorType ty = Type -> ty -> Type

type RankedTensorType = TensorType Nat

type ShapedTensorType = TensorType [Nat]

type MixedTensorType = TensorType [Maybe Nat]

type GoodScalarConstraint r =
  ( Show r, Ord r, Num r, Typeable r, IfDifferentiable r
  , NFData r, Nested.PrimElt r, Nested.Elt r, Nested.NumElt r
  , forall sh. Show (Nested.Mixed sh r), forall sh. Eq (Nested.Mixed sh r)
  , forall sh. NFData (Nested.Mixed sh r), forall sh. Ord (Nested.Mixed sh r) )

type data TensorKindType =
    TKR Type Nat
  | TKS Type [Nat]
  | TKX Type [Maybe Nat]
  | TKProduct TensorKindType TensorKindType
  | TKUnit
  | TKUntyped

type role STensorKindType nominal
data STensorKindType y where
  STKR :: (GoodScalar r, KnownNat n)
       => TypeRep r -> SNat n -> STensorKindType (TKR r n)
  STKS :: (GoodScalar r, KnownShS sh)
       => TypeRep r -> ShS sh -> STensorKindType (TKS r sh)
  STKX :: (GoodScalar r, KnownShX sh)
       => TypeRep r -> StaticShX sh -> STensorKindType (TKX r sh)
  STKProduct :: (TensorKind y, TensorKind z)
             => STensorKindType y -> STensorKindType z
             -> STensorKindType (TKProduct y z)
  STKUnit :: STensorKindType TKUnit
  STKUntyped :: STensorKindType TKUntyped

deriving instance Show (STensorKindType y)

class TensorKind (y :: TensorKindType) where
  stensorKind :: STensorKindType y

instance (GoodScalar r, KnownNat n) => TensorKind (TKR r n) where
  stensorKind = STKR typeRep SNat

instance (GoodScalar r, KnownShS sh) => TensorKind (TKS r sh) where
  stensorKind = STKS typeRep knownShS

instance (GoodScalar r, KnownShX sh) => TensorKind (TKX r sh) where
  stensorKind = STKX typeRep knownShX

instance (TensorKind y, TensorKind z) => TensorKind (TKProduct y z) where
  stensorKind = STKProduct (stensorKind @y) (stensorKind @z)

instance TensorKind TKUnit where
  stensorKind = STKUnit

instance TensorKind TKUntyped where
  stensorKind = STKUntyped

lemTensorKindOfS :: STensorKindType y -> Dict TensorKind y
lemTensorKindOfS = \case
  STKR{} -> Dict
  STKS{} -> Dict
  STKX{} -> Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 -> Dict
  STKUnit -> Dict
  STKUntyped -> Dict

sameTensorKind :: forall y1 y2. (TensorKind y1, TensorKind y2) => Maybe (y1 :~: y2)
sameTensorKind = sameTK (stensorKind @y1) (stensorKind @y2)

sameTK :: STensorKindType y1' -> STensorKindType y2' -> Maybe (y1' :~: y2')
sameTK y1 y2 = case (y1, y2) of
    (STKR r1 snat1, STKR r2 snat2) ->
      case (testEquality r1 r2, testEquality snat1 snat2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKS r1 shs1, STKS r2 shs2) ->
      case (testEquality r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKX r1 shs1, STKX r2 shs2) ->
      case (testEquality r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKProduct x1 z1, STKProduct x2 z2) -> case (sameTK x1 x2, sameTK z1 z2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
    (STKUnit, STKUnit) -> Just Refl
    (STKUntyped, STKUntyped) -> Just Refl
    _ -> Nothing

type family BuildTensorKind k tk where
  BuildTensorKind k (TKR r n) = TKR r (1 + n)
  BuildTensorKind k (TKS r sh) = TKS r (k : sh)
  BuildTensorKind k (TKX r sh) = TKX r (Just k : sh)
  BuildTensorKind k (TKProduct y z) =
    TKProduct (BuildTensorKind k y) (BuildTensorKind k z)
  BuildTensorKind k TKUnit = TKUnit
  BuildTensorKind k TKUntyped = TKUntyped

lemTensorKindOfBuild :: SNat k -> STensorKindType y
                     -> Dict TensorKind (BuildTensorKind k y)
lemTensorKindOfBuild snat@SNat = \case
  STKR{} -> Dict
  STKS{} -> Dict
  STKX{} -> Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfBuild snat stk1
                       , Dict <- lemTensorKindOfBuild snat stk2 -> Dict
  STKUnit -> Dict
  STKUntyped -> Dict


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
  HasSingletonDict sh = KnownShX sh

type Differentiable r =
  (RealFloat r, Nested.FloatElt r)

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

type family ADTensorKind tk where
  ADTensorKind (TKR Double n) = TKR Double n
  ADTensorKind (TKR Float n) = TKR Float n
  ADTensorKind (TKR r n) = TKUnit
  ADTensorKind (TKS Double sh) = TKS Double sh
  ADTensorKind (TKS Float sh) = TKS Float sh
  ADTensorKind (TKS r sh) = TKUnit
  ADTensorKind (TKX Double sh) = TKX Double sh
  ADTensorKind (TKX Float sh) = TKX Float sh
  ADTensorKind (TKX r sh) = TKUnit
  ADTensorKind (TKProduct y z) =
    TKProduct (ADTensorKind y) (ADTensorKind z)
  ADTensorKind TKUnit = TKUnit
  ADTensorKind TKUntyped = TKUntyped
    -- TODO (unlikely): also affect the inside of HVectors

lemTensorKindOfAD :: forall y.
                     STensorKindType y
                  -> Dict TensorKind (ADTensorKind y)
lemTensorKindOfAD = \case
  STKR @r _ _ -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> Dict
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> Dict
      _ -> unsafeCoerce (Dict @TensorKind @TKUnit)
  STKS @r _ _ ->  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> Dict
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> Dict
      _ -> unsafeCoerce (Dict @TensorKind @TKUnit)
  STKX @r _ _ ->  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> Dict
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> Dict
      _ -> unsafeCoerce (Dict @TensorKind @TKUnit)
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfAD stk1
                       , Dict <- lemTensorKindOfAD stk2 -> Dict
  STKUnit -> Dict
  STKUntyped -> Dict

lemBuildOfAD :: forall k y.
                SNat k -> STensorKindType y
             -> Maybe (BuildTensorKind k (ADTensorKind y)
                       :~: ADTensorKind (BuildTensorKind k y))
lemBuildOfAD snat@SNat = \case
  STKR{} -> Just unsafeCoerceRefl
  STKS{} -> Just unsafeCoerceRefl
  STKX{} -> Just unsafeCoerceRefl
  STKProduct stk1 stk2 ->
    case (lemBuildOfAD snat stk1, lemBuildOfAD snat stk2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  STKUnit -> Just Refl
  STKUntyped -> Just Refl


-- * Type families that tensors will belong to

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: TensorType ty) = RankedOf (PrimalOf f) Int64 0

-- ty is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family RankedOf (f :: TensorType ty) :: RankedTensorType

type family ShapedOf (f :: RankedTensorType) = (result :: ShapedTensorType)
  | result -> f

type family MixedOf (f :: RankedTensorType) = (result :: MixedTensorType)
  | result -> f

-- | The type family is defined in order to give a special instance
-- for AST that preservs sharing and, even more importantly, keeps
-- the computation of dervative functions lazy. See the definition
-- of 'AstLambda' and the code that processes it, maintaining laziness.
--
-- The type family can't easily be made injective, because the @ADVal f@
-- instance is independent of @f@.
type family HFunOf (f :: RankedTensorType)
                   (x :: TensorKindType) (z :: TensorKindType) :: Type

type family PrimalOf (f :: TensorType ty) :: TensorType ty

type family DualOf (f :: TensorType ty) :: TensorType ty

type role DummyDual representational nominal
type DummyDual :: TensorType ty
data DummyDual r (y :: ty) = DummyDual

type instance RankedOf DummyDual = DummyDual
type instance ShapedOf DummyDual = DummyDual
type instance MixedOf DummyDual = DummyDual

type family ShareOf (f :: RankedTensorType) :: RankedTensorType


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
