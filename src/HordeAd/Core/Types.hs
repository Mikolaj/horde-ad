{-# LANGUAGE AllowAmbiguousTypes, DerivingVia, ImpredicativeTypes,
             UndecidableInstances, UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Some fundamental type families and types.
module HordeAd.Core.Types
  ( -- * Definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat, valueOf
    -- * Definitions for type-level list shapes
  , withKnownShS, withKnownShX
  , sshapeKnown, slistKnown, sixKnown, knownShR
  , shapeT, shapeP, sizeT, sizeP
  , withShapeP, sameShape, matchingRank, lemKnownNatRank
  , Dict(..), PermC, trustMeThisIsAPermutation
  , Take, Drop, Last, Init
    -- * Kinds of the functors that determine the structure of a tensor type
  , Target, TensorKindType (..), TKR, TKS, TKX, TKUnit
  , STensorKindType(..), TensorKind(..)
  , lemTensorKindOfS, sameTensorKind, sameTK
  , BuildTensorKind, lemTensorKindOfBuild
    -- * Some fundamental constraints
  , GoodScalar, HasSingletonDict, Differentiable, IfDifferentiable(..)
  , ADTensorKind, ADTensorScalar, Z0(..), lemTensorKindOfAD, lemBuildOfAD
    -- * Type families that tensors will belong to
  , IntOf, HFunOf, PrimalOf, DualOf, ShareOf
  , DummyDualTarget(..)
  , IxROf, IxSOf, IxXOf
    -- * Generic types of booleans and related class definitions
  , BoolOf, Boolean(..)
  , IfF(..), EqF(..), OrdF(..), minF, maxF
    -- * Misc
  , IntegralF(..), RealFloatF(..)
  ) where

import Prelude

import Control.DeepSeq (NFData (..))
import Data.Array.Internal.RankedS qualified as RS
import Data.Boolean (Boolean (..))
import Data.Int (Int64)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Storable qualified as V
import Foreign.C (CInt)
import Foreign.Storable (Storable (..))
import GHC.Generics (Generic)
import GHC.TypeLits
  ( KnownNat
  , Nat
  , SNat
  , fromSNat
  , pattern SNat
  , type (+)
  , type (-)
  , withSomeSNat
  )
import Type.Reflection (TypeRep, Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Internal.Arith (NumElt (..))
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (KnownShX (..), StaticShX (..), withKnownShX)
import Data.Array.Mixed.Types (Dict (..), unsafeCoerceRefl)
import Data.Array.Nested
  (IxR, IxS (..), IxX, KnownShS (..), ListS (..), Rank, ShR (..), ShS (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Shape (shsToList, withKnownShS)

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

{-# INLINE valueOf #-}
valueOf :: forall n r. (KnownNat n, Num r) => r
valueOf = fromInteger $ fromSNat (SNat @n)


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

type family Take (n :: Nat) (xs :: [k]) :: [k] where
    Take 0 xs = '[]
    Take n (x ': xs) = x ': Take (n - 1) xs

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
    Drop 0 xs = xs
    Drop n (x ': xs) = Drop (n - 1) xs

type family Last (xs :: [k]) where
  Last '[x] = x
  Last (x ': xs) = Last xs

type family Init (xs :: [k]) where
  Init '[x] = '[]
  Init (x ': xs) = x ': Init xs


-- * Types of types of tensors

type Target = TensorKindType -> Type

type GoodScalarConstraint r =
  ( Show r, Ord r, Num r, Typeable r, IfDifferentiable r
  , NFData r, Nested.PrimElt r, Nested.KnownElt r, Nested.NumElt r
  , forall sh. Show (Nested.Mixed sh r), forall sh. Eq (Nested.Mixed sh r)
  , forall sh. NFData (Nested.Mixed sh r), forall sh. Ord (Nested.Mixed sh r) )

type data TensorKindType =
    TKScalar Type
  | TKR2 Nat TensorKindType
  | TKS2 [Nat] TensorKindType
  | TKX2 [Maybe Nat] TensorKindType
  | TKProduct TensorKindType TensorKindType
  | TKUntyped

type TKR n r = TKR2 n (TKScalar r)
type TKS sh r = TKS2 sh (TKScalar r)
type TKX sh r = TKX2 sh (TKScalar r)

type TKUnit = TKScalar Z0

type role STensorKindType nominal
data STensorKindType y where
  STKScalar :: GoodScalar r
            => TypeRep r -> STensorKindType (TKScalar r)
  STKR :: SNat n -> STensorKindType x -> STensorKindType (TKR2 n x)
  STKS :: ShS sh -> STensorKindType x -> STensorKindType (TKS2 sh x)
  STKX :: StaticShX sh -> STensorKindType x -> STensorKindType (TKX2 sh x)
  STKProduct :: STensorKindType y -> STensorKindType z
             -> STensorKindType (TKProduct y z)
  STKUntyped :: STensorKindType TKUntyped

deriving instance Show (STensorKindType y)

class TensorKind (y :: TensorKindType) where
  stensorKind :: STensorKindType y

instance GoodScalar r => TensorKind (TKScalar r) where
  stensorKind = STKScalar typeRep

instance (TensorKind x, KnownNat n) => TensorKind (TKR2 n x) where
  stensorKind = STKR SNat stensorKind

instance (TensorKind x, KnownShS sh) => TensorKind (TKS2 sh x) where
  stensorKind = STKS knownShS stensorKind

instance (TensorKind x, KnownShX sh) => TensorKind (TKX2 sh x) where
  stensorKind = STKX knownShX stensorKind

instance (TensorKind y, TensorKind z) => TensorKind (TKProduct y z) where
  stensorKind = STKProduct (stensorKind @y) (stensorKind @z)

instance TensorKind TKUntyped where
  stensorKind = STKUntyped

lemTensorKindOfS :: STensorKindType y -> Dict TensorKind y
lemTensorKindOfS = \case
  STKScalar _ -> Dict
  STKR SNat x -> case lemTensorKindOfS x of
    Dict -> Dict
  STKS sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShS sh Dict
  STKX sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 -> Dict
  STKUntyped -> Dict

sameTensorKind :: forall y1 y2. (TensorKind y1, TensorKind y2) => Maybe (y1 :~: y2)
sameTensorKind = sameTK (stensorKind @y1) (stensorKind @y2)

sameTK :: STensorKindType y1' -> STensorKindType y2' -> Maybe (y1' :~: y2')
sameTK y1 y2 = case (y1, y2) of
    (STKScalar r1, STKScalar r2) ->
      case testEquality r1 r2 of
        Just Refl -> Just Refl
        Nothing -> Nothing
    (STKR snat1 r1, STKR snat2 r2) ->
      case (sameTK r1 r2, testEquality snat1 snat2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKS shs1 r1, STKS shs2 r2) ->
      case (sameTK r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKX shs1 r1, STKX shs2 r2) ->
      case (sameTK r1 r2, testEquality shs1 shs2) of
        (Just Refl, Just Refl) -> Just Refl
        _ -> Nothing
    (STKProduct x1 z1, STKProduct x2 z2) -> case (sameTK x1 x2, sameTK z1 z2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
    (STKUntyped, STKUntyped) -> Just Refl
    _ -> Nothing

type family BuildTensorKind k tk where
  BuildTensorKind k (TKR2 n r) = TKR2 (1 + n) r
  BuildTensorKind k (TKS2 sh r) = TKS2 (k : sh) r
  BuildTensorKind k (TKX2 sh r) = TKX2 (Just k : sh) r
  BuildTensorKind k (TKProduct y z) =
    TKProduct (BuildTensorKind k y) (BuildTensorKind k z)
  BuildTensorKind k TKUntyped = TKUntyped

lemTensorKindOfBuild :: SNat k -> STensorKindType y
                     -> Dict TensorKind (BuildTensorKind k y)
lemTensorKindOfBuild snat@SNat = \case
  STKScalar{} ->
    error "lemTensorKindOfBuild: type family BuildTensorKind stuck at TKScalar"
  STKR SNat x -> case lemTensorKindOfS x of
    Dict -> Dict
  STKS sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShS sh Dict
  STKX sh x -> case lemTensorKindOfS x of
    Dict -> withKnownShX sh Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfBuild snat stk1
                       , Dict <- lemTensorKindOfBuild snat stk2 -> Dict
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
  ADTensorKind (TKScalar r) = TKScalar (ADTensorScalar r)
  ADTensorKind (TKR2 n r) = TKR2 n (ADTensorKind r)
  ADTensorKind (TKS2 sh r) = TKS2 sh (ADTensorKind r)
  ADTensorKind (TKX2 sh r) = TKX2 sh (ADTensorKind r)
  ADTensorKind (TKProduct y z) =
    TKProduct (ADTensorKind y) (ADTensorKind z)
  ADTensorKind TKUntyped = TKUntyped
    -- TODO (unlikely): also affect the inside of HVectors

type family ADTensorScalar r where
  ADTensorScalar Double = Double
  ADTensorScalar Float = Float
  ADTensorScalar t = Z0

data Z0 = Z0
 deriving (Eq, Ord, Show)

instance NFData Z0 where
  rnf Z0 = ()

instance Storable Z0 where
  sizeOf _ = 0
  alignment _ = 1
  peek _ = return Z0
  poke _ _ = return ()

instance Num Z0 where
  Z0 + Z0 = Z0
  Z0 * Z0 = Z0
  negate Z0 = Z0
  abs Z0 = Z0
  signum Z0 = Z0
  fromInteger _ = Z0

instance Nested.PrimElt Z0
newtype instance Nested.Internal.Mixed.Mixed sh Z0 = M_NilZ0 (Nested.Internal.Mixed.Mixed sh (Nested.Internal.Mixed.Primitive Z0)) deriving (Eq, Generic) deriving (Show) via (Nested.Internal.Mixed.ShowViaPrimitive sh Z0)  -- no content, orthotope optimises this (via Vector)
deriving instance Ord (Nested.Mixed sh Z0)
instance NFData (Nested.Mixed sh Z0)
newtype instance Nested.Internal.Mixed.MixedVecs s sh Z0 = MV_NilZ0 (V.MVector s Z0)  -- no content, MVector optimises this
deriving via Nested.Primitive Z0 instance Nested.Elt Z0
deriving via Nested.Primitive Z0 instance Nested.KnownElt Z0

instance NumElt Z0 where
  numEltAdd _ arr1 _arr2 = arr1
  numEltSub _ arr1 _arr2 = arr1
  numEltMul _ arr1 _arr2 = arr1
  numEltNeg _ arr = arr
  numEltAbs _ arr = arr
  numEltSignum _ arr = arr
  numEltSum1Inner _ arr = RS.index arr 0
  numEltProduct1Inner _ arr = RS.index arr 0
  numEltSumFull _ _arr = Z0
  numEltProductFull _ _arr = Z0
  numEltMinIndex snat _arr = replicate (sNatValue snat) 0
  numEltMaxIndex snat _arr = replicate (sNatValue snat) 0
  numEltDotprodInner _ arr1 _arr2 = RS.index arr1 0

lemTensorKindOfAD :: forall y.
                     STensorKindType y
                  -> Dict TensorKind (ADTensorKind y)
lemTensorKindOfAD = \case
  STKScalar @r rep -> case testEquality rep (typeRep @Double) of
    Just Refl -> Dict
    _ -> case testEquality rep (typeRep @Float) of
      Just Refl -> Dict
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           Dict @TensorKind @(TKScalar Z0)
  STKR SNat rs -> case lemTensorKindOfAD rs of
    Dict -> Dict
  STKS sh rs -> withKnownShS sh $ case lemTensorKindOfAD rs of
    Dict -> Dict
  STKX sh rs -> withKnownShX sh $ case lemTensorKindOfAD rs of
    Dict -> Dict
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfAD stk1
                       , Dict <- lemTensorKindOfAD stk2 -> Dict
  STKUntyped -> Dict

lemBuildOfAD :: forall k y.
                SNat k -> STensorKindType y
             -> Maybe (BuildTensorKind k (ADTensorKind y)
                       :~: ADTensorKind (BuildTensorKind k y))
lemBuildOfAD snat@SNat = \case
  STKScalar{} -> Just unsafeCoerceRefl
  STKR{} -> Just unsafeCoerceRefl
  STKS{} -> Just unsafeCoerceRefl
  STKX{} -> Just unsafeCoerceRefl
  STKProduct stk1 stk2 ->
    case (lemBuildOfAD snat stk1, lemBuildOfAD snat stk2) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  STKUntyped -> Just Refl


-- * Type families that tensors will belong to

-- This is used only in indexing and similar contexts.
-- If used as size or shape, it would give more expressiveness,
-- but would lead to irregular tensors, especially after vectorization,
-- and would prevent statically known shapes.
type IntOf (f :: Target) = PrimalOf f (TKS '[] Int64)

-- | The type family is defined in order to give a special instance
-- for AST that preservs sharing and, even more importantly, keeps
-- the computation of dervative functions lazy. See the definition
-- of 'AstLambda' and the code that processes it, maintaining laziness.
--
-- The type family can't easily be made injective, because the @ADVal f@
-- instance is independent of @f@.
type family HFunOf (f :: Target)
                   (x :: TensorKindType) (z :: TensorKindType) :: Type

type family PrimalOf (f :: Target) :: Target

type family DualOf (f :: Target) :: Target

type family ShareOf (f :: Target) :: Target

type role DummyDualTarget representational
type DummyDualTarget :: Target
data DummyDualTarget y = DummyDualTarget

-- TODO: move this comment elsewhere?
-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :.: ZIR).
type IxROf (f :: Target) n = IxR n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IxSOf (f :: Target) (sh :: [Nat]) = IxS sh (IntOf f)

type IxXOf (f :: Target) (sh :: [Maybe Nat]) = IxX sh (IntOf f)


-- * Generic types of booleans and related class definitions

type family BoolOf (t :: Target) :: Type

class Boolean (BoolOf f) => IfF (f :: Target) where
  ifF :: TensorKind y => BoolOf f -> f y -> f y -> f y

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (==.), (/=.) :: TensorKind y => f y -> f y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: Target) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (<.), (<=.), (>.), (>=.) :: TensorKind y => f y -> f y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u

minF :: (IfF f, OrdF f, TensorKind y)
     => f y -> f y -> f y
minF u v = ifF (u <=. v) u v

maxF :: (IfF f, OrdF f, TensorKind y)
     => f y -> f y -> f y
maxF u v = ifF (u >=. v) u v


-- * Misc

class IntegralF a where
  quotF, remF :: a -> a -> a

instance IntegralF Int64 where
  quotF = quot
  remF = rem

instance IntegralF CInt where
  quotF = quot
  remF = rem

class Floating a => RealFloatF a where
  atan2F :: a -> a -> a

instance RealFloatF Float where
  atan2F = atan2

instance RealFloatF Double where
  atan2F = atan2

{- TODO: these would be better, but everything then overlaps with everything:
instance {-# OVERLAPPABLE #-} Integral r => IntegralF r where
  quotF = quot
  remF = rem

instance {-# OVERLAPPABLE #-} (Floating r, RealFloat r) => RealFloatF r where
  atan2F = atan2
-}
