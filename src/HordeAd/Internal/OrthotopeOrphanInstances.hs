{-# LANGUAGE AllowAmbiguousTypes, CPP, UndecidableInstances,
             UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( -- * Definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat
    -- * Definitions for type-level list shapes
  , shapeT, shapeP, sizeT, sizeP
  , withShapeP, sameShape, matchingRank
  , lemShapeFromKnownShS, lemKnownNatRank
    -- * Numeric classes and instances for tensors
  , IntegralF(..), RealFloatF(..), FlipR(..), FlipS(..)
  , -- * Assorted orphans and additions
    PermC, trustMeThisIsAPermutation
  ) where

import Prelude

import           Control.DeepSeq (NFData)
import           Control.Exception.Assert.Sugar
import           Data.Array.Convert (Convert)
import qualified Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.Internal.ShapedG as SG
import qualified Data.Array.Internal.ShapedS as SS
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Int (Int64)
import           Data.Kind (Type)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.Stack
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , SNat
  , fromSNat
  , pattern SNat
  , sameNat
  , type (*)
  , type (+)
  , withSomeSNat
  )
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)
import           Numeric.LinearAlgebra.Devel (zipVectorWith)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Internal.Arith as Nested.Internal.Arith
import qualified Data.Array.Mixed.Permutation as Permutation
import qualified Data.Array.Mixed.Shape as X
import           Data.Array.Mixed.Types (Dict (..))
import qualified Data.Array.Mixed.Types as Mixed.Types
import           Data.Array.Nested (KnownShS (..), ShS (ZSS, (:$$)))
import qualified Data.Array.Nested as Nested
import qualified Data.Array.Nested.Internal.Mixed as Nested.Internal.Mixed
import qualified Data.Array.Nested.Internal.Ranked as Nested.Internal
import           Data.Array.Nested.Internal.Shape (shsOrthotopeShape, shsToList)
import qualified Data.Array.Nested.Internal.Shaped as Nested.Internal

-- * Definitions to help express and manipulate type-level natural numbers

withSNat :: Int -> (forall n. KnownNat n => (SNat n -> r)) -> r
withSNat i f = withSomeSNat (fromIntegral i) $ \msnat -> case msnat of
  Just snat@SNat -> f snat
  Nothing -> error "withSNat: negative argument"

sNatValue :: forall n. SNat n -> Int
{-# INLINE sNatValue #-}
sNatValue = fromInteger . fromSNat

proxyFromSNat :: SNat n -> Proxy n
proxyFromSNat SNat = Proxy


-- * Definitions for type-level list shapes

-- Below, copied with modification from ox-arrays.

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
sameShape = case shapeT @sh1 == shapeT @sh2 of
              True -> Just (unsafeCoerce Refl :: sh1 :~: sh2)
              False -> Nothing

matchingRank :: forall sh1 n2. (KnownShS sh1, KnownNat n2)
             => Maybe (X.Rank sh1 :~: n2)
matchingRank =
  if length (shapeT @sh1) == valueOf @n2
  then Just (unsafeCoerce Refl :: X.Rank sh1 :~: n2)
  else Nothing

lemShapeFromKnownShS :: forall sh. KnownShS sh
                       => Proxy sh -> Dict Sh.Shape sh
lemShapeFromKnownShS _ = shsOrthotopeShape (knownShS @sh)

lemKnownNatRank :: ShS sh -> Dict KnownNat (X.Rank sh)
lemKnownNatRank ZSS = Dict
lemKnownNatRank (_ :$$ sh) | Dict <- lemKnownNatRank sh = Dict


-- * Numeric classes and instances for tensors

class IntegralF a where
  quotF, remF :: a -> a -> a

instance IntegralF Int64 where
  quotF = quot
  remF = rem

instance (Nested.PrimElt r, Num (Vector r), Integral r, KnownNat n, Numeric r, Show r)
         => IntegralF (Nested.Ranked n r) where
  quotF = Nested.Internal.arithPromoteRanked2 (Nested.Internal.Mixed.mliftPrim2 quot)
  remF = Nested.Internal.arithPromoteRanked2 (Nested.Internal.Mixed.mliftPrim2 rem)

instance (Nested.PrimElt r, Num (Vector r), Integral r, KnownShS sh, Numeric r, Show r)
         => IntegralF (Nested.Shaped sh r) where
  quotF = Nested.Internal.arithPromoteShaped2 (Nested.Internal.Mixed.mliftPrim2 quot)
  remF = Nested.Internal.arithPromoteShaped2 (Nested.Internal.Mixed.mliftPrim2 rem)

class Floating a => RealFloatF a where
  atan2F :: a -> a -> a

instance (Nested.Internal.Arith.NumElt r, Nested.PrimElt r, RealFloat r, RealFloat (Vector r), Nested.Internal.Arith.FloatElt r, KnownNat n, Numeric r)
         => RealFloatF (Nested.Ranked n r) where
  atan2F = Nested.Internal.arithPromoteRanked2 (Nested.Internal.Mixed.mliftPrim2 atan2)

instance (Nested.Internal.Arith.NumElt r, Nested.PrimElt r, RealFloat r, RealFloat (Vector r), Nested.Internal.Arith.FloatElt r, KnownShS sh, Numeric r)
         => RealFloatF (Nested.Shaped sh r) where
  atan2F = Nested.Internal.arithPromoteShaped2 (Nested.Internal.Mixed.mliftPrim2 atan2)

type role FlipR nominal nominal nominal
type FlipR :: forall {k}. (Nat -> k -> Type) -> k -> Nat -> Type
newtype FlipR p a (b :: Nat) = FlipR { runFlipR :: p b a }

instance (Show r, VS.Storable r, KnownNat n)
         => Show (FlipR OR.Array r n) where
  showsPrec :: Int -> FlipR OR.Array r n -> ShowS
  showsPrec d (FlipR u) =
    showString "Flip " . showParen True (showsPrec d u)

instance (Nested.Elt r, Show r, Show (Nested.Mixed (Mixed.Types.Replicate n Nothing) r))
         => Show (FlipR Nested.Ranked r n) where
  showsPrec :: Int -> FlipR Nested.Ranked r n -> ShowS
  showsPrec d (FlipR u) =
    showString "Flip " . showParen True (showsPrec d u)

instance (Eq r, Numeric r, KnownNat n, Eq (Nested.Mixed (Mixed.Types.Replicate n Nothing) r)) => Eq (FlipR Nested.Ranked r n) where
  (==) :: FlipR Nested.Ranked r n -> FlipR Nested.Ranked r n -> Bool
  FlipR u == FlipR v = u == v

instance (Ord r, Numeric r, KnownNat n, Eq (Nested.Mixed (Mixed.Types.Replicate n Nothing) r), Ord (Nested.Mixed (Mixed.Types.Replicate n Nothing) r)) => Ord (FlipR Nested.Ranked r n) where
  FlipR u <= FlipR v = u <= v

deriving instance Num (f a b) => Num (FlipR f b a)

deriving instance Enum (f a b) => Enum (FlipR f b a)

deriving instance IntegralF (f a b) => IntegralF (FlipR f b a)

deriving instance (Integral (f a b), Ord (FlipR f b a)) => Integral (FlipR f b a)

deriving instance Fractional (f a b) => Fractional (FlipR f b a)

deriving instance Floating (f a b) => Floating (FlipR f b a)

deriving instance (Real (f a b), Ord (FlipR f b a)) => Real (FlipR f b a)

deriving instance (RealFrac (f a b), Ord (FlipR f b a)) => RealFrac (FlipR f b a)

deriving instance RealFloatF (f a b) => RealFloatF (FlipR f b a)

deriving instance (RealFloat (f a b), Ord (FlipR f b a)) => RealFloat (FlipR f b a)

deriving instance NFData (f a b) => NFData (FlipR f b a)

type role FlipS nominal nominal nominal
type FlipS :: forall {k}. ([Nat] -> k -> Type) -> k -> [Nat] -> Type
newtype FlipS p a (b :: [Nat]) = FlipS { runFlipS :: p b a }

instance (Show r, VS.Storable r, KnownShS sh)
         => Show (FlipS OS.Array r sh) where
  showsPrec :: Int -> FlipS OS.Array r sh -> ShowS
  showsPrec d (FlipS u) | Dict <- lemShapeFromKnownShS (Proxy @sh) =
    showString "FlipS " . showParen True (showsPrec d u)

instance (Nested.Elt r, Show r, Show (Nested.Mixed (Mixed.Types.MapJust sh) r))
         => Show (FlipS Nested.Shaped r sh) where
  showsPrec :: Int -> FlipS Nested.Shaped r sh -> ShowS
  showsPrec d (FlipS u) =
    showString "FlipS " . showParen True (showsPrec d u)

instance (Eq r, Numeric r, KnownShS sh, Eq (Nested.Mixed (Mixed.Types.MapJust sh) r)) => Eq (FlipS Nested.Shaped r sh) where
  (==) :: FlipS Nested.Shaped r sh -> FlipS Nested.Shaped r sh -> Bool
  FlipS u == FlipS v = u == v

instance (Ord r, Numeric r, KnownShS sh, Eq (Nested.Mixed (Mixed.Types.MapJust sh) r), Ord (Nested.Mixed (Mixed.Types.MapJust sh) r)) => Ord (FlipS Nested.Shaped r sh) where
  FlipS u <= FlipS v = u <= v

deriving instance Num (f a b) => Num (FlipS f b a)

deriving instance IntegralF (f a b) => IntegralF (FlipS f b a)

deriving instance Fractional (f a b) => Fractional (FlipS f b a)

deriving instance Floating (f a b) => Floating (FlipS f b a)

deriving instance RealFloatF (f a b) => RealFloatF (FlipS f b a)

deriving instance NFData (f a b) => NFData (FlipS f b a)

-- TODO: This one is for convenience in tests only. Overhaul tests and remove.
instance (Num (Vector r), KnownNat n, Numeric r, Show r)
         => Num (OR.Array n r) where
  (+) = undefined
  (-) = undefined
  (*) = undefined
  negate = OR.mapA negate
  abs = undefined
  signum = undefined
  fromInteger = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.constant [] . fromInteger
    Nothing -> error $ "OR.fromInteger: shape unknown at rank "
                       ++ show (valueOf @n :: Int)

-- TODO: This one is for convenience in tests only. Overhaul tests and remove.
instance (Num (Vector r), KnownNat n, Numeric r, Show r, Fractional r)
         => Fractional (OR.Array n r) where
  (/) = undefined
  recip = undefined
  fromRational = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.constant [] . fromRational
    Nothing -> error $ "OR.fromRational: shape unknown at rank "
                       ++ show (valueOf @n :: Int)


-- * Assorted orphans and additions

-- TODO: move to separate orphan module(s) at some point

instance (Sh.Shape sh, X.Rank sh ~ n)
         => Convert (OS.Array sh a) (OR.Array n a) where
  convert (SS.A a@(SG.A t)) = RS.A (RG.A (SG.shapeL a) t)

type family MapSucc (xs :: [Nat]) :: [Nat] where
  MapSucc '[] = '[]
  MapSucc (x ': xs) = 1 + x ': MapSucc xs

class Permutation.IsPermutation is => PermC is
instance Permutation.IsPermutation is => PermC is

trustMeThisIsAPermutationDict :: forall is. Dict PermC is
trustMeThisIsAPermutationDict = unsafeCoerce (Dict :: Dict PermC '[])

trustMeThisIsAPermutation :: forall is r. (PermC is => r) -> r
trustMeThisIsAPermutation r = case trustMeThisIsAPermutationDict @is of
  Dict -> r

instance Enum (Vector r) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Num (Vector r), Integral r, Numeric r, Show r)
         => Integral (Vector r) where
  quot = zipVectorWith quot
  rem = zipVectorWith rem
  quotRem x y = (quot x y, rem x y)  -- TODO
  div = zipVectorWith div
  mod = zipVectorWith mod
  -- divMod  -- TODO
  toInteger = undefined  -- not needed

instance (Num (Vector r), Numeric r, Ord r)
         => Real (Vector r) where
  toRational = undefined  -- TODO

instance (Num (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (Vector r) where
  properFraction = error "Vector.properFraction: can't be implemented"

instance (Floating (Vector r), Numeric r, RealFloat r)
         => RealFloat (Vector r) where
  atan2 = arctan2
  floatRadix = undefined  -- TODO (and below)
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined
