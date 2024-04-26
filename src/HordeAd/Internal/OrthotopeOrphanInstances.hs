{-# LANGUAGE AllowAmbiguousTypes, CPP, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( -- * Definitions to help express and manipulate type-level natural numbers
    SNat, pattern SNat, withSNat, sNatValue, proxyFromSNat
    -- * Definitions for type-level list shapes
  , SShape(..), KnownShape2(..), KnownShape, shapeT, shapeP, sizeT, sizeP
  , withShapeP, sameShape, matchingRank, lemShapeFromKnownShape
  , Dict(..)
  , -- * Numeric instances for tensors
    liftVR, liftVR2, liftVS, liftVS2
  , IntegralF(..), RealFloatF(..)
  , -- * Assorted orphans and additions
    MapSucc, trustMeThisIsAPermutation
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
import           Data.Bifunctor.Flip
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.Stack
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , SNat
  , fromSNat
  , natSing
  , pattern SNat
  , sameNat
  , type (+)
  , withSomeSNat
  )
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)
import           Numeric.LinearAlgebra.Devel (zipVectorWith)
import           Unsafe.Coerce (unsafeCoerce)

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
  ShCons :: KnownShape sh => SNat n -> SShape sh -> SShape (n : sh)
-- TODO: re-add, if beneficial, when we drop GHC 9.6: deriving instance Eq (SShape sh)
deriving instance Show (SShape sh)
infixr 5 `ShCons`

-- | A statically-known shape of a shape-typed array.
class KnownShape2 sh where knownShape :: SShape sh
instance KnownShape2 '[] where knownShape = ShNil
instance (KnownNat n, KnownShape2 sh, Sh.Shape sh)
         => KnownShape2 (n : sh) where knownShape = ShCons natSing knownShape

type KnownShape sh = (KnownShape2 sh, Sh.Shape sh)

shapeT :: forall sh. KnownShape2 sh => [Int]
shapeT = sshapeToList (knownShape @sh)

shapeP :: forall sh. KnownShape2 sh => Proxy sh -> [Int]
shapeP _ = sshapeToList (knownShape @sh)

sshapeToList :: SShape sh -> [Int]
sshapeToList ShNil = []
sshapeToList (ShCons n l) = sNatValue n : sshapeToList l

sizeT :: forall sh. KnownShape2 sh => Int
sizeT = product $ shapeT @sh

sizeP :: forall sh. KnownShape2 sh => Proxy sh -> Int
sizeP _ = sizeT @sh

withShapeP :: [Int] -> (forall sh. KnownShape sh => Proxy sh -> r) -> r
withShapeP [] f = f (Proxy @('[] :: [Nat]))
withShapeP (n : ns) f = withSNat n $ \(SNat @n) ->
  withShapeP ns (\(Proxy @ns) -> f (Proxy @(n : ns)))

sameShape :: forall sh1 sh2. (KnownShape2 sh1, KnownShape2 sh2)
          => Maybe (sh1 :~: sh2)
sameShape = case shapeT @sh1 == shapeT @sh2 of
              True -> Just (unsafeCoerce Refl :: sh1 :~: sh2)
              False -> Nothing

matchingRank :: forall sh1 n2. (KnownShape2 sh1, KnownNat n2)
             => Maybe (Sh.Rank sh1 :~: n2)
matchingRank =
  if length (shapeT @sh1) == valueOf @n2
  then Just (unsafeCoerce Refl :: Sh.Rank sh1 :~: n2)
  else Nothing

-- | Evidence for the constraint @c a@.
type role Dict representational nominal
type Dict :: forall {k}. (k -> Constraint) -> k -> Type
data Dict c a where
  Dict :: c a => Dict c a

shapeFromSShape :: SShape sh -> Dict Sh.Shape sh
shapeFromSShape ShNil = Dict
shapeFromSShape (ShCons SNat sh) | Dict <- shapeFromSShape sh = Dict

lemShapeFromKnownShape :: forall sh. KnownShape2 sh
                       => Proxy sh -> Dict Sh.Shape sh
lemShapeFromKnownShape _ = shapeFromSShape (knownShape @sh)


-- * Numeric instances for tensors

liftVR
  :: (Numeric r1, Numeric r, KnownNat n)
  => (Vector r1 -> Vector r)
  -> OR.Array n r1 -> OR.Array n r
liftVR !op t@(RS.A (RG.A sh oit)) =
  if product sh >= V.length (OI.values oit)
  then RS.A $ RG.A sh $ oit {OI.values = op $ OI.values oit}
  else OR.fromVector sh $ op $ OR.toVector t
    -- avoids applying op to any vector element not in the tensor
    -- (or at least ensures the right asymptotic behaviour, IDK)

-- Inspired by OI.zipWithT.
liftVR2
  :: (Numeric r, Show r, KnownNat n)
  => (Vector r -> Vector r -> Vector r)
  -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2 !op t@(RS.A (RG.A sh oit@(OI.T sst _ vt)))
            u@(RS.A (RG.A shu oiu@(OI.T _ _ vu)))
        = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1 then it's a degenerate case.
      RS.A $ RG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, hmatrix should auto-expand to match second.
      if product sh >= V.length vu
      then RS.A $ RG.A sh $ oiu {OI.values = vt `op` vu}
      else OR.fromVector sh $ vt `op` OR.toVector u
    (_, 1) ->
      -- Second vector has length 1, hmatrix should auto-expand to match first.
      if product sh >= V.length vt
      then RS.A $ RG.A sh $ oit {OI.values = vt `op` vu}
      else OR.fromVector sh $ OR.toVector t `op` vu
    (_, _) ->
      if product sh >= V.length vt
         && product sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ RS.A $ RG.A sh $ oit {OI.values = vt `op` vu}
      else OR.fromVector sh $ OR.toVector t `op` OR.toVector u

liftVR2UnlessZero
  :: (Num (Vector r), Numeric r, Show r, KnownNat n, Eq r)
  => (Vector r -> Vector r -> Vector r)
  -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2UnlessZero op =
  liftVR2 (\x y -> if y == 0 then 0 else op x y)

-- For the operations where hmatrix can't adapt/expand scalars.
liftVR2NoAdapt
  :: (Numeric r, Show r, KnownNat n)
  => (Vector r -> Vector r -> Vector r)
  -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2NoAdapt !op t@(RS.A (RG.A sh oit@(OI.T sst _ vt)))
                   u@(RS.A (RG.A shu oiu@(OI.T _ _ vu)))
               = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1 then it's a degenerate case.
      -- Whether hmatrix can auto-expand doesn't matter here.
      RS.A $ RG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, but hmatrix can't auto-expand.
      if product sh >= V.length vu
      then RS.A $ RG.A sh
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OR.toVector u
           in OR.fromVector sh $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      -- Second vector has length 1, but hmatrix can't auto-expand.
      if product sh >= V.length vt
      then RS.A $ RG.A sh
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OR.toVector t
           in OR.fromVector sh $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) ->
      -- We don't special-case tensors that have same non-zero offsets, etc.,
      -- because the gains are small, correctness suspect (offsets can be
      -- larger than the vector length!) and we often apply op to sliced off
      -- elements, which defeats asymptotic guarantees.
      if product sh >= V.length vt
         && product sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ RS.A $ RG.A sh $ oit {OI.values = vt `op` vu}
      else OR.fromVector sh $ OR.toVector t `op` OR.toVector u
        -- avoids applying op to any vector element not in the tensor
        -- (or at least ensures the right asymptotic behaviour, IDK)

-- See the various comments above; we don't repeat them below.
liftVS
  :: forall sh r1 r. (Numeric r1, Numeric r, KnownShape2 sh)
  => (Vector r1 -> Vector r)
  -> OS.Array sh r1 -> OS.Array sh r
liftVS !op t@(SS.A (SG.A oit)) | Dict <- lemShapeFromKnownShape (Proxy @sh) =
  if sizeT @sh >= V.length (OI.values oit)
  then SS.A $ SG.A $ oit {OI.values = op $ OI.values oit}
  else OS.fromVector $ op $ OS.toVector t

liftVS2
  :: forall sh r. (Numeric r, KnownShape2 sh)
  => (Vector r -> Vector r -> Vector r)
  -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2 !op t@(SS.A (SG.A oit@(OI.T sst _ vt)))
            u@(SS.A (SG.A oiu@(OI.T _ _ vu)))
 | Dict <- lemShapeFromKnownShape (Proxy @sh) =
  case (V.length vt, V.length vu) of
    (1, 1) -> SS.A $ SG.A $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if sizeT @sh >= V.length vu
      then SS.A $ SG.A $ oiu {OI.values = vt `op` vu}
      else OS.fromVector $ vt `op` OS.toVector u
    (_, 1) ->
      if sizeT @sh >= V.length vt
      then SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` vu
    (_, _) ->
      if sizeT @sh >= V.length vt
         && sizeT @sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` OS.toVector u

liftVS2UnlessZero
  :: forall sh r. (Num (Vector r), Numeric r, KnownShape2 sh, Eq r)
  => (Vector r -> Vector r -> Vector r)
  -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2UnlessZero op
  | Dict <- lemShapeFromKnownShape (Proxy @sh) =
    liftVS2 (\x y -> if y == 0 then 0 else op x y)

liftVS2NoAdapt
  :: forall sh r. (Numeric r, KnownShape2 sh)
  => (Vector r -> Vector r -> Vector r)
  -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2NoAdapt !op t@(SS.A (SG.A oit@(OI.T sst _ vt)))
                   u@(SS.A (SG.A oiu@(OI.T _ _ vu)))
 | Dict <- lemShapeFromKnownShape (Proxy @sh)  =
  case (V.length vt, V.length vu) of
    (1, 1) -> SS.A $ SG.A $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if sizeT @sh >= V.length vu
      then SS.A $ SG.A
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OS.toVector u
           in OS.fromVector $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      if sizeT @sh >= V.length vt
      then SS.A $ SG.A
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OS.toVector t
           in OS.fromVector $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) ->
      if sizeT @sh >= V.length vt
         && sizeT @sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` OS.toVector u

-- These constraints force @UndecidableInstances@.
instance (Num (Vector r), KnownNat n, Numeric r, Show r)
         => Num (OR.Array n r) where
  -- TODO: more of an experiment than a real workaround:
  {-# SPECIALIZE instance KnownNat n => Num (OR.Array n Double) #-}
  (+) = liftVR2 (+)
  (-) = liftVR2 (-)
  (*) = liftVR2 (*)
  negate = liftVR negate
  abs = liftVR abs
  signum = liftVR signum
  fromInteger = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.constant [] . fromInteger
    Nothing -> error $ "OR.fromInteger: shape unknown at rank "
                       ++ show (valueOf @n :: Int)

instance (Num (Vector r), KnownShape2 sh, Numeric r) => Num (OS.Array sh r) where
  (+) = liftVS2 (+)
  (-) = liftVS2 (-)
  (*) = liftVS2 (*)
  negate = liftVS negate
  abs = liftVS abs
  signum = liftVS signum
  fromInteger | Dict <- lemShapeFromKnownShape (Proxy @sh) =
    OS.constant . fromInteger

instance Enum (OR.Array n r) where  -- dummy, to satisfy Integral below
  toEnum :: HasCallStack => Int -> a
  toEnum _ = error "toEnum: undefined for OR.Array"
  fromEnum :: HasCallStack => a -> Int
  fromEnum _ = error "fromEnum: undefined for OR.Array"

instance (Num (Vector r), Integral r, KnownNat n, Numeric r, Show r)
         => Integral (OR.Array n r) where
  quot = liftVR2UnlessZero quot
  rem = liftVR2UnlessZero rem
  quotRem x y = (quot x y, rem x y)  -- TODO, another variant of liftVR2 needed
  div = liftVR2UnlessZero div
  mod = liftVR2UnlessZero mod
  -- divMod  -- TODO
  toInteger = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> toInteger . OR.unScalar
    _ -> error $ "OR.toInteger: rank not zero: "
                 ++ show (valueOf @n :: Int)

class IntegralF a where
  quotF, remF :: a -> a -> a

instance (Num (Vector r), Integral r, KnownShape2 sh, Numeric r, Show r)
         => IntegralF (OS.Array sh r) where
  quotF = liftVS2UnlessZero quot
  remF = liftVS2UnlessZero rem

instance (Num (Vector r), KnownNat n, Numeric r, Show r, Fractional r)
         => Fractional (OR.Array n r) where
  (/) = liftVR2 (/)
  recip = liftVR recip
  fromRational = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.constant [] . fromRational
    Nothing -> error $ "OR.fromRational: shape unknown at rank "
                       ++ show (valueOf @n :: Int)

instance (Num (Vector r), KnownShape2 sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  (/) = liftVS2 (/)
  recip = liftVS recip
  fromRational | Dict <- lemShapeFromKnownShape (Proxy @sh) =
    OS.constant . fromRational

instance (Floating (Vector r), KnownNat n, Numeric r, Show r, Floating r)
         => Floating (OR.Array n r) where
  pi = OR.constant [] pi
  exp = liftVR exp
  log = liftVR log
  sqrt = liftVR sqrt
  (**) = liftVR2 (**)
  logBase = liftVR2 logBase
  sin = liftVR sin
  cos = liftVR cos
  tan = liftVR tan
  asin = liftVR asin
  acos = liftVR acos
  atan = liftVR atan
  sinh = liftVR sinh
  cosh = liftVR cosh
  tanh = liftVR tanh
  asinh = liftVR asinh
  acosh = liftVR acosh
  atanh = liftVR atanh

instance (Floating (Vector r), KnownShape2 sh, Numeric r, Floating r)
         => Floating (OS.Array sh r) where
  pi | Dict <- lemShapeFromKnownShape (Proxy @sh) = OS.constant pi
  exp = liftVS exp
  log = liftVS log
  sqrt = liftVS sqrt
  (**) = liftVS2 (**)
  logBase = liftVS2 logBase
  sin = liftVS sin
  cos = liftVS cos
  tan = liftVS tan
  asin = liftVS asin
  acos = liftVS acos
  atan = liftVS atan
  sinh = liftVS sinh
  cosh = liftVS cosh
  tanh = liftVS tanh
  asinh = liftVS asinh
  acosh = liftVS acosh
  atanh = liftVS atanh

instance (Real (Vector r), KnownNat n, Numeric r, Show r, Ord r)
         => Real (OR.Array n r) where
  toRational = undefined  -- TODO

instance ( RealFrac (Vector r), KnownNat n, Numeric r, Show r, Fractional r
         , Ord r )
         => RealFrac (OR.Array n r) where
  properFraction = error "OR.properFraction: can't be implemented"
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor even RealFracB from Boolean package).

instance ( RealFloat (Vector r), KnownNat n, Numeric r, Show r, Floating r
         , Ord r )
         => RealFloat (OR.Array n r) where
  atan2 = liftVR2NoAdapt atan2
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

class Floating a => RealFloatF a where
  atan2F :: a -> a -> a

instance (Floating r, RealFloat (Vector r), KnownShape2 sh, Numeric r)
         => RealFloatF (OS.Array sh r) where
  atan2F = liftVS2NoAdapt atan2

deriving instance Num (f a b) => Num (Flip f b a)

deriving instance Enum (f a b) => Enum (Flip f b a)

deriving instance IntegralF (f a b) => IntegralF (Flip f b a)

deriving instance Integral (f a b) => Integral (Flip f b a)

deriving instance Fractional (f a b) => Fractional (Flip f b a)

deriving instance Floating (f a b) => Floating (Flip f b a)

deriving instance Real (f a b) => Real (Flip f b a)

deriving instance RealFrac (f a b) => RealFrac (Flip f b a)

deriving instance RealFloatF (f a b) => RealFloatF (Flip f b a)

deriving instance RealFloat (f a b) => RealFloat (Flip f b a)

deriving instance NFData (f a b) => NFData (Flip f b a)


-- * Assorted orphans and additions

-- TODO: move to separate orphan module(s) at some point

instance (Sh.Shape sh, Sh.Rank sh ~ n)
         => Convert (OS.Array sh a) (OR.Array n a) where
  convert (SS.A a@(SG.A t)) = RS.A (RG.A (SG.shapeL a) t)

type family MapSucc (xs :: [Nat]) :: [Nat] where
  MapSucc '[] = '[]
  MapSucc (x ': xs) = 1 + x ': MapSucc xs

trustMeThisIsAPermutationDict :: forall is. Dict OS.Permutation is
trustMeThisIsAPermutationDict = unsafeCoerce (Dict :: Dict OS.Permutation '[])

trustMeThisIsAPermutation :: forall is r. (OS.Permutation is => r) -> r
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
