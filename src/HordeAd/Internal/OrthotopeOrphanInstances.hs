{-# LANGUAGE AllowAmbiguousTypes, CPP, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( liftVD, liftVD2, liftVR, liftVR2, liftVS, liftVS2
  , MapSucc, trustMeThisIsAPermutation, sameShape, matchingRank
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Convert (Convert)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.DynamicG as DG
import qualified Data.Array.Internal.DynamicS as DS
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.Internal.Shape as OS
import qualified Data.Array.Internal.ShapedG as SG
import qualified Data.Array.Internal.ShapedS as SS
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)
import           Numeric.LinearAlgebra.Devel (zipVectorWith)
import           Type.Reflection (eqTypeRep, typeRep, (:~~:) (HRefl))
import           Unsafe.Coerce (unsafeCoerce)

-- * Numeric instances for tensor

liftVD
  :: (Numeric r1, Numeric r)
  => (Vector r1 -> Vector r)
  -> OD.Array r1 -> OD.Array r
liftVD op t@(DS.A (DG.A sh oit)) =
  if product sh >= V.length (OI.values oit)
  then DS.A $ DG.A sh $ oit {OI.values = op $ OI.values oit}
  else OD.fromVector sh $ op $ OD.toVector t
    -- avoids applying op to any vector element not in the tensor
    -- (or at least ensures the right asymptotic behaviour, IDK)

-- Inspired by OI.zipWithT.
liftVD2
  :: (Numeric r, Show r)
  => (Vector r -> Vector r -> Vector r)
  -> OD.Array r -> OD.Array r -> OD.Array r
liftVD2 op t@(DS.A (DG.A sh oit@(OI.T sst _ vt)))
           u@(DS.A (DG.A shu oiu@(OI.T _ _ vu)))
        = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1 then it's a degenerate case.
      DS.A $ DG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, hmatrix should auto-expand to match second.
      if product sh >= V.length vu
      then DS.A $ DG.A sh $ oiu {OI.values = vt `op` vu}
      else OD.fromVector sh $ vt `op` OD.toVector u
    (_, 1) ->
      -- Second vector has length 1, hmatrix should auto-expand to match first.
      if product sh >= V.length vt
      then DS.A $ DG.A sh $ oit {OI.values = vt `op` vu}
      else OD.fromVector sh $ OD.toVector t `op` vu
    (_, _) ->
      if product sh >= V.length vt
         && product sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ DS.A $ DG.A sh $ oit {OI.values = vt `op` vu}
      else OD.fromVector sh $ OD.toVector t `op` OD.toVector u

-- For the operations where hmatrix can't adapt/expand scalars.
liftVD2NoAdapt
  :: (Numeric r, Show r)
  => (Vector r -> Vector r -> Vector r)
  -> OD.Array r -> OD.Array r -> OD.Array r
liftVD2NoAdapt op t@(DS.A (DG.A sh oit@(OI.T sst _ vt)))
                  u@(DS.A (DG.A shu oiu@(OI.T _ _ vu)))
               = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1 then it's a degenerate case.
      -- Whether hmatrix can auto-expand doesn't matter here.
      DS.A $ DG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, but hmatrix can't auto-expand.
      if product sh >= V.length vu
      then DS.A $ DG.A sh
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OD.toVector u
           in OD.fromVector sh $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      -- Second vector has length 1, but hmatrix can't auto-expand.
      if product sh >= V.length vt
      then DS.A $ DG.A sh
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OD.toVector t
           in OD.fromVector sh $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) ->
      -- We don't special-case tensors that have same non-zero offsets, etc.,
      -- because the gains are small, correctness suspect (offsets can be
      -- larger than the vector length!) and we often apply op to sliced off
      -- elements, which defeats asymptotic guarantees.
      if product sh >= V.length vt
         && product sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ DS.A $ DG.A sh $ oit {OI.values = vt `op` vu}
      else OD.fromVector sh $ OD.toVector t `op` OD.toVector u
        -- avoids applying op to any vector element not in the tensor
        -- (or at least ensures the right asymptotic behaviour, IDK)

-- See the various comments above; we don't repeat them below.
liftVR
  :: (Numeric r1, Numeric r, KnownNat n)
  => (Vector r1 -> Vector r)
  -> OR.Array n r1 -> OR.Array n r
liftVR op t@(RS.A (RG.A sh oit)) =
  if product sh >= V.length (OI.values oit)
  then RS.A $ RG.A sh $ oit {OI.values = op $ OI.values oit}
  else OR.fromVector sh $ op $ OR.toVector t

liftVR2
  :: (Numeric r, Show r, KnownNat n)
  => (Vector r -> Vector r -> Vector r)
  -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2 op t@(RS.A (RG.A sh oit@(OI.T sst _ vt)))
           u@(RS.A (RG.A shu oiu@(OI.T _ _ vu)))
        = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) -> RS.A $ RG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if product sh >= V.length vu
      then RS.A $ RG.A sh $ oiu {OI.values = vt `op` vu}
      else OR.fromVector sh $ vt `op` OR.toVector u
    (_, 1) ->
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

liftVR2NoAdapt
  :: (Numeric r, Show r, KnownNat n)
  => (Vector r -> Vector r -> Vector r)
  -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2NoAdapt op t@(RS.A (RG.A sh oit@(OI.T sst _ vt)))
                  u@(RS.A (RG.A shu oiu@(OI.T _ _ vu)))
               = assert (sh == shu `blame` (t, u)) $
  case (V.length vt, V.length vu) of
    (1, 1) -> RS.A $ RG.A sh $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if product sh >= V.length vu
      then RS.A $ RG.A sh
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OR.toVector u
           in OR.fromVector sh $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      if product sh >= V.length vt
      then RS.A $ RG.A sh
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OR.toVector t
           in OR.fromVector sh $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) ->
      if product sh >= V.length vt
         && product sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ RS.A $ RG.A sh $ oit {OI.values = vt `op` vu}
      else OR.fromVector sh $ OR.toVector t `op` OR.toVector u

liftVS
  :: forall sh r1 r. (Numeric r1, Numeric r, OS.Shape sh)
  => (Vector r1 -> Vector r)
  -> OS.Array sh r1 -> OS.Array sh r
liftVS op t@(SS.A (SG.A oit)) =
  if OS.sizeT @sh >= V.length (OI.values oit)
  then SS.A $ SG.A $ oit {OI.values = op $ OI.values oit}
  else OS.fromVector $ op $ OS.toVector t

liftVS2
  :: forall sh r. (Numeric r, OS.Shape sh)
  => (Vector r -> Vector r -> Vector r)
  -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2 op t@(SS.A (SG.A oit@(OI.T sst _ vt)))
           u@(SS.A (SG.A oiu@(OI.T _ _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) -> SS.A $ SG.A $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if OS.sizeT @sh >= V.length vu
      then SS.A $ SG.A $ oiu {OI.values = vt `op` vu}
      else OS.fromVector $ vt `op` OS.toVector u
    (_, 1) ->
      if OS.sizeT @sh >= V.length vt
      then SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` vu
    (_, _) ->
      if OS.sizeT @sh >= V.length vt
         && OS.sizeT @sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` OS.toVector u

liftVS2NoAdapt
  :: forall sh r. (Numeric r, OS.Shape sh)
  => (Vector r -> Vector r -> Vector r)
  -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2NoAdapt op t@(SS.A (SG.A oit@(OI.T sst _ vt)))
                  u@(SS.A (SG.A oiu@(OI.T _ _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) -> SS.A $ SG.A $ OI.T sst 0 $ vt `op` vu
    (1, _) ->
      if OS.sizeT @sh >= V.length vu
      then SS.A $ SG.A
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OS.toVector u
           in OS.fromVector $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      if OS.sizeT @sh >= V.length vt
      then SS.A $ SG.A
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OS.toVector t
           in OS.fromVector $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) ->
      if OS.sizeT @sh >= V.length vt
         && OS.sizeT @sh >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu && V.length vt == V.length vu)
           $ SS.A $ SG.A $ oit {OI.values = vt `op` vu}
      else OS.fromVector $ OS.toVector t `op` OS.toVector u

-- These constraints force @UndecidableInstances@.
instance (Num (Vector r), Numeric r, Show r) => Num (OD.Array r) where
  (+) = liftVD2 (+)
  (-) = liftVD2 (-)
  (*) = liftVD2 (*)
  negate = liftVD negate
  abs = liftVD abs
  signum = liftVD signum
  fromInteger = error "OD.fromInteger: shape unknown"

instance (Num (Vector r), KnownNat n, Numeric r, Show r)
         => Num (OR.Array n r) where
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

instance (Num (Vector r), OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  (+) = liftVS2 (+)
  (-) = liftVS2 (-)
  (*) = liftVS2 (*)
  negate = liftVS negate
  abs = liftVS abs
  signum = liftVS signum
  fromInteger = OS.constant . fromInteger

instance Enum (OR.Array n r) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Num (Vector r), Integral r, KnownNat n, Numeric r, Show r)
         => Integral (OR.Array n r) where
  quot = liftVR2 quot
  rem = liftVR2 rem
  quotRem x y = (quot x y, rem x y)  -- TODO, another variant of liftVR2 needed
  div = liftVR2 div
  mod = liftVR2 mod
  -- divMod  -- TODO
  toInteger = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> toInteger . OR.unScalar
    _ -> error $ "OR.toInteger: rank not zero: "
                 ++ show (valueOf @n :: Int)

instance Enum (OS.Array sh r) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Num (Vector r), Integral r, OS.Shape sh, Numeric r, Show r)
         => Integral (OS.Array sh r) where
  quot = liftVS2 quot
  rem = liftVS2 rem
  quotRem x y = (quot x y, rem x y)  -- TODO, another variant of liftVS2 needed
  div = liftVS2 div
  mod = liftVS2 mod
  -- divMod  -- TODO
  toInteger = case sameShape @sh @'[] of
    Just Refl -> toInteger . OS.unScalar
    _ -> error $ "OS.toInteger: shape not empty: "
                 ++ show (OS.shapeT @sh)

instance (Num (Vector r), Numeric r, Show r, Fractional r)
         => Fractional (OD.Array r) where
  (/) = liftVD2 (/)
  recip = liftVD recip
  fromRational = error "OD.fromRational: shape unknown"

instance (Num (Vector r), KnownNat n, Numeric r, Show r, Fractional r)
         => Fractional (OR.Array n r) where
  (/) = liftVR2 (/)
  recip = liftVR recip
  fromRational = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.constant [] . fromRational
    Nothing -> error $ "OR.fromRational: shape unknown at rank "
                       ++ show (valueOf @n :: Int)

instance (Num (Vector r), OS.Shape sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  (/) = liftVS2 (/)
  recip = liftVS recip
  fromRational = OS.constant . fromRational

instance (Floating (Vector r), Numeric r, Show r, Floating r)
         => Floating (OD.Array r) where
  pi = OD.constant [] pi
  exp = liftVD exp
  log = liftVD log
  sqrt = liftVD sqrt
  (**) = liftVD2 (**)
  logBase = liftVD2 logBase
  sin = liftVD sin
  cos = liftVD cos
  tan = liftVD tan
  asin = liftVD asin
  acos = liftVD acos
  atan = liftVD atan
  sinh = liftVD sinh
  cosh = liftVD cosh
  tanh = liftVD tanh
  asinh = liftVD asinh
  acosh = liftVD acosh
  atanh = liftVD atanh

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

instance (Floating (Vector r), OS.Shape sh, Numeric r, Floating r)
         => Floating (OS.Array sh r) where
  pi = OS.constant pi
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

instance (Real (Vector r), Numeric r, Show r, Ord r)
         => Real (OD.Array r) where
  toRational = undefined  -- TODO

instance (Real (Vector r), KnownNat n, Numeric r, Show r, Ord r)
         => Real (OR.Array n r) where
  toRational = undefined  -- TODO

instance (Real (Vector r), OS.Shape sh, Numeric r, Ord r)
         => Real (OS.Array sh r) where
  toRational = undefined  -- TODO

instance (RealFrac (Vector r), Numeric r, Show r, Fractional r, Ord r)
         => RealFrac (OD.Array r) where
  properFraction = error "OD.properFraction: can't be implemented"
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor even RealFracB from Boolean package).

instance ( RealFrac (Vector r), KnownNat n, Numeric r, Show r, Fractional r
         , Ord r )
         => RealFrac (OR.Array n r) where
  properFraction = error "OR.properFraction: can't be implemented"

instance (RealFrac (Vector r), OS.Shape sh, Numeric r, Fractional r, Ord r)
         => RealFrac (OS.Array sh r) where
  properFraction = error "OS.properFraction: can't be implemented"

instance (RealFloat (Vector r), Numeric r, Show r, Floating r, Ord r)
         => RealFloat (OD.Array r) where
  atan2 = liftVD2NoAdapt atan2
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

instance (RealFloat (Vector r), OS.Shape sh, Numeric r, Floating r, Ord r)
         => RealFloat (OS.Array sh r) where
  atan2 = liftVS2NoAdapt atan2
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

deriving instance Num (f a b) => Num (Flip f b a)

deriving instance Enum (f a b) => Enum (Flip f b a)

deriving instance Integral (f a b) => Integral (Flip f b a)

deriving instance Fractional (f a b) => Fractional (Flip f b a)

deriving instance Floating (f a b) => Floating (Flip f b a)

deriving instance Real (f a b) => Real (Flip f b a)

deriving instance RealFrac (f a b) => RealFrac (Flip f b a)

deriving instance RealFloat (f a b) => RealFloat (Flip f b a)


-- * Assorted orphans and additions

-- TODO: move to separate orphan module(s) at some point

instance Convert (OR.Array n a) (OD.Array a) where
  convert (RS.A (RG.A sh t)) = DS.A (DG.A sh t)

instance (OS.Shape sh, OS.Rank sh ~ n)
         => Convert (OS.Array sh a) (OR.Array n a) where
  convert (SS.A a@(SG.A t)) = RS.A (RG.A (SG.shapeL a) t)

type family MapSucc (xs :: [Nat]) :: [Nat] where
  MapSucc '[] = '[]
  MapSucc (x ': xs) = 1 + x ': MapSucc xs

data Dict c where
  Dict :: c => Dict c

trustMeThisIsAPermutationDict :: forall is. Dict (OS.Permutation is)
trustMeThisIsAPermutationDict = unsafeCoerce (Dict :: Dict (OS.Permutation '[]))

trustMeThisIsAPermutation :: forall is r. (OS.Permutation is => r) -> r
trustMeThisIsAPermutation r = case trustMeThisIsAPermutationDict @is of
  Dict -> r

sameShape :: forall sh1 sh2. (OS.Shape sh1, OS.Shape sh2) => Maybe (sh1 :~: sh2)
sameShape = case eqTypeRep (typeRep @sh1) (typeRep @sh2) of
              Just HRefl -> Just Refl
              Nothing -> Nothing

matchingRank :: forall sh1 n2. (OS.Shape sh1, KnownNat n2)
             => Maybe (OS.Rank sh1 :~: n2)
matchingRank =
  if length (OS.shapeT @sh1) == valueOf @n2
  then Just (unsafeCoerce Refl :: OS.Rank sh1 :~: n2)
  else Nothing

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
