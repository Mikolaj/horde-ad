{-# LANGUAGE AllowAmbiguousTypes, CPP, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( liftVT, liftVT2, liftVR, liftVR2, liftVS, liftVS2
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
import           Data.Boolean
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)
import           Type.Reflection (eqTypeRep, typeRep, (:~~:) (HRefl))
import           Unsafe.Coerce (unsafeCoerce)

liftVT :: Numeric r
       => (Vector r -> Vector r)
       -> OD.Array r -> OD.Array r
liftVT op (DS.A (DG.A sh oit)) =
  if product sh >= V.length (OI.values oit)
  then DS.A $ DG.A sh $ oit {OI.values = op $ OI.values oit}
  else OD.fromVector sh $ op $ OI.toVectorT sh oit
    -- avoids applying op to any vector element not in the tensor
    -- (or at least ensures the right asymptotic behaviour, IDK)

-- For the operations where hmatrix can't adapt/expand scalars.
liftVT2NoAdapt :: Numeric r
               => (Vector r -> Vector r -> Vector r)
               -> OD.Array r -> OD.Array r -> OD.Array r
liftVT2NoAdapt op (DS.A (DG.A sht oit@(OI.T sst _ vt)))
                  (DS.A (DG.A shu oiu@(OI.T ssu _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1, then it's a degenerate case.
      -- Additionally, one of them may have non-nil shape due to the hack below.
      -- Whether hmatrix can auto-expand doesn't matter here.
      let (sh, ss) = if null sht then (shu, ssu) else (sht, sst)
      in DS.A $ DG.A sh $ OI.T ss 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, but hmatrix can't auto-expand.
      if product shu >= V.length vu
      then DS.A $ DG.A shu
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OI.toVectorT shu oiu
           in OD.fromVector shu $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      -- Second vector has length 1, but hmatrix can't auto-expand.
      if product sht >= V.length vt
      then DS.A $ DG.A sht
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OI.toVectorT sht oit
           in OD.fromVector sht $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) -> assert (sht == shu) $
      -- We don't special-case tensors that have same non-zero offsets, etc.,
      -- because the gains are small, correctness suspect (offsets can be
      -- larger than the vector length!) and we often apply op to sliced off
      -- elements, which defeats asymptotic guarantees.
      if product sht >= V.length vt && product shu >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu
                   && V.length vt == V.length vu)
           $ DS.A $ DG.A sht $ oit {OI.values = vt `op` vu}
      else OD.fromVector sht $ OI.toVectorT sht oit `op` OI.toVectorT sht oiu
        -- avoids applying op to any vector element not in the tensor
        -- (or at least ensures the right asymptotic behaviour, IDK)

-- Inspired by OI.zipWithT.
liftVT2 :: Numeric r
        => (Vector r -> Vector r -> Vector r)
        -> OD.Array r -> OD.Array r -> OD.Array r
liftVT2 op (DS.A (DG.A sht oit@(OI.T sst _ vt)))
           (DS.A (DG.A shu oiu@(OI.T ssu _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) ->
      -- If both vectors have length 1, then it's a degenerate case.
      -- Additionally, one of them may have non-nil shape due to the hack below,
      -- where the OD.constant in fromInteger below is replaced
      -- by unsafe internal operations and then hmatrix helps some more.
      -- However, the removal of the check vs run-time type is risky.
      let (sh, ss) = if null sht then (shu, ssu) else (sht, sst)
      in DS.A $ DG.A sh $ OI.T ss 0 $ vt `op` vu
    (1, _) ->
      -- First vector has length 1, hmatrix should auto-expand to match second.
      if product shu >= V.length vu
      then DS.A $ DG.A shu $ oiu {OI.values = vt `op` vu}
      else OD.fromVector shu $ vt `op` OI.toVectorT shu oiu
    (_, 1) ->
      -- Second vector has length 1, hmatrix should auto-expand to match first.
      if product sht >= V.length vt
      then DS.A $ DG.A sht $ oit {OI.values = vt `op` vu}
      else OD.fromVector sht $ OI.toVectorT sht oit `op` vu
    (_, _) -> assert (sht == shu) $
      if product sht >= V.length vt && product shu >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu
                   && V.length vt == V.length vu)
           $ DS.A $ DG.A sht $ oit {OI.values = vt `op` vu}
      else OD.fromVector sht $ OI.toVectorT sht oit `op` OI.toVectorT sht oiu

-- See the various comments above; we don't repeat them below.
liftVR :: (Numeric r, KnownNat n)
       => (Vector r -> Vector r)
       -> OR.Array n r -> OR.Array n r
liftVR op (RS.A (RG.A sh oit)) =
  if product sh >= V.length (OI.values oit)
  then RS.A $ RG.A sh $ oit {OI.values = op $ OI.values oit}
  else OR.fromVector sh $ op $ OI.toVectorT sh oit

liftVR2NoAdapt :: (Numeric r, KnownNat n)
               => (Vector r -> Vector r -> Vector r)
               -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2NoAdapt op (RS.A (RG.A sht oit@(OI.T sst _ vt)))
                  (RS.A (RG.A shu oiu@(OI.T ssu _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) ->
      let (sh, ss) = if null sht then (shu, ssu) else (sht, sst)
      in RS.A $ RG.A sh $ OI.T ss 0 $ vt `op` vu
    (1, _) ->
      if product shu >= V.length vu
      then RS.A $ RG.A shu
                $ oiu {OI.values = LA.konst (vt V.! 0) (V.length vu) `op` vu}
      else let v = OI.toVectorT shu oiu
           in OR.fromVector shu $ LA.konst (vt V.! 0) (V.length v) `op` v
    (_, 1) ->
      if product sht >= V.length vt
      then RS.A $ RG.A sht
                $ oit {OI.values = vt `op` LA.konst (vu V.! 0) (V.length vt)}
      else let v = OI.toVectorT sht oit
           in OR.fromVector sht $ v `op` LA.konst (vu V.! 0) (V.length v)
    (_, _) -> assert (sht == shu) $
      if product sht >= V.length vt && product shu >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu
                   && V.length vt == V.length vu)
           $ RS.A $ RG.A sht $ oit {OI.values = vt `op` vu}
      else OR.fromVector sht $ OI.toVectorT sht oit `op` OI.toVectorT sht oiu

liftVR2 :: (Numeric r, Show r, KnownNat n)
        => (Vector r -> Vector r -> Vector r)
        -> OR.Array n r -> OR.Array n r -> OR.Array n r
liftVR2 op t@(RS.A (RG.A sht oit@(OI.T sst _ vt)))
           u@(RS.A (RG.A shu oiu@(OI.T ssu _ vu))) =
  case (V.length vt, V.length vu) of
    (1, 1) ->
      let (sh, ss) = if null sht then (shu, ssu) else (sht, sst)
      in RS.A $ RG.A sh $ OI.T ss 0 $ vt `op` vu
    (1, _) ->
      if product shu >= V.length vu
      then RS.A $ RG.A shu $ oiu {OI.values = vt `op` vu}
      else OR.fromVector shu $ vt `op` OI.toVectorT shu oiu
    (_, 1) ->
      if product sht >= V.length vt
      then RS.A $ RG.A sht $ oit {OI.values = vt `op` vu}
      else OR.fromVector sht $ OI.toVectorT sht oit `op` vu
    (_, _) -> assert (sht == shu `blame` (t, u)) $
      if product sht >= V.length vt && product shu >= V.length vu
         && OI.strides oit == OI.strides oiu
      then assert (OI.offset oit == OI.offset oiu
                   && V.length vt == V.length vu)
           $ RS.A $ RG.A sht $ oit {OI.values = vt `op` vu}
      else OR.fromVector sht $ OI.toVectorT sht oit `op` OI.toVectorT sht oiu

liftVS :: (Numeric r, OS.Shape sh)
       => (Vector r -> Vector r)
       -> OS.Array sh r -> OS.Array sh r
liftVS op t = OS.fromVector $ op $ OS.toVector t

liftVS2 :: (Numeric r, OS.Shape sh)
        => (Vector r -> Vector r -> Vector r)
        -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2 op t u = OS.fromVector $ OS.toVector t `op` OS.toVector u

type instance BooleanOf CInt = Bool

instance IfB CInt where
  ifB b v w = if b then v else w

instance EqB CInt where
  (==*) = (==)
  (/=*) = (/=)

instance OrdB CInt where
  (<*) = (<)
  (<=*) = (<=)
  (>*) = (>)
  (>=*) = (>=)

type instance BooleanOf (OR.Array n r) = Bool

instance IfB (OR.Array n r) where
  ifB b v w = if b then v else w

instance (Eq r, Numeric r) => EqB (OR.Array n r) where
  (==*) = (==)
  (/=*) = (/=)

instance (Ord r, Numeric r) => OrdB (OR.Array n r) where
  (<*) = (<)
  (<=*) = (<=)
  (>*) = (>)
  (>=*) = (>=)

-- These constraints force @UndecidableInstances@.
instance (Num (Vector r), Numeric r) => Num (OD.Array r) where
  (+) = liftVT2 (+)
  (-) = liftVT2 (-)
  (*) = liftVT2 (*)
  negate = liftVT negate
  abs = liftVT abs
  signum = liftVT signum
  fromInteger = OD.constant [] . fromInteger  -- often fails and there's no fix

instance (Num (Vector r), KnownNat n, Numeric r, Show r)
         => Num (OR.Array n r) where
  (+) = liftVR2 (+)
  (-) = liftVR2 (-)
  (*) = liftVR2 (*)
  negate = liftVR negate
  abs = liftVR abs
  signum = liftVR signum
  fromInteger = RS.A . RG.A [] . OI.constantT [] . fromInteger
    -- often fails and there's no fix

-- instance (KnownNat n, Num r) => Num (ORB.Array n r) where

type instance BooleanOf (OS.Array sh r) = Bool

instance IfB (OS.Array sh r) where
  ifB b v w = if b then v else w

instance (Eq r, OS.Shape sh, Numeric r) => EqB (OS.Array sh r) where
  (==*) = (==)
  (/=*) = (/=)

instance (Ord r, OS.Shape sh, Numeric r) => OrdB (OS.Array sh r) where
  (<*) = (<)
  (<=*) = (<=)
  (>*) = (>)
  (>=*) = (>=)

instance (Num (Vector r), OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  (+) = liftVS2 (+)
  (-) = liftVS2 (-)
  (*) = liftVS2 (*)
  negate = liftVS negate
  abs = liftVS abs
  signum = liftVS signum
  fromInteger = OS.constant . fromInteger

instance (Num (Vector r), Numeric r, Fractional r)
         => Fractional (OD.Array r) where
  (/) = liftVT2 (/)
  recip = liftVT recip
  fromRational = OD.constant [] . fromRational

instance (Num (Vector r), KnownNat n, Numeric r, Show r, Fractional r)
         => Fractional (OR.Array n r) where
  (/) = liftVR2 (/)
  recip = liftVR recip
  fromRational = OR.constant [] . fromRational

--instance (KnownNat n, Fractional r)
--         => Fractional (ORB.Array n r) where

instance (Num (Vector r), OS.Shape sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  (/) = liftVS2 (/)
  recip = liftVS recip
  fromRational = OS.constant . fromRational

instance (Floating (Vector r), Numeric r, Floating r)
         => Floating (OD.Array r) where
  pi = OD.constant [] pi
  exp = liftVT exp
  log = liftVT log
  sqrt = liftVT sqrt
  (**) = liftVT2 (**)
  logBase = liftVT2 logBase
  sin = liftVT sin
  cos = liftVT cos
  tan = liftVT tan
  asin = liftVT asin
  acos = liftVT acos
  atan = liftVT atan
  sinh = liftVT sinh
  cosh = liftVT cosh
  tanh = liftVT tanh
  asinh = liftVT asinh
  acosh = liftVT acosh
  atanh = liftVT atanh

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

--instance (KnownNat n, Floating r)
--         => Floating (ORB.Array n r) where

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

instance (Real (Vector r), Numeric r, Ord r)
         => Real (OD.Array r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Real (Vector r), KnownNat n, Numeric r, Show r, Ord r)
         => Real (OR.Array n r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

--instance (KnownNat n, Real r)
--         => Real (ORB.Array n r) where

instance (Real (Vector r), OS.Shape sh, Numeric r, Ord r)
         => Real (OS.Array sh r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFrac (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (OD.Array r) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance ( RealFrac (Vector r), KnownNat n, Numeric r, Show r, Fractional r
         , Ord r )
         => RealFrac (OR.Array n r) where
  properFraction = undefined

--instance (KnownNat n, RealFrac r)
--         => RealFrac (ORB.Array n r) where
--  properFraction = undefined

instance (RealFrac (Vector r), OS.Shape sh, Numeric r, Fractional r, Ord r)
         => RealFrac (OS.Array sh r) where
  properFraction = undefined

instance (RealFloat (Vector r), Numeric r, Floating r, Ord r)
         => RealFloat (OD.Array r) where
  atan2 = liftVT2NoAdapt atan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain
  floatRadix = undefined
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
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain
  floatRadix = undefined
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined

--instance (KnownNat n, RealFloat r)
--         => RealFloat (ORB.Array n r) where

instance (RealFloat (Vector r), OS.Shape sh, Numeric r, Floating r, Ord r)
         => RealFloat (OS.Array sh r) where
  atan2 = liftVS2 atan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain
  floatRadix = undefined
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined

instance Convert (OR.Array n a) (OD.Array a) where
  convert (RS.A (RG.A sh t)) = DS.A (DG.A sh t)

instance (OS.Shape sh, OS.Rank sh ~ n)
         => Convert (OS.Array sh a) (OR.Array n a) where
  convert (SS.A a@(SG.A t)) = RS.A (RG.A (SG.shapeL a) t)

type instance BooleanOf (Flip f a b) = BooleanOf (f b a)

deriving instance IfB (f a b) => IfB (Flip f b a)

deriving instance EqB (f a b) => EqB (Flip f b a)

deriving instance OrdB (f a b) => OrdB (Flip f b a)

deriving instance Num (f a b) => Num (Flip f b a)

deriving instance Fractional (f a b) => Fractional (Flip f b a)

deriving instance Floating (f a b) => Floating (Flip f b a)

deriving instance Real (f a b) => Real (Flip f b a)

deriving instance RealFrac (f a b) => RealFrac (Flip f b a)

deriving instance RealFloat (f a b) => RealFloat (Flip f b a)


-- TODO: move to separate orphan module(s) at some point or to orthotope

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

instance (Num (Vector r), Numeric r, Ord r)
         => Real (Vector r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Num (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (Vector r) where
  properFraction = undefined

instance ( Floating (Vector r), Numeric r, RealFloat r )
         => RealFloat (Vector r) where
  atan2 = arctan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain
  floatRadix = undefined
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined
