{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( liftVT, liftVT2, liftVS, liftVS2
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (arctan2)

liftVT :: Numeric r
       => (Vector r -> Vector r)
       -> OT.Array r -> OT.Array r
liftVT op t = OT.fromVector (OT.shapeL t) $ op $ OT.toVector t

liftVT2 :: Numeric r
        => (Vector r -> Vector r -> Vector r)
        -> OT.Array r -> OT.Array r -> OT.Array r
liftVT2 op t u = OT.fromVector (OT.shapeL t) $ OT.toVector t `op` OT.toVector u

liftVS :: (Numeric r, OS.Shape sh)
       => (Vector r -> Vector r)
       -> OS.Array sh r -> OS.Array sh r
liftVS op t = OS.fromVector $ op $ OS.toVector t

liftVS2 :: (Numeric r, OS.Shape sh)
        => (Vector r -> Vector r -> Vector r)
        -> OS.Array sh r -> OS.Array sh r -> OS.Array sh r
liftVS2 op t u = OS.fromVector $ OS.toVector t `op` OS.toVector u

-- These constraints force @UndecidableInstances@.
instance (Num (Vector r), Numeric r) => Num (OT.Array r) where
  (+) = liftVT2 (+)
  (-) = liftVT2 (-)
  (*) = liftVT2 (*)
  negate = liftVT negate
  abs = liftVT abs
  signum = liftVT signum
  fromInteger = OT.constant [] . fromInteger

instance (Num (Vector r), OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  (+) = liftVS2 (+)
  (-) = liftVS2 (-)
  (*) = liftVS2 (*)
  negate = liftVS negate
  abs = liftVS abs
  signum = liftVS signum
  fromInteger = OS.constant . fromInteger

instance (Num (Vector r), Numeric r, Fractional r)
         => Fractional (OT.Array r) where
  (/) = liftVT2 (/)
  recip = liftVT recip
  fromRational = OT.constant [] . fromRational

instance (Num (Vector r), OS.Shape sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  (/) = liftVS2 (/)
  recip = liftVS recip
  fromRational = OS.constant . fromRational

instance (Floating (Vector r), Numeric r, Floating r)
         => Floating (OT.Array r) where
  pi = OT.constant [] pi
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
         => Real (OT.Array r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Real (Vector r), OS.Shape sh, Numeric r, Ord r)
         => Real (OS.Array sh r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFrac (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (OT.Array r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFrac (Vector r), OS.Shape sh, Numeric r, Fractional r, Ord r)
         => RealFrac (OS.Array sh r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFloat (Vector r), Numeric r, Floating r, Ord r)
         => RealFloat (OT.Array r) where
  atan2 = liftVT2 atan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

instance (RealFloat (Vector r), OS.Shape sh, Numeric r, Floating r, Ord r)
         => RealFloat (OS.Array sh r) where
  atan2 = liftVS2 atan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

type instance Element (OT.Array r) = r

type instance Element (OS.Array sh r) = r

instance Numeric r => MonoFunctor (OT.Array r) where
  omap = OT.mapA

instance (OS.Shape sh, Numeric r) => MonoFunctor (OS.Array sh r) where
  omap = OS.mapA


-- TODO: move to separate orphan module(s) at some point

instance (Num (Vector r), Numeric r, Ord r)
         => Real (Vector r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Num (Vector r), Numeric r, Fractional r, Ord r)
         => RealFrac (Vector r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance ( Floating (Vector r), Numeric r, RealFloat r )
         => RealFloat (Vector r) where
  atan2 = arctan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

-- This instance are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Numeric r => Ord (Matrix r) where

instance (Num (Vector r), Numeric r, Ord (Matrix r))
         => Real (Matrix r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Num (Vector r), Numeric r, Fractional r, Ord r, Ord (Matrix r))
         => RealFrac (Matrix r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance ( Floating (Vector r), Numeric r, RealFloat r, Ord (Matrix r) )
         => RealFloat (Matrix r) where
  atan2 = arctan2
    -- we can be selective here and omit the other methods,
    -- most of which don't even have a differentiable codomain

type instance Element (Matrix r) = r

type instance Element Double = Double

type instance Element Float = Float

instance Numeric r => MonoFunctor (Matrix r) where
  omap = LA.cmap

instance MonoFunctor Double where
  omap f = f

instance MonoFunctor Float where
  omap f = f
