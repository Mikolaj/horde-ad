{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
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
import qualified Numeric.LinearAlgebra as HM

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

instance ( Floating (Vector r), Num (Vector r)
         , Numeric r, Floating r )
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

instance ( Floating (Vector r), Num (Vector r)
         , OS.Shape sh, Numeric r, Floating r )
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

type instance Element (OT.Array r) = r

type instance Element (OS.Array sh r) = r

instance Numeric r => MonoFunctor (OT.Array r) where
  omap = OT.mapA

instance (OS.Shape sh, Numeric r) => MonoFunctor (OS.Array sh r) where
  omap = OS.mapA


-- TODO: move to separate orphan module(s) at some point

type instance Element (Matrix r) = r

type instance Element Double = Double

type instance Element Float = Float

instance Numeric r => MonoFunctor (Matrix r) where
  omap = HM.cmap

instance MonoFunctor Double where
  omap f r = f r

instance MonoFunctor Float where
  omap f r = f r
