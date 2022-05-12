{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances () where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

-- TODO: once we can benchmark, convert more instances to
-- use the corresponding instances of hmatrix vectors
-- and refactor the existing instances

-- These constraints force @UndecidableInstances@.
{-
instance (Num (Vector r), Numeric r) => Num (OT.Array r) where
  t + u = OT.fromVector (OT.shapeL t) $ OT.toVector t + OT.toVector u
  t - u = OT.fromVector (OT.shapeL t) $ OT.toVector t - OT.toVector u
  t * u = OT.fromVector (OT.shapeL t) $ OT.toVector t * OT.toVector u
  negate t = OT.fromVector (OT.shapeL t) $ negate $ OT.toVector t
  abs t = OT.fromVector (OT.shapeL t) $ abs $ OT.toVector t
  signum t = OT.fromVector (OT.shapeL t) $ signum $ OT.toVector t
  fromInteger = OT.constant [] . fromInteger

instance (Num (Vector r), OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  t + u = OS.fromVector $ OS.toVector t + OS.toVector u
  t - u = OS.fromVector $ OS.toVector t - OS.toVector u
  t * u = OS.fromVector $ OS.toVector t * OS.toVector u
  negate t = OS.fromVector $ negate $ OS.toVector t
  abs t = OS.fromVector $ abs $ OS.toVector t
  signum t = OS.fromVector $ signum $ OS.toVector t
  fromInteger = OS.constant . fromInteger

instance (Num (Vector r), Numeric r, Fractional r)
         => Fractional (OT.Array r) where
  t / u = OT.fromVector (OT.shapeL t) $ OT.toVector t / OT.toVector u
  recip t = OT.fromVector (OT.shapeL t) $ recip $ OT.toVector t
  fromRational = OT.constant [] . fromRational

instance (Num (Vector r), OS.Shape sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  t / u = OS.fromVector $ OS.toVector t / OS.toVector u
  recip t = OS.fromVector $ recip $ OS.toVector t
  fromRational = OS.constant . fromRational

instance (Num (Vector r), Numeric r, Floating r)
         => Floating (OT.Array r) where
  pi = OT.constant [] pi
  exp = OT.mapA exp
  log = OT.mapA log
  sqrt = OT.mapA sqrt
  (**) = OT.zipWithA (**)
  logBase = OT.zipWithA logBase
  sin = OT.mapA sin
  cos = OT.mapA cos
  tan = OT.mapA tan
  asin = OT.mapA asin
  acos = OT.mapA acos
  atan = OT.mapA atan
  sinh = OT.mapA sinh
  cosh = OT.mapA cosh
  tanh = OT.mapA tanh
  asinh = OT.mapA asinh
  acosh = OT.mapA acosh
  atanh = OT.mapA atanh

instance ( Floating (Vector r), Num (Vector r)
         , OS.Shape sh, Numeric r, Floating r )
         => Floating (OS.Array sh r) where
  pi = OS.constant pi
  exp t = OS.fromVector $ exp $ OS.toVector t
  log t = OS.fromVector $ log $ OS.toVector t
  sqrt = OS.mapA sqrt
  (**) = OS.zipWithA (**)
  logBase = OS.zipWithA logBase
  sin = OS.mapA sin
  cos = OS.mapA cos
  tan = OS.mapA tan
  asin = OS.mapA asin
  acos = OS.mapA acos
  atan = OS.mapA atan
  sinh = OS.mapA sinh
  cosh = OS.mapA cosh
  tanh t = OS.fromVector $ tanh $ OS.toVector t
  asinh = OS.mapA asinh
  acosh = OS.mapA acosh
  atanh = OS.mapA atanh
-}

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
