{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances () where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Numeric.LinearAlgebra (Numeric)

-- TODO: once we can benchmark, write faster instances using
-- Num and other instances of hmatrix vectors

instance Numeric r => Num (OT.Array r) where
  (+) = OT.zipWithA (+)
  (-) = OT.zipWithA (-)
  (*) = OT.zipWithA (*)
  negate = OT.mapA negate
  abs = OT.mapA abs
  signum = OT.mapA signum
  fromInteger = OT.constant [] . fromInteger

instance (OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  (+) = OS.zipWithA (+)
  (-) = OS.zipWithA (-)
  (*) = OS.zipWithA (*)
  negate = OS.mapA negate
  abs = OS.mapA abs
  signum = OS.mapA signum
  fromInteger = OS.constant . fromInteger

instance (Numeric r, Fractional r) => Fractional (OT.Array r) where
  (/) = OT.zipWithA(/)
  recip = OT.mapA recip
  fromRational = OT.constant [] . fromRational

instance (OS.Shape sh, Numeric r, Fractional r)
         => Fractional (OS.Array sh r) where
  (/) = OS.zipWithA(/)
  recip = OS.mapA recip
  fromRational = OS.constant . fromRational

instance (Numeric r, Floating r) => Floating (OT.Array r) where
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

instance (OS.Shape sh, Numeric r, Floating r) => Floating (OS.Array sh r) where
  pi = OS.constant pi
  exp = OS.mapA exp
  log = OS.mapA log
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
  tanh = OS.mapA tanh
  asinh = OS.mapA asinh
  acosh = OS.mapA acosh
  atanh = OS.mapA atanh
