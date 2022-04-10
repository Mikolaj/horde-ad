{-# OPTIONS_GHC -Wno-orphans #-}
-- | Orphan instances for orthotope classes.
module HordeAd.Internal.OrthotopeOrphanInstances () where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Numeric.LinearAlgebra (Numeric)

-- TODO: once we can benchmark, write faster instances using
-- Num instance of hmatrix vectors

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
