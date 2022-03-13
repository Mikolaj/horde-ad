{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             StandaloneDeriving, TypeFamilyDependencies, TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-redundant-constraints #-}
-- | Orphan instances for hmatrix classes.
module HordeAd.Internal.HmatrixOrphanInstances
  ( Forward(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Coerce (coerce)
import qualified Data.Vector.Generic as V
import qualified Internal.Numeric
import qualified Internal.Vectorized
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import qualified Numeric.Vector

newtype Forward a = Forward a
  deriving ( OT.Storable, Eq, Ord
           , Num, Real, Fractional, Floating, RealFrac, RealFloat )

type instance Internal.Numeric.RealOf (Forward r) = r

-- Sadly, needed for @HM.Container (Forward r)@ instances.
instance Integral Double where
  quotRem = undefined
  toInteger = undefined

instance Integral Float where
  quotRem = undefined
  toInteger = undefined

instance Num (Vector (Forward Double)) where
    (+) = Numeric.Vector.adaptScalar Internal.Numeric.addConstant HM.add
                                     (flip Internal.Numeric.addConstant)
    negate = HM.scale (-1)
    (*) = Numeric.Vector.adaptScalar HM.scale Internal.Numeric.mul
                                     (flip HM.scale)
    signum = coerce
             . Internal.Vectorized.vectorMapR Internal.Vectorized.Sign
             . coerce
    abs = coerce
          . Internal.Vectorized.vectorMapR Internal.Vectorized.Abs
          . coerce
    fromInteger = V.fromList . return . fromInteger

instance Num (Vector (Forward Float)) where
    (+) = Numeric.Vector.adaptScalar Internal.Numeric.addConstant HM.add
                                     (flip Internal.Numeric.addConstant)
    negate = HM.scale (-1)
    (*) = Numeric.Vector.adaptScalar HM.scale Internal.Numeric.mul
                                     (flip HM.scale)
    signum = coerce
             . Internal.Vectorized.vectorMapF Internal.Vectorized.Sign
             . coerce
    abs = coerce
          . Internal.Vectorized.vectorMapF Internal.Vectorized.Abs
          . coerce
    fromInteger = V.fromList . return . fromInteger

instance Floating (Vector (Forward Double)) where
    sin   = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Sin
            . coerce
    cos   = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Cos
            . coerce
    tan   = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Tan
            . coerce
    asin  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ASin
            . coerce
    acos  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ACos
            . coerce
    atan  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ATan
            . coerce
    sinh  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Sinh
            . coerce
    cosh  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Cosh
            . coerce
    tanh  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Tanh
            . coerce
    asinh = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ASinh
            . coerce
    acosh = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ACosh
            . coerce
    atanh = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.ATanh
            . coerce
    exp   = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Exp
            . coerce
    log   = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Log
            . coerce
    sqrt  = coerce
            . Internal.Vectorized.vectorMapR Internal.Vectorized.Sqrt
            . coerce
    (**)  =
      Numeric.Vector.adaptScalar
        (coerce
         . Internal.Vectorized.vectorMapValR Internal.Vectorized.PowSV
         . coerce)
        (coerce
         . Internal.Vectorized.vectorZipR Internal.Vectorized.Pow
         . coerce)
        (flip (coerce
               . Internal.Vectorized.vectorMapValR Internal.Vectorized.PowVS
               . coerce))
    pi    = V.fromList [Forward pi]

instance Floating (Vector (Forward Float)) where
    sin   = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Sin
            . coerce
    cos   = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Cos
            . coerce
    tan   = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Tan
            . coerce
    asin  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ASin
            . coerce
    acos  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ACos
            . coerce
    atan  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ATan
            . coerce
    sinh  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Sinh
            . coerce
    cosh  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Cosh
            . coerce
    tanh  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Tanh
            . coerce
    asinh = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ASinh
            . coerce
    acosh = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ACosh
            . coerce
    atanh = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.ATanh
            . coerce
    exp   = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Exp
            . coerce
    log   = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Log
            . coerce
    sqrt  = coerce
            . Internal.Vectorized.vectorMapF Internal.Vectorized.Sqrt
            . coerce
    (**)  =
      Numeric.Vector.adaptScalar
        (coerce
         . Internal.Vectorized.vectorMapValF Internal.Vectorized.PowSV
         . coerce)
        (coerce
         . Internal.Vectorized.vectorZipF Internal.Vectorized.Pow
         . coerce)
        (flip (coerce
               . Internal.Vectorized.vectorMapValF Internal.Vectorized.PowVS
               . coerce))
    pi    = V.fromList [Forward pi]

deriving instance HM.Element a => HM.Element (Forward a)

deriving instance (HM.Container Vector a, Ord a, Integral a, Fractional a)
                  => HM.Container Vector (Forward a)

deriving instance Internal.Numeric.CTrans a
                  => Internal.Numeric.CTrans (Forward a)

deriving instance HM.Product (Forward Double)

deriving instance HM.Numeric (Forward Double)

deriving instance HM.Product (Forward Float)

deriving instance HM.Numeric (Forward Float)
