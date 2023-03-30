{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.DualNumber
  ( ADVal, dD, pattern D, dDnotShared
  , SNat(..), staticNatValue, staticNatFromProxy
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , -- * Re-exports
    IsPrimal (..), IsPrimalWithScalar
  , Domain0, DomainR, Domains(..), emptyDomain0, nullDomains
  , ADNum
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.Proxy (Proxy (Proxy))
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Delta
  (Domain0, DomainR, Domains (..), emptyDomain0, nullDomains)
import HordeAd.Core.DualClass
import HordeAd.Core.TensorClass

-- * The main dual number type

-- | Values the objective functions operate on. The first type argument
-- is the automatic differentiation mode and the second is the underlying
-- basic values (scalars, vectors, matrices, tensors and any other
-- supported containers of scalars).
--
-- Here, the datatype is implemented as dual numbers (hence @D@),
-- where the primal component, the basic value, the \"number\"
-- can be any containers of scalars. The primal component has the type
-- given as the second type argument and the dual component (with the type
-- determined by the type faimly @Dual@) is defined elsewhere.
data ADVal a = D a (Dual a)

deriving instance (Show a, Show (Dual a)) => Show (ADVal a)

type instance BooleanOf (ADVal a) = BooleanOf a

instance IfB (ADVal Double) where
  ifB b v w = if b then v else w

instance IfB (ADVal Float) where
  ifB b v w = if b then v else w

instance IfB (ADVal (OR.Array n r)) where
  ifB b v w = if b then v else w

instance EqB a => EqB (ADVal a) where
  D u _ ==* D v _ = u ==* v
  D u _ /=* D v _ = u /=* v

instance OrdB a => OrdB (ADVal a) where
  D u _ <* D v _ = u <* v
  D u _ <=* D v _ = u <=* v
  D u _ >* D v _ = u >* v
  D u _ >=* D v _ = u >=* v

-- | Smart constructor for 'D' of 'ADVal' that additionally records sharing
-- information, if applicable for the differentiation mode in question.
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal a => a -> Dual a -> ADVal a
dD a dual = D a (recordSharing dual)

-- | This a not so smart constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: a -> Dual a -> ADVal a
dDnotShared = D


-- * Auxiliary definitions

type ADNum r =
  ( Numeric r
  , Show r
  , Show (Dual (OD.Array r))
  , HasRanks r
  , IsPrimalWithScalar r r
  , IsPrimalWithScalar (OD.Array r) r
  , IsPrimalR r
  , RealFloat r
  , RealFloat (Vector r)
  , Tensor r
  , TensorOf 0 r ~ OR.Array 0 r
  , TensorOf 1 r ~ OR.Array 1 r
  , IntOf r ~ CInt
  , DynamicTensor r ~ OD.Array r
  )

-- All this is not needed in the simplified version, except for compilation
-- with the common test code.
-- | Sizes of tensor dimensions, of batches, etc., packed for passing
-- between functions as witnesses of type variable values.
data SNat (n :: Nat) where
  MkSNat :: KnownNat n => SNat n

staticNatValue :: forall n i. (KnownNat n, Num i) => SNat n -> i
{-# INLINE staticNatValue #-}
staticNatValue = fromInteger . natVal

staticNatFromProxy :: KnownNat n => Proxy n -> SNat n
staticNatFromProxy Proxy = MkSNat

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal a => ADVal a -> ADVal a
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num a, IsPrimal a) => a -> ADVal a -> ADVal a
scaleNotShared a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal a) => ADVal a -> ADVal a -> ADVal a
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal a) => ADVal a -> ADVal a -> ADVal a
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))
{-
addParameters :: (Numeric r, Num (Vector r), DynamicTensor r ~ OD.Array r)
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1) (Domains b0 b1) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (Numeric r, DynamicTensor r ~ OD.Array r)
              => Domains r -> Domains r -> r
dotParameters (Domains a0 a1) (Domains b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

constantADVal :: IsPrimal a => a -> ADVal a
constantADVal a = dD a dZero


-- * Numeric instances for ADVal

-- These two instances are now required for the Tensor instance.
instance Eq a => Eq (ADVal a) where
  D u _ == D v _ = u == v
  D u _ /= D v _ = u /= v

instance Ord a => Ord (ADVal a) where
  compare (D u _) (D v _) = compare u v
  D u _ < D v _ = u < v
  D u _ <= D v _ = u <= v
  D u _ > D v _ = u > v
  D u _ >= D v _ = u >= v

instance (Num a, IsPrimal a) => Num (ADVal a) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' = dD (u - v) (dAdd u' (dScaleByScalar v (-1) v'))
  D u u' * D v v' = dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScaleByScalar v (-1) v')
  abs (D v v') = dD (abs v) (dScale (signum v) v')
  signum (D v _) = dD (signum v) dZero
  fromInteger = constantADVal . fromInteger

instance (Real a, IsPrimal a) => Real (ADVal a) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Fractional a, IsPrimal a) => Fractional (ADVal a) where
  D u u' / D v v' =
    dD (u / v) (dAdd (dScale (recip v) u') (dScale (- u / (v * v)) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = constantADVal . fromRational

instance (Floating a, IsPrimal a) => Floating (ADVal a) where
  pi = constantADVal pi
  exp (D u u') = let expU = exp u
                 in dD expU (dScale expU u')
  log (D u u') = dD (log u) (dScale (recip u) u')
  sqrt (D u u') = let sqrtU = sqrt u
                  in dD sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D u u' ** D v v' = dD (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                                       (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D u u') = dD (sin u) (dScale (cos u) u')
  cos (D u u') = dD (cos u) (dScale (- (sin u)) u')
  tan (D u u') = let cosU = cos u
                 in dD (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D u u') = dD (asin u) (dScale (recip (sqrt (1 - u*u))) u')
  acos (D u u') = dD (acos u) (dScale (- recip (sqrt (1 - u*u))) u')
  atan (D u u') = dD (atan u) (dScale (recip (1 + u*u)) u')
  sinh (D u u') = dD (sinh u) (dScale (cosh u) u')
  cosh (D u u') = dD (cosh u) (dScale (sinh u) u')
  tanh (D u u') = let y = tanh u
                  in dD y (dScale (1 - y * y) u')
  asinh (D u u') = dD (asinh u) (dScale (recip (sqrt (1 + u*u))) u')
  acosh (D u u') = dD (acosh u) (dScale (recip (sqrt (u*u - 1))) u')
  atanh (D u u') = dD (atanh u) (dScale (recip (1 - u*u)) u')

instance (RealFrac a, IsPrimal a) => RealFrac (ADVal a) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat a, IsPrimal a) => RealFloat (ADVal a) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in dD (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
  floatRadix (D u _) = floatRadix u
  floatDigits (D u _) = floatDigits u
  floatRange (D u _) = floatRange u
  decodeFloat (D u _) = decodeFloat u
  encodeFloat i j = D (encodeFloat i j) dZero
  isNaN (D u _) = isNaN u
  isInfinite (D u _) = isInfinite u
  isDenormalized (D u _) = isDenormalized u
  isNegativeZero (D u _) = isNegativeZero u
  isIEEE (D u _) = isIEEE u
