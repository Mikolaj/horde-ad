{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them. This is a part of
-- the mid-level API of the horde-ad library, together with
-- the safely impure "HordeAd.Core.DualClass".
module HordeAd.Core.DualNumber
  ( ADTensor, ADVal, dD, pattern D, dDnotShared
  , SNat(..), staticNatValue, staticNatFromProxy
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , IsPrimal (..), ADNum
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.Domains
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
data ADVal a = D (ADShare (Underlying a)) a (Dual a)

deriving instance (Show a, Show (ADShare (Underlying a)), Show (Dual a))
                  => Show (ADVal a)

-- | Smart constructor for 'D' of 'ADVal' that additionally records sharing
-- information, if applicable for the differentiation mode in question.
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal a => ADShare (Underlying a) -> a -> Dual a -> ADVal a
dD l a dual = D l a (recordSharing dual)

-- | This a not so smart constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: ADShare (Underlying a) -> a -> Dual a -> ADVal a
dDnotShared = D


-- * Auxiliary definitions

type ADTensor r =
  ( IsPrimal r
  , HasRanks r
  , Tensor r
  , DynamicTensor r
  , DomainsCollection r
  , DomainsTensor r
  )

type ADNum r =
  ( Numeric r
  , Show r
  , Show (Dual (OD.Array r))
  , Scalar r ~ r
  , IsPrimalR r
  , ADTensor r
  , Ranked r ~ Flip OR.Array r
  , IntOf r ~ CInt
  , DTensorOf r ~ OD.Array r
  , Floating (Vector r)
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
ensureToplevelSharing (D l u u') = dD l u u'

scaleNotShared :: (Num a, IsPrimal a) => a -> ADVal a -> ADVal a
scaleNotShared a (D l u u') = dDnotShared l (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal a) => ADVal a -> ADVal a -> ADVal a
addNotShared (D l1 u u') (D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal a) => ADVal a -> ADVal a -> ADVal a
multNotShared (D l1 u u') (D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u * v) (dAdd (dScale v u') (dScale u v'))
{-
addParameters :: (Numeric r, Num (Vector r), DTensorOf r ~ OD.Array r)
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1) (Domains b0 b1) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (Numeric r, DTensorOf r ~ OD.Array r)
              => Domains r -> Domains r -> r
dotParameters (Domains a0 a1) (Domains b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

constantADVal :: IsPrimal a => a -> ADVal a
constantADVal a = dDnotShared emptyADShare a dZero


-- * Numeric instances for ADVal

-- These two instances are now required for the Tensor instance.
-- Note that for term types @a@ this is invalid without an extra let
-- containing the first field of @D@. However, for terms this is invalid
-- anyway, because they require interpretation before they can be compared.
instance Eq a => Eq (ADVal a) where
  D _ u _ == D _ v _ = u == v
  D _ u _ /= D _ v _ = u /= v

instance Ord a => Ord (ADVal a) where
  compare (D _ u _) (D _ v _) = compare u v
  D _ u _ < D _ v _ = u < v
  D _ u _ <= D _ v _ = u <= v
  D _ u _ > D _ v _ = u > v
  D _ u _ >= D _ v _ = u >= v

instance (Num a, IsPrimal a) => Num (ADVal a) where
  D l1 u u' + D l2 v v' = dD (l1 `mergeADShare` l2) (u + v) (dAdd u' v')
  D l1 u u' - D l2 v v' =
    dD (l1 `mergeADShare` l2) (u - v) (dAdd u' (dScaleByScalar v (-1) v'))
  D l1 ue u' * D l2 ve v' =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D l v v') = dD l (negate v) (dScaleByScalar v (-1) v')
  abs (D l ve v') = let (l2, v) = recordSharingPrimal ve l
                    in dD l2 (abs v) (dScale (signum v) v')
  signum (D l v _) = dD l (signum v) dZero
  fromInteger = constantADVal . fromInteger

instance (Real a, IsPrimal a) => Real (ADVal a) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Fractional a, IsPrimal a) => Fractional (ADVal a) where
  D l1 ue u' / D l2 ve v' =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u / v)
             (dAdd (dScale (recip v) u') (dScale (- u / (v * v)) v'))
  recip (D l ve v') =
    let (l2, v) = recordSharingPrimal ve l
        minusRecipSq = - recip (v * v)
    in dD l2 (recip v) (dScale minusRecipSq v')
  fromRational = constantADVal . fromRational

instance (Floating a, IsPrimal a) => Floating (ADVal a) where
  pi = constantADVal pi
  exp (D l ue u') = let (l2, expU) = recordSharingPrimal (exp ue) l
                    in dD l2 expU (dScale expU u')
  log (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                    in dD l2 (log u) (dScale (recip u) u')
  sqrt (D l ue u') = let (l2, sqrtU) = recordSharingPrimal (sqrt ue) l
                     in dD l2 sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D l1 ue u' ** D l2 ve v' =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                            (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                    in dD l2 (sin u) (dScale (cos u) u')
  cos (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                    in dD l2 (cos u) (dScale (- (sin u)) u')
  tan (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                        (l3, cosU) = recordSharingPrimal (cos u) l2
                    in dD l3 (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (asin u) (dScale (recip (sqrt (1 - u*u))) u')
  acos (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (acos u) (dScale (- recip (sqrt (1 - u*u))) u')
  atan (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (atan u) (dScale (recip (1 + u*u)) u')
  sinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (sinh u) (dScale (cosh u) u')
  cosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (cosh u) (dScale (sinh u) u')
  tanh (D l ue u') = let (l2, y) = recordSharingPrimal (tanh ue) l
                     in dD l2 y (dScale (1 - y * y) u')
  asinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (asinh u) (dScale (recip (sqrt (1 + u*u))) u')
  acosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (acosh u) (dScale (recip (sqrt (u*u - 1))) u')
  atanh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (atanh u) (dScale (recip (1 - u*u)) u')

instance (RealFrac a, IsPrimal a) => RealFrac (ADVal a) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat a, IsPrimal a) => RealFloat (ADVal a) where
  atan2 (D l1 ue u') (D l2 ve v') =
    -- The bangs below are neccessary for GHC 9.2.7.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3 in
    let !(!l5, t) = recordSharingPrimal (recip (u * u + v * v)) l4
    in dD l5 (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
  -- Note that for term types @a@ this is invalid without an extra let
  -- containing the first field of @D@. However, for terms this unimplemented
  -- anyway, for unrelated reasons.
  floatRadix (D _ u _) = floatRadix u
  floatDigits (D _ u _) = floatDigits u
  floatRange (D _ u _) = floatRange u
  decodeFloat (D _ u _) = decodeFloat u
  encodeFloat i j = D emptyADShare (encodeFloat i j) dZero
  isNaN (D _ u _) = isNaN u
  isInfinite (D _ u _) = isInfinite u
  isDenormalized (D _ u _) = isDenormalized u
  isNegativeZero (D _ u _) = isNegativeZero u
  isIEEE (D _ u _) = isIEEE u
