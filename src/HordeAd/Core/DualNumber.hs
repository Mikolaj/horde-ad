{-# LANGUAGE UndecidableInstances #-}
-- | Dual numbers and arithmetic operations on them. This is a part of
-- the mid-level API of the horde-ad library, together with
-- the safely impure "HordeAd.Core.DualClass".
module HordeAd.Core.DualNumber
  ( -- * The main dual number type
    ADVal, dD, pattern D, dDnotShared, constantADVal, ADValClown
    -- * Auxiliary definitions
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , DerivativeStages (..)
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Kind (Constraint, Type)
import           GHC.TypeLits (KnownNat)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.Delta (Dual)
import HordeAd.Core.DualClass
import HordeAd.Core.Types

-- * The main dual number type

-- | Values that the objective functions operate on when they are being
-- differentiated. The values are, in general, tensors.
-- The first type argument is the functor determining the structure
-- of the tensors (whether ranked, shaped, dynamic, storable, unboxed, etc.).
-- The second argument is the underlying scalar type. The third
-- is the rank or shape of the tensor value.
--
-- The datatype is implemented as dual numbers (hence @D@),
-- where @ADShare@ holds the sharing information if the values are,
-- in fact, AST terms. The @f r z@ value is the primal component,
-- which is the normal, the basic value. The exact type of the dual component
-- is determined by a definition of type family @Dual@ provided elsewhere.
data ADVal (f :: TensorKind k) (r :: Type) (z :: k) =
  D ADShare (f r z) (Dual f r z)

deriving instance (Show (f r z), Show (Dual f r z))
                  => Show (ADVal f r z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal f r z
   => ADShare -> f r z -> Dual f r z -> ADVal f r z
dD !l !a !dual = D l a (recordSharing dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: ADShare -> f r z -> Dual f r z -> ADVal f r z
dDnotShared = D

constantADVal :: IsPrimal f r z => f r z -> ADVal f r z
constantADVal a = dDnotShared emptyADShare a (dZeroOfShape a)

type ADValClown dynamic = Flip (ADVal (Clown dynamic)) '()


-- * Auxiliary definitions

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal f r z => ADVal f r z -> ADVal f r z
ensureToplevelSharing (D l u u') = dD l u u'

scaleNotShared :: (Num (f r z), IsPrimal f r z)
               => f r z -> ADVal f r z -> ADVal f r z
scaleNotShared !a (D l u u') = dDnotShared l (a * u) (dScale a u')

addNotShared :: (Num (f r z), IsPrimal f r z)
             => ADVal f r z -> ADVal f r z -> ADVal f r z
addNotShared (D l1 u u') (D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u + v) (dAdd u' v')

multNotShared :: (Num (f r z), IsPrimal f r z)
              => ADVal f r z -> ADVal f r z -> ADVal f r z
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

-- * Reverse and forward derivative stages instances

type DerivativeStages :: forall k. TensorKind k -> Constraint
class DerivativeStages g where
  revProduceArtifact
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => Bool
    -> (Domains (DynamicOf g) -> g r y)
    -> AstEnv (ADVal (RankedOf (PrimalOf g)))
              (ADVal (ShapedOf (PrimalOf g)))
    -> DomainsOD
    -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)

  revEvalArtifact
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => AstArtifactRev (PrimalOf g) r y -> DomainsOD -> Maybe (ConcreteOf g r y)
    -> (DomainsOD, ConcreteOf g r y)

  fwdProduceArtifact
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => (Domains (DynamicOf g) -> g r y)
    -> AstEnv (ADVal (RankedOf (PrimalOf g)))
              (ADVal (ShapedOf (PrimalOf g)))
    -> DomainsOD
    -> (AstArtifactFwd (PrimalOf g) r y, Dual (PrimalOf g) r y)

  fwdEvalArtifact
    :: forall r y. (GoodScalar r, HasSingletonDict y)
    => AstArtifactFwd (PrimalOf g) r y -> DomainsOD -> DomainsOD
    -> (ConcreteOf g r y, ConcreteOf g r y)


-- * Numeric instances for ADVal

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f r z) where
  (==) = error "AST requires that EqB be used instead"
  (/=) = error "AST requires that EqB be used instead"

instance Ord (ADVal f r z) where
  (<=) = error "AST requires that OrdB be used instead"

instance (Num (f r z), IsPrimal f r z) => Num (ADVal f r z) where
  -- The 0 cases are needed to get GHC 9.6 to use the specialization
  -- (only at rank 0, though; we'd need many more for common ranks and shapes).
  {-# SPECIALIZE instance Num (ADVal (Flip OR.Array) Double 0) #-}
  {-# SPECIALIZE instance Num (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (AstRanked PrimalSpan) Double n) #-}
  D l1 u u' + D l2 v v' = dD (l1 `mergeADShare` l2) (u + v) (dAdd u' v')
  D l1 u u' - D l2 v v' =
    dD (l1 `mergeADShare` l2) (u - v) (dAdd u' (dScale (intOfShape v (-1)) v'))
  D l1 ue u' * D l2 ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D l v v') = dD l (negate v) (dScale (intOfShape v (-1)) v')
  abs (D l ve v') = let !(!l2, v) = recordSharingPrimal ve l
                    in dD l2 (abs v) (dScale (signum v) v')
  signum (D l v _) = dD l (signum v) (dZeroOfShape v)
  fromInteger = constantADVal . fromInteger

instance (Real (f r z), IsPrimal f r z) => Real (ADVal f r z) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (ADVal f r z) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Integral (f r z), IsPrimal f r z)
         => Integral (ADVal f r z) where
  quot (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (quot u v) (dZeroOfShape u)
  rem (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (rem u v) (dZeroOfShape u)
  quotRem x y = (quot x y, rem x y)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Fractional (f r z), IsPrimal f r z) => Fractional (ADVal f r z) where
  {-# SPECIALIZE instance
      Fractional (ADVal (Flip OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Fractional (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (AstRanked PrimalSpan) Double n) #-}
  D l1 ue u' / D l2 ve v' =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u / v)
             (dAdd (dScale (recip v) u') (dScale (- u / (v * v)) v'))
  recip (D l ve v') =
    let !(!l2, v) = recordSharingPrimal ve l
        minusRecipSq = - recip (v * v)
    in dD l2 (recip v) (dScale minusRecipSq v')
  fromRational = constantADVal . fromRational

instance (Floating (f r z), IsPrimal f r z) => Floating (ADVal f r z) where
  {-# SPECIALIZE instance
      Floating (ADVal (Flip OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Floating (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (AstRanked PrimalSpan) Double n) #-}
  pi = constantADVal pi
  exp (D l ue u') = let !(!l2, expU) = recordSharingPrimal (exp ue) l
                    in dD l2 expU (dScale expU u')
  log (D l ue u') = let !(!l2, u) = recordSharingPrimal ue l
                    in dD l2 (log u) (dScale (recip u) u')
  sqrt (D l ue u') = let !(!l2, sqrtU) = recordSharingPrimal (sqrt ue) l
                     in dD l2 sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D l1 ue u' ** D l2 ve v' =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3
    in dD l4 (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v 1))) u')
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
                     in dD l2 (asin u)
                           (dScale (recip (sqrt (intOfShape u 1 - u*u))) u')
  acos (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (acos u)
                           (dScale (- recip (sqrt (intOfShape u 1 - u*u))) u')
  atan (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (atan u)
                           (dScale (recip (intOfShape u 1 + u*u)) u')
  sinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (sinh u) (dScale (cosh u) u')
  cosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                     in dD l2 (cosh u) (dScale (sinh u) u')
  tanh (D l ue u') = let (l2, y) = recordSharingPrimal (tanh ue) l
                     in dD l2 y (dScale (intOfShape y 1 - y * y) u')
  asinh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (asinh u)
                            (dScale (recip (sqrt (intOfShape u 1 + u*u))) u')
  acosh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (acosh u)
                            (dScale (recip (sqrt (u*u - intOfShape u 1))) u')
  atanh (D l ue u') = let (l2, u) = recordSharingPrimal ue l
                      in dD l2 (atanh u)
                            (dScale (recip (intOfShape u 1 - u*u)) u')

instance (RealFrac (f r z), IsPrimal f r z) => RealFrac (ADVal f r z) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat (f r z), IsPrimal f r z) => RealFloat (ADVal f r z) where
  {-# SPECIALIZE instance
      RealFloat (ADVal (Flip OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      RealFloat (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (AstRanked PrimalSpan) Double n) #-}
  atan2 (D l1 ue u') (D l2 ve v') =
    let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2 in
    let !(!l4, v) = recordSharingPrimal ve l3 in
    let !(!l5, t) = recordSharingPrimal (recip (u * u + v * v)) l4
    in dD l5 (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
  -- Note that for term types @a@ this is invalid without an extra let
  -- containing the first field of @D@. However, for terms this is
  -- unimplemented anyway.
  floatRadix (D _ u _) = floatRadix u
  floatDigits (D _ u _) = floatDigits u
  floatRange (D _ u _) = floatRange u
  decodeFloat (D _ u _) = decodeFloat u
  encodeFloat i j = constantADVal (encodeFloat i j)
  isNaN (D _ u _) = isNaN u
  isInfinite (D _ u _) = isInfinite u
  isDenormalized (D _ u _) = isDenormalized u
  isNegativeZero (D _ u _) = isNegativeZero u
  isIEEE (D _ u _) = isIEEE u
