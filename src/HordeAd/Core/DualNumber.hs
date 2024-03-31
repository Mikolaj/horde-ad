{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them.
module HordeAd.Core.DualNumber
  ( -- * The main dual number type
    ADVal, dD, pattern D, dDnotShared, constantADVal
    -- * Auxiliary definitions
  , indexPrimal, fromList, indexPrimalS, fromListS
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , generateDeltaInputs, makeADInputs
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.Kind (Type)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           Type.Reflection (typeRep)

import           HordeAd.Core.Ast
import           HordeAd.Core.Delta
import           HordeAd.Core.HVector
import           HordeAd.Core.IsPrimal
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

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
type role ADVal nominal nominal nominal
data ADVal (f :: TensorType ty) (r :: Type) (z :: ty) =
  ADVal (f r z) (Dual f r z)

pattern D :: f r z -> Dual f r z -> ADVal f r z
pattern D t u <- ADVal t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f r z), Show (Dual f r z))
                  => Show (ADVal f r z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal f r z
   => f r z -> Dual f r z -> ADVal f r z
dD !a !dual = dDnotShared a (shareDual dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: f r z -> Dual f r z -> ADVal f r z
dDnotShared = ADVal


-- * Auxiliary definitions

constantADVal :: IsPrimal f r z => f r z -> ADVal f r z
constantADVal a = dDnotShared a (dZeroOfShape a)

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal f r z => ADVal f r z -> ADVal f r z
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num (f r z), IsPrimal f r z)
               => f r z -> ADVal f r z -> ADVal f r z
scaleNotShared !a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num (f r z), IsPrimal f r z)
             => ADVal f r z -> ADVal f r z -> ADVal f r z
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num (f r z), IsPrimal f r z)
              => ADVal f r z -> ADVal f r z -> ADVal f r z
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))
{-
addParameters :: (Numeric r, Num (Vector r), DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> HVector r
addParameters (HVector a0 a1) (HVector b0 b1) =
  HVector (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (Numeric r, DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> r
dotParameters (HVector a0 a1) (HVector b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

generateDeltaInputs
  :: forall ranked ranked2 shaped2.
     (RankedTensor ranked, shaped2 ~ ShapedOf ranked2)
  => HVector ranked
  -> HVector (Dual ranked2)
generateDeltaInputs =
  let f :: Int -> DynamicTensor ranked -> DynamicTensor (Dual ranked2)
      f i (DynamicRanked @r @n t) =
        case rshape t of
          (sh :: ShapeInt n2) | Just Refl <- sameNat (Proxy @n) (Proxy @n2) ->
            DynamicRanked $ InputR @ranked2 @r @n sh (toInputId i)
          _ -> error "generateDeltaInputs: wrong rank"
      f i (DynamicShaped @r @sh _) =
        DynamicShaped $ InputS @shaped2 @r @sh (toInputId i)
      f i (DynamicRankedDummy @r @sh _ _) =
        withListSh (Proxy @sh) $ \sh ->
          DynamicRanked $ InputR @ranked2 @r sh (toInputId i)
      f i (DynamicShapedDummy @r @sh _ _) =
        DynamicShaped $ InputS @shaped2 @r @sh (toInputId i)
  in V.imap f
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE generateDeltaInputs
  :: HVector (Flip OR.Array) -> HVector (Dual (Flip OR.Array)) #-}
-}

-- Not specialized, because not overloaded (HVector is a type synonym).
makeADInputs
  :: HVector ranked -> HVector (Dual ranked)
  -> HVector (ADVal ranked)
makeADInputs =
  let f :: DynamicTensor ranked -> DynamicTensor (Dual ranked)
        -> DynamicTensor (ADVal ranked)
      f (DynamicRanked @r @n t) (DynamicRanked @r2 @n2 d)
        | Just Refl <- sameNat (Proxy @n) (Proxy @n2)
        , Just Refl <- testEquality (typeRep @r) (typeRep @r2) =
          DynamicRanked $ dDnotShared t d
      f (DynamicShaped @r @sh t) (DynamicShaped @r2 @sh2 d)
        | Just Refl <- sameShape @sh @sh2
        , Just Refl <- testEquality (typeRep @r) (typeRep @r2) =
          DynamicShaped $ dDnotShared t d
      f _ _ = error "makeADInputs: non-matching arguments"
  in V.zipWith f


-- * Assorted instances

type instance BoolOf (ADVal f) = BoolOf f

instance EqF f => EqF (ADVal f) where
  D u _ ==. D v _ = u ==. v
  D u _ /=. D v _ = u /=. v

instance OrdF f => OrdF (ADVal f) where
  D u _ <. D v _ = u <. v
  D u _ <=. D v _ = u <=. v
  D u _ >. D v _ = u >. v
  D u _ >=. D v _ = u >=. v

indexPrimal :: (RankedTensor ranked, KnownNat m, KnownNat n, GoodScalar r)
            => ADVal ranked r (m + n) -> IndexOf ranked m
            -> ADVal ranked r n
indexPrimal (D u u') ix = dD (rindex u ix) (IndexR u' ix)

fromList :: (RankedTensor ranked, KnownNat n, GoodScalar r)
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (rfromList $ map (\(D u _) -> u) lu)
     (FromListR $ map (\(D _ u') -> u') lu)

instance ( RankedTensor ranked, IfF (RankedOf (PrimalOf ranked))
         , Boolean (BoolOf ranked)
         , BoolOf (RankedOf (PrimalOf ranked)) ~ BoolOf ranked )
         => IfF (ADVal ranked) where
  ifF b v w =
    let D u u' = indexPrimal (fromList [v, w])
                             (singletonIndex $ ifF b 0 1)
    in dDnotShared u u'

indexPrimalS :: ( ShapedTensor shaped, GoodScalar r
                , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape (sh1 Sh.++ sh2) )
             => ADVal shaped r (sh1 Sh.++ sh2) -> IndexSh shaped sh1
             -> ADVal shaped r sh2
indexPrimalS (D u u') ix = dD (sindex u ix) (IndexS u' ix)

fromListS :: forall n sh shaped r.
             (ShapedTensor shaped, KnownNat n, Sh.Shape sh, GoodScalar r)
           => [ADVal shaped r sh]
           -> ADVal shaped r (n ': sh)
fromListS lu = assert (length lu == valueOf @n) $
  dD (sfromList $ map (\(D u _) -> u) lu)
     (FromListS $ map (\(D _ u') -> u') lu)

instance ( ShapedTensor shaped, IfF (RankedOf (PrimalOf shaped))
         , Boolean (BoolOf shaped)
         , BoolOf (RankedOf (PrimalOf shaped)) ~ BoolOf shaped )
         => IfF (ADVal shaped) where
  ifF b v w =
    let D u u' = indexPrimalS (fromListS @2 [v, w])
                              (ShapedList.singletonIndex
                               $ ifF b 0 1)
    in dDnotShared u u'

{- TODO: use for speed-up, e.g,. by checking the type at runtime
instance IfF (ADVal (Flip OR.Array)) where
  ifF (_, b) v w = if b then v else w

instance IfF (ADVal (Flip OS.Array)) where
  ifF (_, b) v w = if b then v else w
-}

type instance RankedOf (ADVal f) = ADVal (RankedOf f)

type instance ShapedOf (ADVal f) = ADVal (ShapedOf f)

type instance HVectorOf (ADVal f) = HVector (ADVal f)

type instance HFunOf (ADVal f) = HFun

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Dual f


-- * Numeric instances

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f r z) where
  (==) = error "AST requires that EqB be used instead"
  (/=) = error "AST requires that EqB be used instead"

instance Ord (ADVal f r z) where
  (<=) = error "AST requires that OrdB be used instead"

instance (Num (f r z), IsPrimal f r z)
         => Num (ADVal f r z) where
  -- The 0 cases are needed to get GHC 9.6 to use the specialization
  -- (only at rank 0, though; we'd need many more for common ranks and shapes).
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance Num (ADVal (Flip OR.Array) Double 0) #-}
  {-# SPECIALIZE instance Num (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (Flip OR.Array) Double n) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' =
    dD (u - v) (dAdd u' (dScale (intOfShape v (-1)) v'))
  D ue u' * D ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (intOfShape v (-1)) v')
  abs (D ve v') = let !v = sharePrimal ve
                  in dD (abs v) (dScale (signum v) v')
  signum (D v _) = dD (signum v) (dZeroOfShape v)
  fromInteger = constantADVal . fromInteger

instance (Real (f r z), IsPrimal f r z)
         => Real (ADVal f r z) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (ADVal f r z) where  -- dummy, to satisfy Integral below
  toEnum = undefined
  fromEnum = undefined

instance (Integral (f r z), IsPrimal f r z)
         => Integral (ADVal f r z) where
  quot (D u _) (D v _) = dD (quot u v) (dZeroOfShape u)
  rem (D u _) (D v _) = dD (rem u v) (dZeroOfShape u)
  quotRem x y = (quot x y, rem x y)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Fractional (f r z), IsPrimal f r z)
         => Fractional (ADVal f r z) where
{- TODO: this causes a cyclic dependency:
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
-}
  D ue u' / D ve v' =
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD (u / v)
          (dAdd (dScale (recip v) u') (dScale ((- u) / (v * v)) v'))
  recip (D ve v') =
    let !v = sharePrimal ve
        minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = constantADVal . fromRational

instance (Floating (f r z), IsPrimal f r z)
         => Floating (ADVal f r z) where
{- TODO: this causes a cyclic dependency:
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
-}
  pi = constantADVal pi
  exp (D ue u') = let !expU = sharePrimal (exp ue)
                  in dD expU (dScale expU u')
  log (D ue u') = let !u = sharePrimal ue
                  in dD (log u) (dScale (recip u) u')
  sqrt (D ue u') = let !sqrtU = sharePrimal (sqrt ue)
                   in dD sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D ue u' ** D ve v' =
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v 1))) u')
                         (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D ue u') = let !u = sharePrimal ue
                  in dD (sin u) (dScale (cos u) u')
  cos (D ue u') = let !u = sharePrimal ue
                  in dD (cos u) (dScale (- (sin u)) u')
  tan (D ue u') = let !u = sharePrimal ue in
                  let !cosU = sharePrimal (cos u)
                  in dD (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D ue u') = let !u = sharePrimal ue
                   in dD (asin u)
                         (dScale (recip (sqrt (intOfShape u 1 - u * u))) u')
  acos (D ue u') = let !u = sharePrimal ue
                   in dD (acos u)
                         (dScale (- recip (sqrt (intOfShape u 1 - u * u))) u')
  atan (D ue u') = let !u = sharePrimal ue
                   in dD (atan u)
                         (dScale (recip (intOfShape u 1 + u * u)) u')
  sinh (D ue u') = let !u = sharePrimal ue
                   in dD (sinh u) (dScale (cosh u) u')
  cosh (D ue u') = let !u = sharePrimal ue
                   in dD (cosh u) (dScale (sinh u) u')
  tanh (D ue u') = let !y = sharePrimal (tanh ue)
                   in dD y (dScale (intOfShape y 1 - y * y) u')
  asinh (D ue u') = let !u = sharePrimal ue
                    in dD (asinh u)
                          (dScale (recip (sqrt (intOfShape u 1 + u * u))) u')
  acosh (D ue u') = let !u = sharePrimal ue
                    in dD (acosh u)
                          (dScale (recip (sqrt (u * u - intOfShape u 1))) u')
  atanh (D ue u') = let !u = sharePrimal ue
                    in dD (atanh u)
                          (dScale (recip (intOfShape u 1 - u * u)) u')

instance (RealFrac (f r z), IsPrimal f r z)
         => RealFrac (ADVal f r z) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat (f r z), IsPrimal f r z)
         => RealFloat (ADVal f r z) where
{- TODO: this causes a cyclic dependency:
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
-}
  atan2 (D ue u') (D ve v') =
    let !u = sharePrimal ue in
    let !v = sharePrimal ve in
    let !t = sharePrimal (recip (u * u + v * v))
    in dD (atan2 u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))
  -- Note that for term types @a@ this is invalid without an extra let
  -- containing the first field of @D@. However, for terms this is
  -- unimplemented anyway.
  floatRadix (D u _) = floatRadix u
  floatDigits (D u _) = floatDigits u
  floatRange (D u _) = floatRange u
  decodeFloat (D u _) = decodeFloat u
  encodeFloat i j = constantADVal (encodeFloat i j)
  isNaN (D u _) = isNaN u
  isInfinite (D u _) = isInfinite u
  isDenormalized (D u _) = isDenormalized u
  isNegativeZero (D u _) = isNegativeZero u
  isIEEE (D u _) = isIEEE u
