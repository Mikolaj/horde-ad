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
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Product
import           Data.Functor.Const
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
  ADVal ADShare (f r z) (Dual f r z)

pattern D :: ADShare -> f r z -> Dual f r z -> ADVal f r z
pattern D l t u <- ADVal l t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f r z), Show (Dual f r z))
                  => Show (ADVal f r z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: IsPrimal f r z
   => ADShare -> f r z -> Dual f r z -> ADVal f r z
dD !l !a !dual = dDnotShared l a (shareDual dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: ADShare -> f r z -> Dual f r z -> ADVal f r z
dDnotShared = ADVal


-- * Auxiliary definitions

constantADVal :: IsPrimal f r z => f r z -> ADVal f r z
constantADVal a = dDnotShared emptyADShare a (dZeroOfShape a)

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
          DynamicRanked $ dDnotShared emptyADShare t d
      f (DynamicShaped @r @sh t) (DynamicShaped @r2 @sh2 d)
        | Just Refl <- sameShape @sh @sh2
        , Just Refl <- testEquality (typeRep @r) (typeRep @r2) =
          DynamicShaped $ dDnotShared emptyADShare t d
      f _ _ = error "makeADInputs: non-matching arguments"
  in V.zipWith f


-- * Assorted instances

type instance SimpleBoolOf (ADVal f) = SimpleBoolOf f

instance EqF f => EqF (ADVal f) where
  D l1 u _ ==. D l2 v _ = (l1 `mergeADShare` l2, snd $ u ==. v)
  D l1 u _ /=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u /=. v)

instance OrdF f => OrdF (ADVal f) where
  D l1 u _ <. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <. v)
  D l1 u _ <=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u <=. v)
  D l1 u _ >. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >. v)
  D l1 u _ >=. D l2 v _ = (l1 `mergeADShare` l2, snd $ u >=. v)

indexPrimal :: (RankedTensor ranked, KnownNat m, KnownNat n, GoodScalar r)
            => ADVal ranked r (m + n) -> IndexOf ranked m
            -> ADVal ranked r n
indexPrimal (D l u u') ix = dD l (rindex u ix) (IndexR u' ix)

fromList :: (RankedTensor ranked, KnownNat n, GoodScalar r)
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (rfromList $ map (\(D _ u _) -> u) lu)
     (FromListR $ map (\(D _ _ u') -> u') lu)

instance ( RankedTensor ranked, IfF (RankedOf (PrimalOf ranked))
         , Boolean (SimpleBoolOf ranked)
         , SimpleBoolOf (RankedOf (PrimalOf ranked)) ~ SimpleBoolOf ranked )
         => IfF (ADVal ranked) where
  ifF (l1, b) v w =
    let D l2 u u' = indexPrimal (fromList [v, w])
                                (singletonIndex $ ifF (emptyADShare, b) 0 1)
    in dDnotShared (l1 `mergeADShare` l2) u u'

indexPrimalS :: ( ShapedTensor shaped, GoodScalar r
                , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape (sh1 Sh.++ sh2) )
             => ADVal shaped r (sh1 Sh.++ sh2) -> IndexSh shaped sh1
             -> ADVal shaped r sh2
indexPrimalS (D l u u') ix = dD l (sindex u ix) (IndexS u' ix)

fromListS :: forall n sh shaped r.
             (ShapedTensor shaped, KnownNat n, Sh.Shape sh, GoodScalar r)
           => [ADVal shaped r sh]
           -> ADVal shaped r (n ': sh)
fromListS lu = assert (length lu == valueOf @n) $
  dD (flattenADShare $ map (\(D l _ _) -> l) lu)
     (sfromList $ map (\(D _ u _) -> u) lu)
     (FromListS $ map (\(D _ _ u') -> u') lu)

instance ( ShapedTensor shaped, IfF (RankedOf (PrimalOf shaped))
         , Boolean (SimpleBoolOf shaped)
         , SimpleBoolOf (RankedOf (PrimalOf shaped)) ~ SimpleBoolOf shaped )
         => IfF (ADVal shaped) where
  ifF (l1, b) v w =
    let D l2 u u' = indexPrimalS (fromListS @2 [v, w])
                                 (ShapedList.singletonIndex
                                  $ ifF (emptyADShare, b) 0 1)
    in dDnotShared (l1 `mergeADShare` l2) u u'

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

type instance DualOf (ADVal f) = Product (Clown (Const ADShare)) (Dual f)


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
  D l1 u u' + D l2 v v' = dD (l1 `mergeADShare` l2) (u + v) (dAdd u' v')
  D l1 u u' - D l2 v v' =
    dD (l1 `mergeADShare` l2) (u - v) (dAdd u' (dScale (intOfShape v (-1)) v'))
  D l1 ue u' * D l2 ve v' =
    -- The bangs are neccessary for GHC 9.2.7 test results to match 9.4.
    let !l3 = l1 `mergeADShare` l2 in
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD l3 (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D l v v') = dD l (negate v) (dScale (intOfShape v (-1)) v')
  abs (D l ve v') = let !v = sharePrimal ve
                    in dD l (abs v) (dScale (signum v) v')
  signum (D l v _) = dD l (signum v) (dZeroOfShape v)
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
  quot (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (quot u v) (dZeroOfShape u)
  rem (D l1 u _) (D l2 v _) =
    dD (l1 `mergeADShare` l2) (rem u v) (dZeroOfShape u)
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
  D l1 ue u' / D l2 ve v' =
    let !l3 = l1 `mergeADShare` l2 in
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD l3 (u / v)
             (dAdd (dScale (recip v) u') (dScale ((- u) / (v * v)) v'))
  recip (D l ve v') =
    let !v = sharePrimal ve
        minusRecipSq = - recip (v * v)
    in dD l (recip v) (dScale minusRecipSq v')
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
  exp (D l ue u') = let !expU = sharePrimal (exp ue)
                    in dD l expU (dScale expU u')
  log (D l ue u') = let !u = sharePrimal ue
                    in dD l (log u) (dScale (recip u) u')
  sqrt (D l ue u') = let !sqrtU = sharePrimal (sqrt ue)
                     in dD l sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D l1 ue u' ** D l2 ve v' =
    let !l3 = l1 `mergeADShare` l2 in
    let !u = sharePrimal ue in
    let !v = sharePrimal ve
    in dD l3 (u ** v) (dAdd (dScale (v * (u ** (v - intOfShape v 1))) u')
                            (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D l ue u') = let !u = sharePrimal ue
                    in dD l (sin u) (dScale (cos u) u')
  cos (D l ue u') = let !u = sharePrimal ue
                    in dD l (cos u) (dScale (- (sin u)) u')
  tan (D l ue u') = let !u = sharePrimal ue in
                    let !cosU = sharePrimal (cos u)
                    in dD l (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D l ue u') = let !u = sharePrimal ue
                     in dD l (asin u)
                           (dScale (recip (sqrt (intOfShape u 1 - u * u))) u')
  acos (D l ue u') = let !u = sharePrimal ue
                     in dD l (acos u)
                           (dScale (- recip (sqrt (intOfShape u 1 - u * u))) u')
  atan (D l ue u') = let !u = sharePrimal ue
                     in dD l (atan u)
                           (dScale (recip (intOfShape u 1 + u * u)) u')
  sinh (D l ue u') = let !u = sharePrimal ue
                     in dD l (sinh u) (dScale (cosh u) u')
  cosh (D l ue u') = let !u = sharePrimal ue
                     in dD l (cosh u) (dScale (sinh u) u')
  tanh (D l ue u') = let !y = sharePrimal (tanh ue)
                     in dD l y (dScale (intOfShape y 1 - y * y) u')
  asinh (D l ue u') = let !u = sharePrimal ue
                      in dD l (asinh u)
                            (dScale (recip (sqrt (intOfShape u 1 + u * u))) u')
  acosh (D l ue u') = let !u = sharePrimal ue
                      in dD l (acosh u)
                            (dScale (recip (sqrt (u * u - intOfShape u 1))) u')
  atanh (D l ue u') = let !u = sharePrimal ue
                      in dD l (atanh u)
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
  atan2 (D l1 ue u') (D l2 ve v') =
    let !l3 = l1 `mergeADShare` l2 in
    let !u = sharePrimal ue in
    let !v = sharePrimal ve in
    let !t = sharePrimal (recip (u * u + v * v))
    in dD l3 (atan2 u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))
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
