{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them.
module HordeAd.Core.DualNumber
  ( -- * The main dual number type
    ADVal, dD, pattern D, dDnotShared, constantADVal
    -- * Auxiliary definitions
  , indexPrimal, fromVector, indexPrimalS, fromVectorS
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , generateDeltaInputs, makeADInputs, ahhToHVector
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+))

import Data.Array.Mixed.Types qualified as X

import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.IsPrimal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList (IndexSh)
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The main dual number type

-- | Values that the objective functions operate on when they are being
-- differentiated. The values are, in general, tensors.
-- The first type argument is the functor determining the structure
-- of the tensors (whether ranked, shaped, dynamic, storable, unboxed, etc.).
-- The second argument is the underlying scalar type. The third
-- is the rank or shape of the tensor value.
--
-- The datatype is implemented as dual numbers (hence @D@).,
-- The @f r z@ value is the primal component, which is the normal,
-- the basic value. The exact type of the dual component
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
  :: forall x ranked ranked2.
     ( x ~ TKUntyped, RankedTensor ranked, HVectorTensor ranked (ShapedOf ranked)
     , RankedOf (ShapedOf ranked2) ~ ranked2 )
  => InterpretationTarget ranked x
  -> InterpretationTarget (Dual ranked2) x
generateDeltaInputs =
  let f :: Int -> DynamicTensor ranked -> DynamicTensor (Dual ranked2)
      f i (DynamicRanked @r @n t) =
        case rshape t of
          (sh :: IShR n2) | Just Refl <- sameNat (Proxy @n) (Proxy @n2) ->
            DynamicRanked $ DeltaR $ InputR @ranked2 @r @n sh (toInputIdR i)
          _ -> error "generateDeltaInputs: wrong rank"
      f i (DynamicShaped @r @sh _) =
        DynamicShaped $ DeltaS $ InputS @ranked2 @r @sh (toInputIdS i)
      f i (DynamicRankedDummy @r @sh _ _) =
        withListSh (Proxy @sh) $ \sh ->
          DynamicRanked $ DeltaR $ InputR @ranked2 @r sh (toInputIdR i)
      f i (DynamicShapedDummy @r @sh _ _) =
        DynamicShaped $ DeltaS $ InputS @ranked2 @r @sh (toInputIdS i)
  in HVectorPseudoTensor . HToH . V.imap f . dunHVector . unHVectorPseudoTensor
       -- dunHVector is fine, because p is made with dmkHVector
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE generateDeltaInputs
  :: HVector (FlipR OR.Array) -> HVector (Dual (FlipR OR.Array)) #-}
-}

makeADInputs
  :: forall x ranked.
     ( TensorKind x, HVectorTensor ranked (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => InterpretationTarget ranked x -> InterpretationTarget (Dual ranked) x
  -> InterpretationTarget (ADVal ranked) x
makeADInputs p0 d0 =
  let g :: STensorKindType y
        -> InterpretationTarget ranked y -> InterpretationTarget (Dual ranked) y
        -> InterpretationTarget (ADVal ranked) y
      g STKR{} p d = dDnotShared p d
      g STKS{} p d = dDnotShared p d
      g (STKProduct stk1 stk2) p d =
        (g stk1 (fst p) (fst d), g stk2 (snd p) (snd d))
      g STKUntyped p d =
        HVectorPseudoTensor
        $ ahhToHVector (dunHVector $ unHVectorPseudoTensor p)
                       (unHVectorPseudoTensor d)
            -- dunHVector is fine, because p is made with dmkHVector
  in g (stensorKind @x) p0 d0

ahhToHVector
  :: forall ranked. RankedOf (ShapedOf ranked) ~ ranked
  => HVector ranked -> Delta ranked TKUntyped -> HVector (ADVal ranked)
ahhToHVector h h' =
  let selectDual :: Int -> DynamicTensor ranked -> DynamicTensor (ADVal ranked)
      selectDual i d = case d of
        DynamicRanked t -> DynamicRanked $ dDnotShared t (DeltaR $ RFromH h' i)
        DynamicShaped t -> DynamicShaped $ dDnotShared t (DeltaS $ SFromH h' i)
        DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
        DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
  in V.imap selectDual h
       -- TODO: write why these projections don't break any sharing


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
indexPrimal (D u u') ix = dD (rindex u ix) (DeltaR $ IndexR (unDeltaR u') ix)

fromVector :: (RankedTensor ranked, KnownNat n, GoodScalar r)
           => Data.Vector.Vector (ADVal ranked r n)
           -> ADVal ranked r (1 + n)
fromVector lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (rfromVector $ V.map (\(D u _) -> u) lu)
     (DeltaR $ FromVectorR $ V.map (\(D _ u') -> unDeltaR u') lu)

instance ( RankedTensor ranked, IfF (RankedOf (PrimalOf ranked))
         , Boolean (BoolOf ranked)
         , BoolOf (RankedOf (PrimalOf ranked)) ~ BoolOf ranked )
         => IfF (ADVal ranked) where
  ifF !b !v !w =  -- bangs for the proper order of sharing stamps
    let D u u' = indexPrimal (fromVector $ V.fromList [v, w])
                             (singletonIndex $ ifF b 0 1)
    in dDnotShared u u'

indexPrimalS :: ( ShapedTensor shaped, GoodScalar r
                , KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2) )
             => ADVal shaped r (sh1 X.++ sh2) -> IndexSh shaped sh1
             -> ADVal shaped r sh2
indexPrimalS (D u u') ix = dD (sindex u ix) (DeltaS $ IndexS (unDeltaS u') ix)

fromVectorS :: forall n sh shaped r.
               (ShapedTensor shaped, KnownNat n, KnownShS sh, GoodScalar r)
            => Data.Vector.Vector (ADVal shaped r sh)
            -> ADVal shaped r (n ': sh)
fromVectorS lu = assert (length lu == valueOf @n) $
  dD (sfromVector $ V.map (\(D u _) -> u) lu)
     (DeltaS $ FromVectorS $ V.map (\(D _ u') -> unDeltaS u') lu)

instance ( ShapedTensor shaped, IfF (RankedOf (PrimalOf shaped))
         , Boolean (BoolOf shaped)
         , BoolOf (RankedOf (PrimalOf shaped)) ~ BoolOf shaped )
         => IfF (ADVal shaped) where
  ifF !b !v !w =  -- bangs for the proper order of sharing stamps
    let D u u' = indexPrimalS (fromVectorS @2 $ V.fromList [v, w])
                              (ShapedList.singletonIndex
                               $ ifF b 0 1)
    in dDnotShared u u'

{- TODO: use for speed-up, e.g,. by checking the type at runtime
instance IfF (ADVal (FlipR OR.Array)) where
  ifF (_, b) v w = if b then v else w

instance IfF (ADVal (FlipS OS.Array)) where
  ifF (_, b) v w = if b then v else w
-}

type instance RankedOf (ADVal f) = ADVal (RankedOf f)

type instance ShapedOf (ADVal f) = ADVal (ShapedOf f)

type instance HVectorOf (ADVal f) = HVector (ADVal f)

type instance HFunOf (ADVal f) x y = HFun x y

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
  {-# SPECIALIZE instance Num (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance Num (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance KnownNat n
                          => Num (ADVal (FlipR OR.Array) Double n) #-}
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

instance (IntegralF (f r z), IsPrimal f r z)
         => IntegralF (ADVal f r z) where
  quotF (D u _) (D v _) = dD (quotF u v) (dZeroOfShape u)
  remF (D u _) (D v _) = dD (remF u v) (dZeroOfShape u)

instance (Fractional (f r z), IsPrimal f r z)
         => Fractional (ADVal f r z) where
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      Fractional (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Fractional (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Fractional (ADVal (FlipR OR.Array) Double n) #-}
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
      Floating (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      Floating (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => Floating (ADVal (FlipR OR.Array) Double n) #-}
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

instance (Fractional (f r z), RealFloatF (f r z), IsPrimal f r z)
         => RealFloatF (ADVal f r z) where
  atan2F (D ue u') (D ve v') =
    let !u = sharePrimal ue in
    let !v = sharePrimal ve in
    let !t = sharePrimal (recip (u * u + v * v))
    in dD (atan2F u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))

instance (RealFloat (f r z), IsPrimal f r z)
         => RealFloat (ADVal f r z) where
{- TODO: this causes a cyclic dependency:
  {-# SPECIALIZE instance
      RealFloat (ADVal (FlipR OR.Array) Double 0) #-}
  {-# SPECIALIZE instance
      RealFloat (ADVal (AstRanked PrimalSpan) Double 0) #-}
  {-# SPECIALIZE instance
      KnownNat n
      => RealFloat (ADVal (FlipR OR.Array) Double n) #-}
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
