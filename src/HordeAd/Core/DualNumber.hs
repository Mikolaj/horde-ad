{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and arithmetic operations on them.
module HordeAd.Core.DualNumber
  ( -- * The main dual number type
    ADVal, pattern D, dD, dDnotShared, constantADVal
    -- * Auxiliary definitions
  , indexPrimal, fromVector, indexPrimalS, fromVectorS, indexPrimalX, fromVectorX
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
--  , addParameters, dotParameters
  , generateDeltaInputs, makeADInputs, ahhToHVector
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, sameNat, type (+))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape (ssxFromShape)
import Data.Array.Nested (KnownShX, type (++))
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.IsPrimal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList (IndexSh, IndexShX)
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
-- The @f z@ value is the primal component, which is the normal,
-- the basic value.
type role ADVal nominal nominal
data ADVal (f :: Target) y = ADVal (f y) (Delta f y)

pattern D :: f z -> Delta f z -> ADVal f z
pattern D t u <- ADVal t u  -- enforces only pattern matching
{-# COMPLETE D #-}

deriving instance (Show (f z), Show (Delta f z))
                  => Show (ADVal f z)

-- | Smart constructor for 'D' of 'ADVal' that additionally records delta
-- expression sharing information (regardless if the basic value
-- of the dual number is an AST term or not).
-- The bare constructor should not be used directly (which is not enforced
-- by the types yet), except when deconstructing via pattern-matching.
dD :: forall f z. IsPrimal f z
   => f z -> Delta f z -> ADVal f z
dD !a !dual = dDnotShared a (shareDual dual)

-- | This a not so smart a constructor for 'D' of 'ADVal' that does not record
-- sharing information. If used in contexts where sharing may occur,
-- it may cause exponential blowup when evaluating the term
-- in backpropagation phase. In contexts without sharing, it saves
-- some evaluation time and memory (in term structure, but even more
-- in the per-node data stored while evaluating).
dDnotShared :: f z -> Delta f z -> ADVal f z
dDnotShared = ADVal


-- * Auxiliary definitions

constantADVal :: IsPrimal f z => f z -> ADVal f z
constantADVal a = dDnotShared a (dZeroOfShape a)

-- | Add sharing information to the top level of a term, presumably
-- constructed using multiple applications of the `dDnotShared` operation.
-- The resulting term may not have sharing information inside,
-- but is ready to be shared as a whole.
ensureToplevelSharing :: IsPrimal f z => ADVal f z -> ADVal f z
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num (f z), IsPrimal f z)
               => f z -> ADVal f z -> ADVal f z
scaleNotShared !a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: forall f z. (Num (f z), IsPrimal f z)
             => ADVal f z -> ADVal f z -> ADVal f z
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: forall f z. (Num (f z), IsPrimal f z)
              => ADVal f z -> ADVal f z -> ADVal f z
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))
{-
addParameters :: (DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> HVector r
addParameters (HVector a0 a1) (HVector b0 b1) =
  HVector (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: (DTensorOf r ~ OD.Array r)
              => HVector r -> HVector r -> r
dotParameters (HVector a0 a1) (HVector b0 b1) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)
-}

generateDeltaInputs
  :: forall x target.
     TensorKindFull x -> Delta target x
generateDeltaInputs =
  let gen :: Int -> TensorKindFull y -> (Delta target y, Int)
      gen j ftk = case ftk of
        FTKScalar -> (InputG ftk (toInputId j), j + 1)
        FTKR sh | SNat <- shrRank sh -> (InputG ftk (toInputId j), j + 1)
        FTKS sh -> withKnownShS sh $ (InputG ftk (toInputId j), j + 1)
        FTKX sh -> withKnownShX (ssxFromShape sh)
                   $ (InputG ftk (toInputId j), j + 1)
        FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                             , Dict <- lemTensorKindOfF ftk2 ->
          let (d1, j1) = gen j ftk1
              (d2, j2) = gen j1 ftk2
          in (PairG d1 d2, j2)
        FTKUntyped shs ->
          let f :: (Int, DynamicTensor VoidTensor) -> DynamicTensor (Delta target)
              f (i, DynamicRankedDummy @r @sh _ _) =
                withListSh (Proxy @sh) $ \sh ->
                  DynamicRanked $ InputG (FTKR @r sh) (toInputId i)
              f (i, DynamicShapedDummy @r @sh _ _) =
                DynamicShaped $ InputG (FTKS @r @sh knownShS) (toInputId i)
              len = V.length shs
          in (HToH $ V.map f $ V.zip (V.enumFromN j len) shs, j + len)
  in fst . gen 0
{- TODO: this causes a cyclic dependency:
{-# SPECIALIZE generateDeltaInputs
  :: HVector (FlipR OR.Array) -> HVector (Delta (FlipR OR.Array)) #-}
-}

makeADInputs
  :: target x -> Delta target x
  -> ADVal target x
makeADInputs = dDnotShared  -- not dD, because generateDeltaInputs has only inputs and containers; TODO: join makeADInputs and generateDeltaInputs?

ahhToHVector  -- TODO: remove?
  :: forall target.
     HVector target -> Delta target TKUntyped -> HVector (ADVal target)
ahhToHVector h hNotShared' =
  let h' = case hNotShared' of
        HToH{} -> hNotShared'
        _ -> shareDelta hNotShared'
      selectDual :: Int -> DynamicTensor target -> DynamicTensor (ADVal target)
      selectDual i d = case d of
        DynamicRanked t -> DynamicRanked $ dDnotShared t (rFromH h' i)
        DynamicShaped t -> DynamicShaped $ dDnotShared t (sFromH h' i)
        DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
        DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
  in V.imap selectDual h

rFromH :: forall r n target. (GoodScalar r, KnownNat n)
       => Delta target TKUntyped -> Int -> Delta target (TKR r n)
rFromH (HToH hv) i = case hv V.! i of
  DynamicRanked @r2 @n2 d
    | Just Refl <- sameNat (Proxy @n) (Proxy @n2)
    , Just Refl <- testEquality (typeRep @r) (typeRep @r2) -> d
  DynamicRankedDummy @r2 @sh _ _
    | Just Refl <- matchingRank @sh @n
    , Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
      ZeroG (FTKR $ fromList $ shapeT @sh)
  _ -> error "rFromH: impossible case"
rFromH (ZeroG (FTKUntyped shs)) i = case shs V.! i of
  DynamicRankedDummy @_ @sh _ _ -> ZeroG (FTKR $ fromList $ shapeT @sh)
  DynamicShapedDummy{} -> error "rFromH: DynamicShapedDummy"
rFromH d i = RFromH d i

sFromH :: forall r sh target. (GoodScalar r, KnownShS sh)
       => Delta target TKUntyped -> Int -> Delta target (TKS r sh)
sFromH (HToH hv) i = case hv V.! i of
  DynamicShaped @r2 @sh2 d
    | Just Refl <- sameShape @sh @sh2
    , Just Refl <- testEquality (typeRep @r) (typeRep @r2) -> d
  DynamicShapedDummy @r2 @sh3 _ _
    | Just Refl <- sameShape @sh @sh3
    , Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
      ZeroG (FTKS $ fromList $ shapeT @sh3)
  _ -> error "sFromH: impossible case"
sFromH (ZeroG (FTKUntyped shs)) i = case shs V.! i of
  DynamicRankedDummy{} -> error "sFromH: DynamicRankedDummy"
  DynamicShapedDummy @_ @sh3 _ _ -> ZeroG (FTKS $ fromList $ shapeT @sh3)
sFromH d i = SFromH d i


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

indexPrimal :: ( ADReadyNoLet target, ShareTensor target
               , KnownNat m, KnownNat n, GoodScalar r )
            => ADVal target (TKR r (m + n)) -> IndexOf target m
            -> ADVal target (TKR r n)
indexPrimal (D u u') ix = dD (rindex u ix) (IndexR u' ix)

fromVector :: ( ADReadyNoLet target, ShareTensor target
              , KnownNat n, GoodScalar r )
           => Data.Vector.Vector (ADVal target (TKR r n))
           -> ADVal target (TKR r (1 + n))
fromVector lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (rfromVector $ V.map (\(D u _) -> u) lu)
     (FromVectorR $ V.map (\(D _ u') -> u') lu)

instance ( ADReadyNoLet target, ShareTensor target
         , BoolOf (PrimalOf target) ~ BoolOf target )
         => IfF (ADVal target) where
  ifF :: forall y. TensorKind y
      => BoolOf target -> ADVal target y -> ADVal target y -> ADVal target y
  ifF !b !v !w = case stensorKind @y of  -- bangs for the proper order of sharing stamps
    STKR STKScalar{} SNat ->
      indexPrimal (fromVector $ V.fromList [v, w])
                  (fromList [ifF b 0 1])
    STKS STKScalar{} sh -> withKnownShS sh $
      indexPrimalS @_ @_ @'[2]
                   (fromVectorS $ V.fromList [v, w])
                   (fromList [ifF b 0 1])
    STKX STKScalar{} sh -> withKnownShX sh $
      indexPrimalX @_ @_ @'[Just 2]
                   (fromVectorX $ V.fromList [v, w])
                   (fromList [ifF b 0 1])
    _ -> error "TODO"

indexPrimalS :: ( ADReadyNoLet target, ShareTensor target
                , GoodScalar r, KnownShS sh1, KnownShS sh2
                , KnownShS (sh1 ++ sh2) )
             => ADVal target (TKS r (sh1 ++ sh2)) -> IndexSh target sh1
             -> ADVal target (TKS r sh2)
indexPrimalS (D u u') ix = dD (sindex u ix) (IndexS u' ix)

fromVectorS :: forall n sh target r.
               ( ADReadyNoLet target, ShareTensor target
               , KnownNat n, KnownShS sh, GoodScalar r )
            => Data.Vector.Vector (ADVal target (TKS r sh))
            -> ADVal target (TKS r (n ': sh))
fromVectorS lu = assert (length lu == valueOf @n) $
  dD (sfromVector $ V.map (\(D u _) -> u) lu)
     (FromVectorS $ V.map (\(D _ u') -> u') lu)

indexPrimalX :: ( ADReadyNoLet target, ShareTensor target
                , GoodScalar r, KnownShX sh1, KnownShX sh2
                , KnownShX (sh1 ++ sh2) )
             => ADVal target (TKX r (sh1 ++ sh2)) -> IndexShX target sh1
             -> ADVal target (TKX r sh2)
indexPrimalX (D u u') ix = dD (xindex u ix) (IndexX u' ix)

fromVectorX :: forall n sh target r.
               ( ADReadyNoLet target, ShareTensor target
               , KnownNat n, KnownShX sh, GoodScalar r )
            => Data.Vector.Vector (ADVal target (TKX r sh))
            -> ADVal target (TKX r (Just n ': sh))
fromVectorX lu = assert (length lu == valueOf @n) $
  dD (xfromVector $ V.map (\(D u _) -> u) lu)
     (FromVectorX $ V.map (\(D _ u') -> u') lu)

{- TODO: use for speed-up, e.g,. by checking the type at runtime
instance IfF (ADVal (FlipR OR.Array)) where
  ifF (_, b) v w = if b then v else w

instance IfF (ADVal (FlipS OS.Array)) where
  ifF (_, b) v w = if b then v else w
-}

type instance HFunOf (ADVal f) x y = HFun x y

type instance PrimalOf (ADVal f) = f

type instance DualOf (ADVal f) = Delta f

type instance ShareOf (ADVal f) = ADVal f


-- * Numeric instances

-- These two instances are required for the numeric tensor instances.
-- They can't be made valid for AST, because they require interpretation before
-- they can be compared with an instant Bool result, so let's fail early
-- also here.
instance Eq (ADVal f z) where
  (==) = error "AST requires that EqB be used instead"
  (/=) = error "AST requires that EqB be used instead"

instance Ord (ADVal f z) where
  (<=) = error "AST requires that OrdB be used instead"

instance (Num (f z), IsPrimal f z)
         => Num (ADVal f z) where
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

instance (Real (f z), IsPrimal f z)
         => Real (ADVal f z) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (IntegralF (f z), IsPrimal f z)
         => IntegralF (ADVal f z) where
  quotF (D u _) (D v _) = dD (quotF u v) (dZeroOfShape u)
  remF (D u _) (D v _) = dD (remF u v) (dZeroOfShape u)

instance (Fractional (f z), IsPrimal f z)
         => Fractional (ADVal f z) where
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

instance (Floating (f z), IsPrimal f z)
         => Floating (ADVal f z) where
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

instance (RealFrac (f z), IsPrimal f z)
         => RealFrac (ADVal f z) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Fractional (f z), RealFloatF (f z), IsPrimal f z)
         => RealFloatF (ADVal f z) where
  atan2F (D ue u') (D ve v') =
    let !u = sharePrimal ue in
    let !v = sharePrimal ve in
    let !t = sharePrimal (recip (u * u + v * v))
    in dD (atan2F u v) (dAdd (dScale ((- u) * t) v') (dScale (v * t) u'))

instance (RealFloat (f z), IsPrimal f z)
         => RealFloat (ADVal f z) where
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
