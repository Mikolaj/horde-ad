{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | This is a shim module provided exclusively to use old tests.
module HordeAd.Core.DualNumber2
  ( ADVal, dD, pattern D, Dual
  , ADModeAndNum, HasDelta
  , fromX1, from1X
  , Vec, vecToV, vToVec
  , SNat(..), staticNatValue, staticNatFromProxy
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
  , addParameters, dotParameters
  , sumElements10, index10, minimum0, maximum0
  , (<.>!), (<.>!!)
  , fromList1, fromVector1, konst1, append1, slice1, reverse1
  , build1Elementwise, build1Closure
  , map1Elementwise
  , -- * Re-exports
    ADMode(..)
  , IsPrimal, IsPrimalWithScalar, IsPrimalAndHasFeatures, IsPrimalAndHasInputs
  , Domain0, DomainR, Domains
  , domains0, domainsR, mkDomains
  , Domain1, domains1
  , ADInputs
  , at0, at1, ifoldlDual', foldlDual'
  , domainsFromD01, domainsFrom01, domainsFrom0V
  , listsToParameters, listsToParameters4, domainsD0
  , valueGeneral, valueOnDomains, revOnADInputs, revOnDomains, prettyPrintDf
  , constant, scale, logistic, altSumElements10
  , softMax, softMaxV, lossCrossEntropy, lossCrossEntropyV
  , lossSoftMaxCrossEntropyV, relu
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Boolean
import           Data.Functor.Compose
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Text.Show.Pretty (ppShow)

import           HordeAd.Core.Ast
import           HordeAd.Core.Delta (Delta0, ForwardDerivative)
import           HordeAd.Core.Domains
import           HordeAd.Core.DualClass hiding (IsPrimal)
import qualified HordeAd.Core.DualClass as DualClass
import           HordeAd.Core.DualNumber (ADTensor, dD, dDnotShared)
import qualified HordeAd.Core.DualNumber as DualNumber
import qualified HordeAd.Core.Engine as Engine
import           HordeAd.Core.SizedIndex
import qualified HordeAd.Core.TensorADVal as TensorADVal
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.TensorOps

type IsPrimalWithScalarNew a r = (DualClass.IsPrimal a, Scalar a ~ r)

pattern D :: a -> Dual a -> DualNumber.ADVal a
pattern D u u' <- DualNumber.D _ u u'
{-# COMPLETE D #-}

type Domain1 r = DomainR r

domains1 :: DomainsCollection r => Domains r -> Domain1 r
domains1 = domainsR

type ADInputs d r = Domains (DualNumber.ADVal r)

data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue
  deriving Show

type ADVal (d :: ADMode) a = DualNumber.ADVal a

type IsPrimal (d :: ADMode) a =
  DualClass.IsPrimal a

type IsPrimalWithScalar (d :: ADMode) a r =
  IsPrimalWithScalarNew a r

type IsPrimalAndHasFeatures (d :: ADMode) a r =
  IsPrimalWithScalarNew a r

type IsPrimalAndHasInputs (d :: ADMode) a r =
  IsPrimalWithScalarNew a r

type ADModeAndNum (d :: ADMode) r =
  ( DualNumber.ADNum r
  , ForwardDerivative r
  , Primal (DualNumber.ADVal r) ~ r
  , Tensor (DualNumber.ADVal r)
  , DynamicTensor (DualNumber.ADVal r)
  , Ranked (DualNumber.ADVal r) ~ Compose DualNumber.ADVal (Flip OR.Array r)
  )

type HasDelta r = ( ADModeAndNum 'ADModeGradient r
                  , Dual r ~ Delta0 r )

-- shims:

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: forall r a. ADTensor r
  => (Domains (DualNumber.ADVal r) -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = TensorADVal.makeADInputs parameters deltaInputs
  in f inputs

valueOnDomains
  :: (ADTensor r, IsPrimalWithScalarNew a r)
  => (Domains (DualNumber.ADVal r) -> DualNumber.ADVal a)
  -> Domains r
  -> a
{-# INLINE valueOnDomains #-}
valueOnDomains f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = TensorADVal.makeADInputs parameters deltaInputs
  in snd $ Engine.revOnADInputs Nothing f inputs

revOnADInputs
  :: (ADTensor r, IsPrimalWithScalarNew a r)
  => a
  -> (Domains (DualNumber.ADVal r) -> DualNumber.ADVal a)
  -> Domains (DualNumber.ADVal r)
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs = Engine.revOnADInputs  . Just

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (ADTensor r, IsPrimalWithScalarNew a r)
  => a
  -> (Domains (DualNumber.ADVal r) -> DualNumber.ADVal a)
  -> Domains r
  -> (Domains r, a)
revOnDomains = Engine.revOnDomains . Just

prettyPrintDf
  :: (ADTensor r, Show (Dual r))
  => (Domains (DualNumber.ADVal r) -> DualNumber.ADVal r)
  -> Domains r
  -> String
prettyPrintDf f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = TensorADVal.makeADInputs parameters deltaInputs
      !(DualNumber.D _ _ deltaTopLevel) = f inputs
  in ppShow deltaTopLevel

-- * Simplified version compatibility shims

at0 :: ADModeAndNum d r => Domains (DualNumber.ADVal r) -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 TensorADVal.ADInputs{..} i =
  dD emptyADShare (OR.toVector (runFlip inputPrimal0) V.! i)
                               (inputDual0 V.! i)

at1 :: forall n r d.
       ( KnownNat n, ADModeAndNum d r, TensorOf n r ~ Flip OR.Array r n )
    => Domains (DualNumber.ADVal r) -> Int -> ADVal d (Flip OR.Array r n)
{-# INLINE at1 #-}
at1 TensorADVal.ADInputs{..} i = dD emptyADShare (tfromD $ inputPrimal1 V.! i)
                                            (dFromD $ inputDual1 V.! i)

ifoldlDual' :: forall a d r. ADModeAndNum d r
             => (a -> Int -> ADVal d r -> a)
             -> a
             -> Domains (DualNumber.ADVal r)
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a TensorADVal.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD emptyADShare valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a $ OR.toVector (runFlip inputPrimal0)

foldlDual' :: forall a d r. ADModeAndNum d r
            => (a -> ADVal d r -> a)
            -> a
            -> Domains (DualNumber.ADVal r)
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a TensorADVal.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD emptyADShare valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a $ OR.toVector (runFlip inputPrimal0)

domainsFromD01 :: (Tensor r, DomainsCollection r)
               => Domain0 r -> DomainR r -> Domains r
domainsFromD01 = mkDomains

domainsFrom01 :: ( Numeric r, TensorOf 1 r ~ Flip OR.Array r 1, Tensor r
                 , DomainsCollection r )
              => Vector r -> DomainR r -> Domains r
domainsFrom01 v0 = mkDomains (Flip $ OR.fromVector [V.length v0] v0)

domainsFrom0V :: ( Numeric r, DTensorOf r ~ OD.Array r, DomainsCollection r
                 , TensorOf 1 r ~ Flip OR.Array r 1, Tensor r )
              => Vector r -> Data.Vector.Vector (Vector r) -> Domains r
domainsFrom0V v0 vs =
  domainsFrom01 v0 (V.map (\v -> OD.fromVector [V.length v] v) vs)

listsToParameters :: ( Numeric r, DTensorOf r ~ OD.Array r
                     , TensorOf 1 r ~ Flip OR.Array r 1, Tensor r
                     , DomainsCollection r )
                  => ([r], [r]) -> Domains r
listsToParameters (a0, a1) =
  domainsFrom0V (V.fromList a0) (V.singleton (V.fromList a1))

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, _a2, _aX) = listsToParameters (a0, a1)

domainsD0 :: (Tensor r, DomainsCollection r)
          => (Numeric r, TensorOf 1 r ~ Flip OR.Array r 1) => Domains r -> Vector r
domainsD0 = OR.toVector . runFlip . domains0

-- * Auxiliary definitions

fromX1 :: forall n d r.(ADModeAndNum d r, KnownNat n)
       => ADVal d (OD.Array r) -> ADVal d (TensorOf n r)
fromX1 (DualNumber.D l u u') = dDnotShared l (tfromD u) (dFromD u')

from1X :: (ADModeAndNum d r, KnownNat n)
       => ADVal d (TensorOf n r) -> ADVal d (OD.Array r)
from1X (DualNumber.D l u u') = dDnotShared l (dfromR u) (dFromR u')

-- Shims to reuse the tests for ordinary vectors.
type Vec r = Flip OR.Array r 1

vecToV :: Numeric r => Vec r -> Vector r
vecToV = OR.toVector . runFlip

vToVec :: Numeric r => Vector r -> Vec r
vToVec v = Flip $ OR.fromVector [V.length v] v

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
ensureToplevelSharing :: IsPrimal d a => ADVal d a -> ADVal d a
ensureToplevelSharing (DualNumber.D l u u') = dD l u u'

scaleNotShared :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleNotShared a (DualNumber.D l u u') = dDnotShared l (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
addNotShared (DualNumber.D l1 u u') (DualNumber.D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
multNotShared (DualNumber.D l1 u u') (DualNumber.D l2 v v') =
  dDnotShared (l1 `mergeADShare` l2) (u * v) (dAdd (dScale v u') (dScale u v'))

addParameters :: ( Numeric r, Num (Vector r), DTensorOf r ~ OD.Array r
                 , Tensor r, DomainsCollection r )
              => Domains r -> Domains r -> Domains r
addParameters paramsA paramsB =
  mkDomains (domains0 paramsA + domains0 paramsB)
            (V.zipWith (+) (domainsR paramsA) (domainsR paramsB))

-- Dot product and sum respective ranks and then sum it all.
dotParameters
  :: ( Tensor r, DomainsCollection r
     , Numeric r, DTensorOf r ~ OD.Array r, TensorOf 1 r ~ Flip OR.Array r 1 )
  => Domains r -> Domains r -> r
dotParameters paramsA paramsB =
  runFlip (domains0 paramsA) `tdot0R` runFlip (domains0 paramsB)
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1)
          (domainsR paramsA) (domainsR paramsB))


-- * Legacy operations needed to re-use vector differentiation tests

-- Operations resulting in a scalar

sumElements10 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
sumElements10 = tunScalar . tsum . Compose

index10 :: ADModeAndNum d r => ADVal d (Vec r) -> Int -> ADVal d r
index10 d ix = tunScalar $ Compose d ! (singletonIndex $ fromIntegral ix)

minimum0 :: (KnownNat n, Tensor r) => TensorOf n r -> r
minimum0 = tunScalar . tminimum

maximum0 :: (KnownNat n, Tensor r) => TensorOf n r -> r
maximum0 = tunScalar . tmaximum

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d (Vec r) -> ADVal d r
(<.>!) u v = tunScalar $ tdot0 (Compose u) (Compose v)

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r => ADVal d (Vec r) -> Vec r -> ADVal d r
(<.>!!) u s = (<.>!) u (constant s)


-- Operations resulting in a vector (really, a OR.Array)

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNum d r => [ADVal d r] -> ADVal d (Vec r)
fromList1 = getCompose . tfromList . map tscalar

fromVector1 :: ADModeAndNum d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (Vec r)
fromVector1 = getCompose . tfromVector . V.map tscalar

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vec r)
konst1 d n = getCompose $ tkonst n (tscalar d)

append1 :: Tensor r => TensorOf 1 r -> TensorOf 1 r -> TensorOf 1 r
append1 = tappend

slice1 :: Tensor r => Int -> Int -> TensorOf 1 r -> TensorOf 1 r
slice1 = tslice

reverse1 :: Tensor r => TensorOf 1 r -> TensorOf 1 r
reverse1 = treverse


-- Build and map variants

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Elementwise n f = getCompose $ tfromList $ map (tscalar . f) [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Closure n f =
  let g i = let DualNumber.D _ u _ = f i in u
      h i = let DualNumber.D _ _ u' = f $ fromIntegral i in u'
  in dD emptyADShare (Flip $ OR.fromList [n] $ map g [0 .. n - 1])
                     (dBuildR n (dScalarR . h))

map1Elementwise
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vec r) -> ADVal d (Vec r)
map1Elementwise f = getCompose . tmap1 (tscalar . f . tunScalar) . Compose
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (llength d) (lindex0 d)@


-- These can't be easily generalized to non-ADVal without causing
-- typing problems where this special variant is used, so it has to stay
-- for the sake of old tests.
scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (DualNumber.D l u u') = dD l (a * u) (dScale a u')

constant :: IsPrimal d a => a -> ADVal d a
constant a = dD emptyADShare a dZero

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (DualNumber.D l u u') =
  let y = recip (1 + exp (- u))
  in dD l y (dScale (y * (1 - y)) u')

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vec r)
        -> ADVal d r
foldl'0 f uu' (DualNumber.D _ v v') =
  let g !acc ix p =
        f (dD emptyADShare p (dIndex0 v' (singletonIndex $ fromIntegral ix)
                           (flattenShape (tshapeR $ runFlip v)))) acc
  in V.ifoldl' g uu' (OR.toVector $ runFlip v)

altSumElements10 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
altSumElements10 = foldl'0 (+) 0

sumElementsVectorOfDual
  :: ADModeAndNum d r => Data.Vector.Vector (ADVal d r) -> ADVal d r
sumElementsVectorOfDual = V.foldl' (+) 0

softMax :: ADModeAndNum d r
        => Data.Vector.Vector (ADVal d r)
        -> Data.Vector.Vector (ADVal d r)
softMax us =
  let expUs = V.map exp us  -- used twice below, so named, to enable sharing
      sumExpUs = sumElementsVectorOfDual expUs
  in V.map (\r -> r * recip sumExpUs) expUs

softMaxV :: ADModeAndNum d r
         => ADVal d (Vec r) -> ADVal d (Vec r)
softMaxV d' =
  let d = Compose d'
      expU0 = exp d
  in getCompose
     $ tlet expU0 $ \expU -> tkonst0N (tshape d) (recip $ tsum0 expU) * expU

scaleADVal :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleADVal a (DualNumber.D l u u') = dD l (a * u) (dScale a u')

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall d r. ADModeAndNum d r
                 => Vector r
                 -> Data.Vector.Vector (ADVal d r)
                 -> ADVal d r
lossCrossEntropy targ res =
  let f :: ADVal d r -> Int -> ADVal d r -> ADVal d r
      f !acc i d = acc + scaleADVal (targ V.! i) (log d)
  in negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: ADModeAndNum d r
                  => Vec r
                  -> ADVal d (Vec r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ADModeAndNum d r
  => Vec r -> ADVal d (Vec r) -> ADVal d r
lossSoftMaxCrossEntropyV target d' =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let d = Compose d'
      u = tprimalPart d
      expU = exp (u - tkonst0N (tshape u) (tminimum u))
      sumExpU = tsum0 expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = tscaleByScalar (tunScalar recipSum) expU
  in tunScalar
     $ tD (negate $ log softMaxU `tdot0` target)
            -- TODO: avoid: log . exp
          (tdualPart $ (tconstant (softMaxU - target)) `tdot0` d)
            -- TODO: probably defining tDot0 would lead to a faster
            -- tDot0 (softMaxU - target) u'

relu
  :: forall r d. ADModeAndNum d r
  => ADVal d (Vec r) -> ADVal d (Vec r)
relu v =
  let oneIfGtZero = tmap0N (\x -> ifB (x <=* 0) 0.0 1.0) $ Compose v
  in getCompose $ oneIfGtZero * Compose v
