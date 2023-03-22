{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.DualNumber2
  ( ADVal, dD, pattern D, Dual
  , ADModeAndNum, HasDelta
  , fromX1, from1X
  , Vec, vecToV, vToVec
  , SNat(..), staticNatValue, staticNatFromProxy
  , ensureToplevelSharing, scaleNotShared, addNotShared, multNotShared
  , addParameters, dotParameters
  , square, squaredDifference
  , sumElements10, index10, minimum0, maximum0, altSumElements10
  , (<.>!), (<.>!!)
  , softMax, lossCrossEntropy, lossCrossEntropyV, lossSoftMaxCrossEntropyV
  , fromList1, fromVector1, konst1, append1, slice1, reverse1, maxPool1
  , softMaxV, build1POPL, build1Elementwise, build1Closure, build1
  , map1POPL, map1Elementwise
  , -- * Re-exports
    ADMode(..)
  , IsPrimal, IsPrimalWithScalar, IsPrimalAndHasFeatures, IsPrimalAndHasInputs
  , Domain0, DomainR, Domain1, domains1, Domains(..), emptyDomain0, nullDomains
  , ADInputs
  , at0, at1, ifoldlDual', foldlDual'
  , domainsFromD01, domainsFrom01, domainsFrom0V
  , listsToParameters, listsToParameters4, domainsD0
  , valueGeneral, valueOnDomains, revOnADInputs, revOnDomains
  , constant, scale, logistic
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

import           HordeAd.Core.Delta
  ( Delta0
  , Domain0
  , DomainR
  , Domains (..)
  , ForwardDerivative
  , emptyDomain0
  , nullDomains
  )
import           HordeAd.Core.DualClass hiding (IsPrimal, IsPrimalWithScalar)
import qualified HordeAd.Core.DualClass as DualClass
import           HordeAd.Core.DualNumber (dD, dDnotShared, pattern D)
import qualified HordeAd.Core.DualNumber as DualNumber
import qualified HordeAd.Core.Engine as Engine
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorADVal (ADTensor)
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.TensorOps

type Domain1 r = DomainR r

domains1 :: Domains r -> Domain1 r
domains1 = domainsR

type ADInputs d r = Engine.ADInputs r

data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue
  deriving Show

type ADVal (d :: ADMode) a = DualNumber.ADVal a

type IsPrimal (d :: ADMode) a =
  DualClass.IsPrimal a

type IsPrimalWithScalar (d :: ADMode) a r =
  DualClass.IsPrimalWithScalar a r

type IsPrimalAndHasFeatures (d :: ADMode) a r =
  DualClass.IsPrimalWithScalar a r

type IsPrimalAndHasInputs (d :: ADMode) a r =
  DualClass.IsPrimalWithScalar a r

type ADModeAndNum (d :: ADMode) r =
  ( DualNumber.ADNum r, ForwardDerivative r, Primal (DualNumber.ADVal r) ~ r
  , Tensor (DualNumber.ADVal r) )

type HasDelta r = ( ADModeAndNum 'ADModeGradient r
                  , Dual r ~ Delta0 r )

-- shims:

-- The general case, needed for old hacky tests using only scalars.
valueGeneral
  :: forall r a. ADTensor r
  => (Engine.ADInputs r -> a)
  -> Domains r
  -> a
-- Small enough that inline won't hurt.
{-# INLINE valueGeneral #-}
valueGeneral f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = Engine.makeADInputs parameters deltaInputs
  in f inputs

valueOnDomains
  :: (ADTensor r, DualClass.IsPrimalWithScalar a r)
  => (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Domains r
  -> a
{-# INLINE valueOnDomains #-}
valueOnDomains f parameters =
  let deltaInputs = Engine.generateDeltaInputs parameters
      inputs = Engine.makeADInputs parameters deltaInputs
  in snd $ Engine.revOnADInputs Nothing f inputs

revOnADInputs
  :: (ADTensor r, DualClass.IsPrimalWithScalar a r)
  => a
  -> (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Engine.ADInputs r
  -> (Domains r, a)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE revOnADInputs #-}
revOnADInputs = Engine.revOnADInputs  . Just

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names, but newcomers may have trouble understanding them.
revOnDomains
  :: (ADTensor r, DualClass.IsPrimalWithScalar a r)
  => a
  -> (Engine.ADInputs r -> DualNumber.ADVal a)
  -> Domains r
  -> (Domains r, a)
revOnDomains = Engine.revOnDomains . Just

-- * Simplified version compatibility shims

at0 :: ADModeAndNum d r => Engine.ADInputs r -> Int -> ADVal d r
{-# INLINE at0 #-}
at0 Engine.ADInputs{..} i = D (OR.toVector inputPrimal0 V.! i) (inputDual0 V.! i)

at1 :: forall n r d. (KnownNat n, ADModeAndNum d r, TensorOf n r ~ OR.Array n r)
    => Engine.ADInputs r -> Int -> ADVal d (OR.Array n r)
{-# INLINE at1 #-}
at1 Engine.ADInputs{..} i = dD (tfromD $ inputPrimal1 V.! i)
                               (dFromD $ inputDual1 V.! i)

ifoldlDual' :: forall a d r. ADModeAndNum d r
             => (a -> Int -> ADVal d r -> a)
             -> a
             -> Engine.ADInputs r
             -> a
{-# INLINE ifoldlDual' #-}
ifoldlDual' f a Engine.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc i b
  V.ifoldl' g a $ OR.toVector inputPrimal0

foldlDual' :: forall a d r. ADModeAndNum d r
            => (a -> ADVal d r -> a)
            -> a
            -> Engine.ADInputs r
            -> a
{-# INLINE foldlDual' #-}
foldlDual' f a Engine.ADInputs{..} = do
  let g :: a -> Int -> r -> a
      g !acc i valX =
        let !b = dD valX (inputDual0 V.! i)
        in f acc b
  V.ifoldl' g a $ OR.toVector inputPrimal0

domainsFromD01 :: Domain0 r -> DomainR r -> Domains r
domainsFromD01 = Domains

domainsFrom01 :: (Numeric r, TensorOf 1 r ~ OR.Array 1 r)
              => Vector r -> DomainR r -> Domains r
domainsFrom01 v0 = Domains (OR.fromVector [V.length v0] v0)

domainsFrom0V :: ( Numeric r, DynamicTensor r ~ OD.Array r
                 , TensorOf 1 r ~ OR.Array 1 r )
              => Vector r -> Data.Vector.Vector (Vector r) -> Domains r
domainsFrom0V v0 vs =
  domainsFrom01 v0 (V.map (\v -> OD.fromVector [V.length v] v) vs)

listsToParameters :: ( Numeric r, DynamicTensor r ~ OD.Array r
                     , TensorOf 1 r ~ OR.Array 1 r )
                  => ([r], [r]) -> Domains r
listsToParameters (a0, a1) =
  domainsFrom0V (V.fromList a0) (V.singleton (V.fromList a1))

listsToParameters4 :: ([Double], [Double], [Double], [Double]) -> Domains Double
listsToParameters4 (a0, a1, _a2, _aX) = listsToParameters (a0, a1)

domainsD0 :: (Numeric r, TensorOf 1 r ~ OR.Array 1 r) => Domains r -> Vector r
domainsD0 = OR.toVector . domains0

-- * Auxiliary definitions

fromX1 :: forall n d r. (ADModeAndNum d r, KnownNat n)
       => ADVal d (OD.Array r) -> ADVal d (TensorOf n r)
fromX1 (D u u') = dDnotShared (tfromD u) (dFromD u')

from1X :: (ADModeAndNum d r, KnownNat n)
       => ADVal d (TensorOf n r) -> ADVal d (OD.Array r)
from1X (D u u') = dDnotShared (tfromR u) (dFromR u')

-- Shims to reuse the tests for ordinary vectors.
type Vec r = OR.Array 1 r

vecToV :: Numeric r => Vec r -> Vector r
vecToV = OR.toVector

vToVec :: Numeric r => Vector r  -> Vec r
vToVec v = OR.fromVector [V.length v] v

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
ensureToplevelSharing (D u u') = dD u u'

scaleNotShared :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleNotShared a (D u u') = dDnotShared (a * u) (dScale a u')

addNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
addNotShared (D u u') (D v v') = dDnotShared (u + v) (dAdd u' v')

multNotShared :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a -> ADVal d a
multNotShared (D u u') (D v v') =
  dDnotShared (u * v) (dAdd (dScale v u') (dScale u v'))

addParameters :: ( Numeric r, Num (Vector r), DynamicTensor r ~ OD.Array r
                 , Num (TensorOf 1 r) )
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1) (Domains b0 b1) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)

-- Dot product and sum respective ranks and then sum it all.
dotParameters
  :: (Numeric r, DynamicTensor r ~ OD.Array r, TensorOf 1 r ~ OR.Array 1 r)
  => Domains r -> Domains r -> r
dotParameters (Domains a0 a1) (Domains b0 b1) =
  a0 `tdot0R` b0
  + V.sum (V.zipWith (\v1 u1 ->
      if isTensorDummy v1 || isTensorDummy u1
      then 0
      else OD.toVector v1 LA.<.> OD.toVector u1) a1 b1)

-- * Legacy operations needed to re-use vector differentiation tests

-- General operations, for any tensor rank

constantADVal :: IsPrimal d a => a -> ADVal d a
constantADVal a = dD a dZero

-- Optimized and more clearly written @u ** 2@.
square :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a
square (D u u') = dD (u * u) (dScale (2 * u) u')

squaredDifference :: (Num a, IsPrimal d a)
                  => a -> ADVal d a -> ADVal d a
squaredDifference targ res = square $ res - constantADVal targ

-- Operations resulting in a scalar

sumElements10 :: ADModeAndNum d r
              => ADVal d (Vec r) -> ADVal d r
sumElements10 (D u u') = dD (tsum0R u) (dSum0 (tshapeR u) u')

index10 :: ADModeAndNum d r => ADVal d (Vec r) -> Int -> ADVal d r
index10 (D u u') ix = dD (u `tindex0R` singletonIndex ix)
                         (dIndex0 u' (singletonIndex ix) (tshapeR u))

minimum0 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
minimum0 (D u u') =
  let ix = tminIndexR u
  in dD (OR.unScalar $ tindex1R u ix)
        (dIndex0 u' (singletonIndex ix) (flattenShape (tshapeR u)))

maximum0 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
maximum0 (D u u') =
  let ix = tmaxIndexR u
  in dD (OR.unScalar $ tindex1R u ix)
        (dIndex0 u' (singletonIndex ix) (flattenShape (tshapeR u)))

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vec r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let g !acc ix p =
        f (dD p (dIndex0 v' (singletonIndex ix) (flattenShape (tshapeR v)))) acc
  in V.ifoldl' g uu' (OR.toVector v)

altSumElements10 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d r
altSumElements10 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r
       => ADVal d (Vec r) -> ADVal d (Vec r) -> ADVal d r
(<.>!) (D u u') (D v v') = dD (tdot0R u v)
                              (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r
        => ADVal d (Vec r) -> Vec r -> ADVal d r
(<.>!!) (D u u') v = dD (tdot0R u v) (dDot0 v u')

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

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall d r. ADModeAndNum d r
                 => Vector r
                 -> Data.Vector.Vector (ADVal d r)
                 -> ADVal d r
lossCrossEntropy targ res =
  let f :: ADVal d r -> Int -> ADVal d r -> ADVal d r
      f !acc i d = acc + scaleADVal (targ V.! i) (log d)
  in negate $ V.ifoldl' f 0 res

scaleADVal :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scaleADVal a (D u u') = dD (a * u) (dScale a u')

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
lossSoftMaxCrossEntropyV target (D u u') =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - OR.constant [tsizeR u] (tminimum0R u))
      sumExpU = tsum0R expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU =  OR.constant [tsizeR expU] recipSum * expU
  in dD (negate $ log softMaxU `tdot0R` target)  -- TODO: avoid: log . exp
        (dDot0 (softMaxU - target) u')


-- Operations resulting in a vector (really, a OR.Array)

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNum d r
          => [ADVal d r] -> ADVal d (Vec r)
fromList1 l =
  dD (tfromListR $ map (\(D u _) -> tscalarR u) l)
     (dFromListR $ map (\(D _ u') -> dScalarR u') l)

fromVector1 :: ADModeAndNum d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (Vec r)
fromVector1 l =
  dD (tfromVectorR
      $ V.convert $ V.map (\(D u _) -> tscalarR u) l)  -- hope it fuses
     (dFromVectorR
      $ V.map (\(D _ u') -> dScalarR u') l)

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vec r)
konst1 (D u u') n =
  dD (tkonstR n (tscalarR u)) (dKonstR n (dScalarR u'))

append1 :: ADModeAndNum d r
        => ADVal d (Vec r) -> ADVal d (Vec r) -> ADVal d (Vec r)
append1 (D u u') (D v v') = dD (tappendR u v)
                               (dAppendR u' (head $ OR.shapeL u) v')

slice1 :: ADModeAndNum d r
       => Int -> Int -> ADVal d (Vec r) -> ADVal d (Vec r)
slice1 i k (D u u') = dD (tsliceR i k u)
                         (dSliceR i k u' (head $ OR.shapeL u))

reverse1 :: ADModeAndNum d r => ADVal d (Vec r) -> ADVal d (Vec r)
reverse1 (D u u') = dD (treverseR u) (dReverseR u')

-- TODO: define Enum instance of (AstInt r) to enable AST for this.
-- No padding; remaining areas ignored.
maxPool1 :: ADModeAndNum d r
         => Int -> Int -> ADVal d (Vec r) -> ADVal d (Vec r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. tsizeR u - ksize]]
  in fromList1 $ map maximum0 slices

softMaxV :: ADModeAndNum d r
         => ADVal d (Vec r) -> ADVal d (Vec r)
softMaxV d@(D u _) =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements10 expU
  in konst1 (recip sumExpU) (tsizeR u) * expU


-- Build and map variants

build1POPL :: Int -> (Int -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
build1POPL n f = V.fromList $ map f [0 .. n - 1]

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Elementwise n f = fromList1 $ map f [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1Closure n f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (OR.fromList [n] $ map g [0 .. n - 1])
        (dBuildR n (dScalarR . h))

build1
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vec r)
build1 = build1Closure

map1POPL :: (ADVal d r -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
         -> Data.Vector.Vector (ADVal d r)
map1POPL = V.map

map1Elementwise
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vec r) -> ADVal d (Vec r)
map1Elementwise f d@(D u _) =
  build1Elementwise (tsizeR u) $ \i -> f (index10 d i)
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (llength d) (lindex0 d)@

-- These can't be easily generalized to non-ADVal without causing
-- typing problems where this special variant is used, so it has to stay
-- for the sake of old tests.
scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (D u u') = dD (a * u) (dScale a u')

constant :: IsPrimal d a => a -> ADVal d a
constant a = dD a dZero

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in dD y (dScale (y * (1 - y)) u')
