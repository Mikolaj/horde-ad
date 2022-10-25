{-# LANGUAGE AllowAmbiguousTypes, CPP, DataKinds, FlexibleInstances, GADTs,
             QuantifiedConstraints, RankNTypes, TypeFamilies,
             TypeFamilyDependencies #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Simplified.DualNumber
  ( module HordeAd.Core.DualNumber
  , ADMode(..), ADModeAndNum
  , IsPrimal (..), IsPrimalAndHasFeatures, HasDelta
  , Domain0, Domain1, Domains  -- an important re-export
  ) where

import Prelude

import           Data.List.Index (imap)
import           Data.MonoTraversable (MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Simplified.Delta
  ( Delta0 (..)
  , Delta0' (..)
  , Delta1 (..)
  , Delta1' (..)
  , Domain0
  , Domain1
  , Domains
  )

-- * The main dual number type

-- | The enumeration of all available automatic differentiation computation
-- modes.
data ADMode =
    ADModeGradient
  | ADModeDerivative
  | ADModeValue

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
data ADVal (d :: ADMode) a = D a (Dual d a)

-- | The type family that enumerates all possible \"ranks\" for each
-- automatic differentiation mode. The second type argument is meant
-- to be the primal component of dual numbers. The result is the dual component.
--
-- Rank 0 is troublesome because, in derivative mode, the dual component
-- is not the primal component wrapped in a datatype or newtype constructor.
-- This makes impossible a representation of primal and dual components as
-- the primal plus the type constructor for creating the dual.
--
-- Rank S is troublesome because of the extra type parameter @sh@ representing
-- a shape. This is another obstacle to a dual number representation via
-- a single-argument type constructor.
type family Dual (d :: ADMode) a = result | result -> d a where
  Dual 'ADModeGradient Double = Delta0 Double
  Dual 'ADModeGradient Float = Delta0 Float
  Dual 'ADModeGradient (Vector r) = Delta1 r
-- not injective:  Dual 'ADModeDerivative r = r
  Dual 'ADModeDerivative Double = Double
  Dual 'ADModeDerivative Float = Float
  Dual 'ADModeDerivative (Vector r) = Vector r
  Dual 'ADModeValue a = DummyDual a

-- A bit more verbose, but a bit faster than @data@, perhaps by chance.
newtype DummyDual a = DummyDual ()

dummyDual :: DummyDual a
dummyDual = DummyDual ()


-- * Standard numeric operations, one set of definitions for each rank
-- and differentiation mode combination, because we don't have
-- rank polymorphism in the simplified variant of horde-ad

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (ADVal d a) where

instance Ord (ADVal d a) where

instance (Num a, Dual 'ADModeGradient a ~ Delta0 a)
         => Num (ADVal 'ADModeGradient a) where
  D u u' + D v v' = D (u + v) (Delta0 undefined (Add0 u' v'))
  D u u' - D v v' = D (u - v) (Add0 u' (Scale0 (-1) v'))
  D u u' * D v v' = D (u * v) (Add0 (Scale0 v u') (Scale0 u v'))
  negate (D v v') = D (negate v) (Scale0 (-1) v')
  abs (D v v') = D (abs v) (Scale0 (signum v) v')
  signum (D v _) = D (signum v) Zero0
  fromInteger = constant . fromInteger

instance (Real a, Dual 'ADModeGradient a ~ Delta0 a)
         => Real (ADVal d a) where
  toRational = undefined  -- TODO?

instance (Fractional a, Dual 'ADModeGradient a ~ Delta0 a)
         => Fractional (ADVal d a) where
  D u u' / D v v' =
    let recipSq = recip (v * v)  -- ensure sharing; also elsewhere
    in D (u / v) (Add0 (Scale0 (v * recipSq) u') (Scale0 (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (Scale0 minusRecipSq v')
  fromRational = constant . fromRational

instance (Floating a, Dual 'ADModeGradient a ~ Delta0 a)
         => Floating (ADVal d a) where
  pi = constant pi
  exp (D u u') = let expU = exp u
                 in D expU (Scale0 expU u')
  log (D u u') = D (log u) (Scale0 (recip u) u')
  sqrt (D u u') = let sqrtU = sqrt u
                  in D sqrtU (Scale0 (recip (sqrtU + sqrtU)) u')
  D u u' ** D v v' = D (u ** v) (Add0 (Scale0 (v * (u ** (v - 1))) u')
                                      (Scale0 ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D u u') = D (sin u) (Scale0 (cos u) u')
  cos (D u u') = D (cos u) (Scale0 (- (sin u)) u')
  tan (D u u') = let cosU = cos u
                 in D (tan u) (Scale0 (recip (cosU * cosU)) u')
  asin (D u u') = D (asin u) (Scale0 (recip (sqrt (1 - u*u))) u')
  acos (D u u') = D (acos u) (Scale0 (- recip (sqrt (1 - u*u))) u')
  atan (D u u') = D (atan u) (Scale0 (recip (1 + u*u)) u')
  sinh (D u u') = D (sinh u) (Scale0 (cosh u) u')
  cosh (D u u') = D (cosh u) (Scale0 (sinh u) u')
  tanh (D u u') = let y = tanh u
                  in D y (Scale0 (1 - y * y) u')
  asinh (D u u') = D (asinh u) (Scale0 (recip (sqrt (1 + u*u))) u')
  acosh (D u u') = D (acosh u) (Scale0 (recip (sqrt (u*u - 1))) u')
  atanh (D u u') = D (atanh u) (Scale0 (recip (1 - u*u)) u')

instance (RealFrac a, Dual 'ADModeGradient a ~ Delta0 a)
         => RealFrac (ADVal d a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance (RealFloat a, Dual 'ADModeGradient a ~ Delta0 a)
         => RealFloat (ADVal d a) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (Add0 (Scale0 (- u * t) v') (Scale0 (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

-- * Other morally rank-polymorphic operations that here get expanded

{-
constant :: IsPrimal d a => a -> ADVal d a
constant a = D a Zero0

scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (D u u') = D (a * u) (Scale0 a u')

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in D y (Scale0 (y * (1 - y)) u')

-- Optimized and more clearly written @u ** 2@.
square :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a
square (D u u') = D (u * u) (Scale0 (2 * u) u')

squaredDifference :: (Num a, IsPrimal d a)
                  => a -> ADVal d a -> ADVal d a
squaredDifference targ res = square $ res - constant targ

relu :: (ADModeAndNum d r, IsPrimalAndHasFeatures d a r)
     => ADVal d a -> ADVal d a
relu v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) u
  in scale oneIfGtZero v

reluLeaky :: (ADModeAndNum d r, IsPrimalAndHasFeatures d a r)
          => ADVal d a -> ADVal d a
reluLeaky v@(D u _) =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) u
  in scale oneIfGtZero v


-- * Operations resulting in a scalar

sumElements0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
sumElements0 (D u u') = D (HM.sumElements u) (dSumElements0 u' (V.length u))

index0 :: ADModeAndNum d r => ADVal d (Vector r) -> Int -> ADVal d r
index0 (D u u') ix = D (u V.! ix) (dIndex0 u' ix (V.length u))

minimum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
minimum0 (D u u') =
  D (HM.minElement u) (dIndex0 u' (HM.minIndex u) (V.length u))

maximum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
maximum0 (D u u') =
  D (HM.maxElement u) (dIndex0 u' (HM.maxIndex u) (V.length u))

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vector r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (dIndex0 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
altSumElements0 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r
       => ADVal d (Vector r) -> ADVal d (Vector r) -> ADVal d r
(<.>!) (D u u') (D v v') = D (u HM.<.> v) (Add0 (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r
        => ADVal d (Vector r) -> Vector r -> ADVal d r
(<.>!!) (D u u') v = D (u HM.<.> v) (dDot0 v u')

infixr 8 <.>$
(<.>$) :: (ADModeAndNum d r, KnownNat n)
       => ADVal d (OS.Array '[n] r) -> ADVal d (OS.Array '[n] r)
       -> ADVal d r
(<.>$) d e = fromS1 d <.>! fromS1 e

fromX0 :: ADModeAndNum d r => ADVal d (OT.Array r) -> ADVal d r
fromX0 (D u u') = D (OT.unScalar u) (dFromX0 u')

fromS0 :: ADModeAndNum d r => ADVal d (OS.Array '[] r) -> ADVal d r
fromS0 (D u u') = D (OS.unScalar u) (dFromS0 u')

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
      f !acc i d = acc + scale (targ V.! i) (log d)
  in negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: ADModeAndNum d r
                  => Vector r
                  -> ADVal d (Vector r)
                  -> ADVal d r
lossCrossEntropyV targ res = negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ADModeAndNum d r
  => Vector r -> ADVal d (Vector r) -> ADVal d r
lossSoftMaxCrossEntropyV target (D u u') =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - HM.scalar (HM.maxElement u))
      sumExpU = HM.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = HM.scaleRecip sumExpU expU
      softMaxU = HM.scale recipSum expU
  in D (negate $ log softMaxU HM.<.> target)  -- TODO: avoid: log . exp
       (dDot0 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
seq1 :: ADModeAndNum d r
     => Data.Vector.Vector (ADVal d r) -> ADVal d (Vector r)
seq1 v = D (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
           (dSeq1 $ V.map (\(D _ u') -> u') v)

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vector r)
konst1 (D u u') n = D (HM.konst u n) (dKonst1 u' n)

append1 :: ADModeAndNum d r
        => ADVal d (Vector r) -> ADVal d (Vector r)
        -> ADVal d (Vector r)
append1 (D u u') (D v v') = D (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: ADModeAndNum d r
       => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
slice1 i n (D u u') = D (V.slice i n u) (dSlice1 i n u' (V.length u))

-- The detour through a boxed vector (list probably fuses away)
-- is costly, but only matters if @f@ is cheap.
map1 :: ADModeAndNum d r
     => (ADVal d r -> ADVal d r) -> ADVal d (Vector r)
     -> ADVal d (Vector r)
map1 f (D v v') =
  let k = V.length v
      g ix p = f $ D p (dIndex0 v' ix k)
      ds = imap g $ V.toList v
  in seq1 $ V.fromList ds

reverse1 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d (Vector r)
reverse1 (D u u') = D (V.reverse u) (dReverse1 u')

corr1 :: ADModeAndNum d r
      => ADVal d (Vector r) -> ADVal d (Vector r)
      -> ADVal d (Vector r)
corr1 ker@(D u _) vv@(D v _) = case (V.length u, V.length v) of
  (0, lenV) -> konst1 0 lenV
  (lenK, lenV) -> if lenK <= lenV
                  then vectorSlices2 lenK vv #>! ker
                  else error $ "corr1: len kernel " ++ show lenK
                               ++ " > len vector " ++ show lenV

-- This is not optimally implemented: @append1@ is costly compared
-- to the @mconcat@ counterpart.
conv1 :: ADModeAndNum d r
      => ADVal d (Vector r) -> ADVal d (Vector r)
      -> ADVal d (Vector r)
conv1 ker@(D u _) vv@(D v _) =
  let lenK = V.length u
      lenV = V.length v
      kerRev = reverse1 ker
      z = konst1 0 (lenK - 1)
      vvPadded = append1 z $ append1 vv z
  in if lenK == 0
     then konst1 0 lenV
     else corr1 kerRev vvPadded

-- No padding; remaining areas ignored.
maxPool1 :: ADModeAndNum d r
         => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. V.length u - ksize]]
  in seq1 $ V.fromList $ map maximum0 slices

softMaxV :: ADModeAndNum d r
         => ADVal d (Vector r) -> ADVal d (Vector r)
softMaxV d@(D u _) =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements0 expU
  in konst1 (recip sumExpU) (V.length u) * expU
-}
