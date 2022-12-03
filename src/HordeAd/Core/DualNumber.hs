{-# LANGUAGE AllowAmbiguousTypes, CPP, DataKinds, FlexibleInstances, GADTs,
             QuantifiedConstraints, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.DualNumber
  ( module HordeAd.Core.DualNumber
  , ADVal, dD, dDnotShared
  , ADMode(..), ADModeAndNum
  , IsPrimal (..), IsPrimalAndHasFeatures, HasDelta
  , Domain0, Domain1, Domain2, DomainX, Domains(..), nullDomains
      -- an important re-export
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import           Data.Array.Shape (DivRoundUp)
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.List.Index (imap)
import           Data.MonoTraversable (MonoFunctor (omap))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , SomeNat (..)
  , natVal
  , someNatVal
  , type (+)
  , type (-)
  , type (<=)
  )
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.DualClass
import HordeAd.Internal.Delta
  ( Domain0
  , Domain1
  , Domain2
  , DomainX
  , Domains (..)
  , atIndexInTensor
  , isTensorDummy
  , nullDomains
  )

-- * Auxiliary definitions

-- | Sizes of tensor dimensions, of batches, etc., packed for passing
-- between functions as witnesses of type variable values.
data StaticNat (n :: Nat) where
  MkSN :: KnownNat n => StaticNat n

staticNatValue :: forall n i. (KnownNat n, Num i) => StaticNat n -> i
{-# INLINE staticNatValue #-}
staticNatValue = fromInteger . natVal

-- | Warning: takes the absolute value of the argument.
withStaticNat :: Int -> (forall n. KnownNat n => (StaticNat n -> r)) -> r
withStaticNat i f = case someNatVal $ toInteger $ abs i of
  Just (SomeNat (_ :: Proxy n)) -> f (MkSN :: StaticNat n)
  Nothing -> error "impossible in mkStaticNat"

staticNatFromProxy :: KnownNat n => Proxy n -> StaticNat n
staticNatFromProxy Proxy = MkSN

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

addParameters :: (Numeric r, Num (Vector r))
              => Domains r -> Domains r -> Domains r
addParameters (Domains a0 a1 a2 aX) (Domains b0 b1 b2 bX) =
  Domains (a0 + b0)
          (V.zipWith (+) a1 b1)
          (V.zipWith (+) a2 b2)
          (V.zipWith (+) aX bX)

-- Dot product and sum respective ranks and then sum it all.
dotParameters :: Numeric r => Domains r -> Domains r -> r
dotParameters (Domains a0 a1 a2 aX) (Domains b0 b1 b2 bX) =
  a0 LA.<.> b0
  + V.sum (V.zipWith (\v1 u1 ->
      if V.null v1 || V.null u1
      then 0
      else v1 LA.<.> u1) a1 b1)
  + V.sum (V.zipWith (\v2 u2 ->
      if LA.rows v2 <= 0 || LA.rows u2 <= 0
      then 0
      else LA.flatten v2 LA.<.> LA.flatten u2) a2 b2)
  + V.sum (V.zipWith (\vX uX ->
      if isTensorDummy vX || isTensorDummy uX
      then 0
      else OT.toVector vX LA.<.> OT.toVector uX) aX bX)


-- * General operations, for any tensor rank

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (ADVal d a) where

instance Ord (ADVal d a) where

instance (Num a, IsPrimal d a) => Num (ADVal d a) where
  D u u' + D v v' = dD (u + v) (dAdd u' v')
  D u u' - D v v' = dD (u - v) (dAdd u' (dScale (-1) v'))
  D u u' * D v v' = dD (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = dD (negate v) (dScale (-1) v')
  abs (D v v') = dD (abs v) (dScale (signum v) v')
  signum (D v _) = dD (signum v) dZero
  fromInteger = constant . fromInteger

instance (Real a, IsPrimal d a) => Real (ADVal d a) where
  toRational = undefined  -- TODO?

instance (Fractional a, IsPrimal d a) => Fractional (ADVal d a) where
  D u u' / D v v' =
    let recipSq = recip (v * v)  -- ensure sharing; also elsewhere
    in dD (u / v) (dAdd (dScale (v * recipSq) u') (dScale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in dD (recip v) (dScale minusRecipSq v')
  fromRational = constant . fromRational

instance (Floating a, IsPrimal d a) => Floating (ADVal d a) where
  pi = constant pi
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

instance (RealFrac a, IsPrimal d a) => RealFrac (ADVal d a) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance (RealFloat a, IsPrimal d a) => RealFloat (ADVal d a) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in dD (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

constant :: IsPrimal d a => a -> ADVal d a
constant a = dD a dZero

scale :: (Num a, IsPrimal d a) => a -> ADVal d a -> ADVal d a
scale a (D u u') = dD (a * u) (dScale a u')

logistic :: (Floating a, IsPrimal d a) => ADVal d a -> ADVal d a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in dD y (dScale (y * (1 - y)) u')

-- Optimized and more clearly written @u ** 2@.
square :: (Num a, IsPrimal d a) => ADVal d a -> ADVal d a
square (D u u') = dD (u * u) (dScale (2 * u) u')

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
sumElements0 (D u u') = dD (LA.sumElements u) (dSumElements0 u' (V.length u))

index10 :: ADModeAndNum d r => ADVal d (Vector r) -> Int -> ADVal d r
index10 (D u u') ix = dD (u V.! ix) (dIndex10 u' ix (V.length u))

-- index10(flatten) is not a solution, because it's O(n).
index20 :: ADModeAndNum d r => ADVal d (Matrix r) -> (Int, Int) -> ADVal d r
index20 (D u u') ix = dD (u `LA.atIndex` ix) (dIndex20 u' ix (LA.size u))

indexX0 :: ADModeAndNum d r => ADVal d (OT.Array r) -> [Int] -> ADVal d r
indexX0 (D u u') ix = dD (u `atIndexInTensor` ix) (dIndexX0 u' ix (OT.shapeL u))

-- Passing the index via type application, as in @indexS@,
-- would guarantee it's in bounds, but would require it to be statically
-- known (unless we deploy some machinery that postpones to runtime
-- the type checks that are determined impossible at compile-time).
-- Conversion in @fromSX@ is O(1).
indexS0 :: (ADModeAndNum d r, OS.Shape sh)
        => ADVal d (OS.Array sh r) -> [Int] -> ADVal d r
indexS0 d ix = indexX0 (fromSX d) ix

minimum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
minimum0 (D u u') =
  dD (LA.minElement u) (dIndex10 u' (LA.minIndex u) (V.length u))

maximum0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
maximum0 (D u u') =
  dD (LA.maxElement u) (dIndex10 u' (LA.maxIndex u) (V.length u))

foldl'0 :: ADModeAndNum d r
        => (ADVal d r -> ADVal d r -> ADVal d r)
        -> ADVal d r -> ADVal d (Vector r)
        -> ADVal d r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (dD p (dIndex10 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d r
altSumElements0 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: ADModeAndNum d r
       => ADVal d (Vector r) -> ADVal d (Vector r) -> ADVal d r
(<.>!) (D u u') (D v v') = dD (u LA.<.> v) (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: ADModeAndNum d r
        => ADVal d (Vector r) -> Vector r -> ADVal d r
(<.>!!) (D u u') v = dD (u LA.<.> v) (dDot0 v u')

infixr 8 <.>$
(<.>$) :: (ADModeAndNum d r, KnownNat n)
       => ADVal d (OS.Array '[n] r) -> ADVal d (OS.Array '[n] r)
       -> ADVal d r
(<.>$) d e = fromS1 d <.>! fromS1 e

fromX0 :: ADModeAndNum d r => ADVal d (OT.Array r) -> ADVal d r
fromX0 (D u u') = dD (OT.unScalar u) (dFromX0 u')

fromS0 :: ADModeAndNum d r => ADVal d (OS.Array '[] r) -> ADVal d r
fromS0 (D u u') = dD (OS.unScalar u) (dFromS0 u')

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
  let expU = exp (u - LA.scalar (LA.maxElement u))
      sumExpU = LA.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = LA.scaleRecip sumExpU expU
      softMaxU = LA.scale recipSum expU
  in dD (negate $ log softMaxU LA.<.> target)  -- TODO: avoid: log . exp
        (dDot0 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
fromList1 :: ADModeAndNum d r
          => [ADVal d r] -> ADVal d (Vector r)
fromList1 l = dD (V.fromList $ map (\(D u _) -> u) l)  -- I hope this fuses
                 (dFromList1 $ map (\(D _ u') -> u') l)

fromVector1 :: ADModeAndNum d r
            => Data.Vector.Vector (ADVal d r) -> ADVal d (Vector r)
fromVector1 v = dD (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
                   (dFromVector1 $ V.map (\(D _ u') -> u') v)

konst1 :: ADModeAndNum d r => ADVal d r -> Int -> ADVal d (Vector r)
konst1 (D u u') n = dD (LA.konst u n) (dKonst1 u' n)

append1 :: ADModeAndNum d r
        => ADVal d (Vector r) -> ADVal d (Vector r)
        -> ADVal d (Vector r)
append1 (D u u') (D v v') = dD (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: ADModeAndNum d r
       => Int -> Int -> ADVal d (Vector r) -> ADVal d (Vector r)
slice1 i n (D u u') = dD (V.slice i n u) (dSlice1 i n u' (V.length u))

sumRows1 :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (Vector r)
sumRows1 (D u u') = dD (V.fromList $ map LA.sumElements $ LA.toRows u)
                       (dSumRows1 u' (LA.cols u))

sumColumns1 :: ADModeAndNum d r
            => ADVal d (Matrix r) -> ADVal d (Vector r)
sumColumns1 (D u u') = dD (V.fromList $ map LA.sumElements $ LA.toColumns u)
                          (dSumColumns1 u' (LA.rows u))

-- | Dense matrix-vector product.
infixr 8 #>!
(#>!) :: ADModeAndNum d r
      => ADVal d (Matrix r) -> ADVal d (Vector r)
      -> ADVal d (Vector r)
(#>!) (D u u') (D v v') = dD (u LA.#> v) (dAdd (dMD_V1 u' v) (dM_VD1 u v'))

-- | Dense matrix-vector product with a constant vector.
infixr 8 #>!!
(#>!!) :: ADModeAndNum d r
       => ADVal d (Matrix r) -> Vector r
       -> ADVal d (Vector r)
(#>!!) (D u u') v = dD (u LA.#> v) (dMD_V1 u' v)

fromX1 :: ADModeAndNum d r => ADVal d (OT.Array r) -> ADVal d (Vector r)
fromX1 (D u u') = dD (OT.toVector u) (dFromX1 u')

fromS1 :: forall len d r. (KnownNat len, ADModeAndNum d r)
       => ADVal d (OS.Array '[len] r) -> ADVal d (Vector r)
fromS1 (D u u') = dD (OS.toVector u) (dFromS1 u')

reverse1 :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d (Vector r)
reverse1 (D u u') = dD (V.reverse u) (dReverse1 u')

flatten1 :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (Vector r)
flatten1 (D u u') = let (rows, cols) = LA.size u
                    in dD (LA.flatten u) (dFlatten1 rows cols u')

flattenX1 :: ADModeAndNum d r
          => ADVal d (OT.Array r) -> ADVal d (Vector r)
flattenX1 (D u u') = let sh = OT.shapeL u
                     in dD (OT.toVector u) (dFlattenX1 sh u')

flattenS1 :: (ADModeAndNum d r, OS.Shape sh)
          => ADVal d (OS.Array sh r) -> ADVal d (Vector r)
flattenS1 (D u u') = dD (OS.toVector u) (dFlattenS1 u')

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
  in fromList1 $ map maximum0 slices

softMaxV :: ADModeAndNum d r
         => ADVal d (Vector r) -> ADVal d (Vector r)
softMaxV d@(D u _) =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
      sumExpU = sumElements0 expU
  in konst1 (recip sumExpU) (V.length u) * expU

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyL
  :: ADModeAndNum d r
  => Matrix r
  -> ADVal d (Matrix r)
  -> ADVal d (Vector r)
lossSoftMaxCrossEntropyL target (D u u') =
  let expU = exp (u - LA.scalar (LA.maxElement u))  -- vs exploding gradients
      sumExpU = V.fromList $ map LA.sumElements $ LA.toColumns expU
      recipSum = recip sumExpU
      softMaxU = LA.asRow recipSum * expU
                   -- this @asRow@ is safe; multiplied at once
      scaled = dD (negate $ log softMaxU * target)
                  (dScale (softMaxU - target) u')
  in sumColumns1 scaled

build1POPL :: Int -> (Int -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
build1POPL n f = V.fromList $ map f [0 .. n - 1]

-- Fake rank 1. This is still an array of delta expressions, thinly wrapped,
-- instead of a single delta expression representing an array.
-- We gain a little by storing the primal part in an unboxed vector.
build1Elementwise, build1Closure, build1
  :: ADModeAndNum d r
  => Int -> (Int -> ADVal d r) -> ADVal d (Vector r)
build1Elementwise n f = fromList1 $ map f [0 .. n - 1]
  -- equivalent to @fromVector1 $ build1POPL n f@

build1Closure n f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (V.fromList $ map g [0 .. n - 1]) (dBuild1 n h)

build1 = build1Closure

map1POPL :: (ADVal d r -> ADVal d r) -> Data.Vector.Vector (ADVal d r)
         -> Data.Vector.Vector (ADVal d r)
map1POPL f vd = V.map f vd

-- The list probably fuses away, which may make it a bit faster than
-- if written using @build1Elementwise@.
map1Elementwise, map1Closure
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Vector r)
  -> ADVal d (Vector r)
map1Elementwise f _d@(D v v') =
  let k = V.length v
      g ix p = f $ dD p (dIndex10 v' ix k)
      ds = imap g $ V.toList v
  in fromList1 ds
    -- equivalent to @build1Elementwise (V.length v) $ \i -> f (index10 _d i)@
    -- equivalent to
    -- @fromVector1 . map1POPL f . rank1toVector
    --   where rank1toVector d@(D v _v') = V.generate (V.length v) (index10 d)@

map1Closure f d@(D v _) = build1Closure (V.length v) $ \i -> f (index10 d i)


-- * Operations resulting in a matrix

-- @2@ means rank two, so the dual component represents a matrix.
fromList2 :: ADModeAndNum d r
          => (Int, Int) -> [ADVal d r] -> ADVal d (Matrix r)
fromList2 (i, j) l = dD (j LA.>< i $ map (\(D u _) -> u) l)
                        (dFromList2 (i, j) $ map (\(D _ u') -> u') l)

fromVector2 :: ADModeAndNum d r
            => (Int, Int) -> Data.Vector.Vector (ADVal d r)
            -> ADVal d (Matrix r)
fromVector2 (i, j) v = dD (LA.reshape j $ V.convert $ V.map (\(D u _) -> u) v)
                          (dFromVector2 (i, j) $ V.map (\(D _ u') -> u') v)

fromRows2 :: ADModeAndNum d r
          => Data.Vector.Vector (ADVal d (Vector r))
          -> ADVal d (Matrix r)
fromRows2 v = dD (LA.fromRows $ map (\(D u _) -> u) $ V.toList v)
                 (dFromRows2 $ V.map (\(D _ u') -> u') v)

fromColumns2 :: ADModeAndNum d r
             => Data.Vector.Vector (ADVal d (Vector r))
             -> ADVal d (Matrix r)
fromColumns2 v = dD (LA.fromRows $ map (\(D u _) -> u) $ V.toList v)
                    (dFromColumns2 $ V.map (\(D _ u') -> u') v)

konst2 :: ADModeAndNum d r
       => ADVal d r -> (Int, Int) -> ADVal d (Matrix r)
konst2 (D u u') sz = dD (LA.konst u sz) (dKonst2 u' sz)

transpose2 :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (Matrix r)
transpose2 (D u u') = dD (LA.tr' u) (dTranspose2 u')

-- | Dense matrix-matrix product.
--
-- If @u@ is a m x n (number of rows x number of columns) matrix
-- and @v@ is a n x p matrix then the result of @u <>! v@ is a m x p matrix.
infixr 8 <>!
(<>!) :: ADModeAndNum d r
      => ADVal d (Matrix r) -> ADVal d (Matrix r)
      -> ADVal d (Matrix r)
(<>!) (D u u') (D v v') = dD (u LA.<> v) (dAdd (dMD_M2 u' v) (dM_MD2 u v'))

-- | Dense matrix-matrix product with a constant matrix.
infixr 8 <>!!
(<>!!) :: ADModeAndNum d r
       => ADVal d (Matrix r) -> Matrix r
       -> ADVal d (Matrix r)
(<>!!) (D u u') v = dD (u LA.<> v) (dMD_M2 u' v)

rowAppend2 :: ADModeAndNum d r
           => ADVal d (Matrix r) -> ADVal d (Matrix r)
           -> ADVal d (Matrix r)
rowAppend2 (D u u') (D v v') =
  dD (u LA.=== v) (dRowAppend2 u' (LA.rows u) v')

columnAppend2 :: ADModeAndNum d r
              => ADVal d (Matrix r) -> ADVal d (Matrix r)
              -> ADVal d (Matrix r)
columnAppend2 (D u u') (D v v') =
  dD (u LA.||| v) (dColumnAppend2 u' (LA.cols u) v')

rowSlice2 :: ADModeAndNum d r
          => Int -> Int -> ADVal d (Matrix r)
          -> ADVal d (Matrix r)
rowSlice2 i n (D u u') = dD (LA.subMatrix (i, 0) (n, LA.cols u) u)
                            (dRowSlice2 i n u' (LA.rows u))

columnSlice2 :: ADModeAndNum d r
             => Int -> Int -> ADVal d (Matrix r)
             -> ADVal d (Matrix r)
columnSlice2 i n (D u u') = dD (LA.subMatrix (0, i) (LA.rows u, n) u)
                               (dColumnSlice2 i n u' (LA.rows u))

asRow2 :: ADModeAndNum d r
       => ADVal d (Vector r) -> Int -> ADVal d (Matrix r)
asRow2 (D u u') n = dD (LA.fromRows $ replicate n u) (dAsRow2 u')

asColumn2 :: ADModeAndNum d r
          => ADVal d (Vector r) -> Int -> ADVal d (Matrix r)
asColumn2 (D u u') n = dD (LA.fromColumns $ replicate n u) (dAsColumn2 u')

fromX2 :: ADModeAndNum d r => ADVal d (OT.Array r) -> ADVal d (Matrix r)
fromX2 (D u u') = case OT.shapeL u of
  [_, cols] -> dD (LA.reshape cols $ OT.toVector u) (dFromX2 u')
  dims -> error $ "fromX2: the tensor has wrong dimensions " ++ show dims

fromS2 :: forall rows cols d r.
          (KnownNat rows, KnownNat cols, ADModeAndNum d r)
       => ADVal d (OS.Array '[rows, cols] r) -> ADVal d (Matrix r)
fromS2 (D u u') = dD (LA.reshape (valueOf @cols) $ OS.toVector u) (dFromS2 u')

flipud2 :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (Matrix r)
flipud2 (D u u') = dD (LA.flipud u) (dFlipud2 u')

fliprl2 :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (Matrix r)
fliprl2 (D u u') = dD (LA.fliprl u) (dFliprl2 u')

vectorSlices2 :: ADModeAndNum d r
              => Int -> ADVal d (Vector r) -> ADVal d (Matrix r)
vectorSlices2 n vv@(D v _) =
  fromRows2 $ V.fromList [slice1 i n vv | i <- [0 .. V.length v - n]]

reshape2 :: ADModeAndNum d r
         => Int -> ADVal d (Vector r) -> ADVal d (Matrix r)
reshape2 cols (D u u') = dD (LA.reshape cols u) (dReshape2 cols u')

-- TODO: This has list of matrices result instead of a cube tensor.
matrixSlices2 :: ADModeAndNum d r
              => Int -> ADVal d (Matrix r) -> [ADVal d (Matrix r)]
matrixSlices2 dr m@(D u _) =
  let (rows, cols) = LA.size u
      n = dr * cols
      f k = reshape2 cols $ slice1 (k * cols) n (flatten1 m)
  in map f [0 .. rows - dr]

-- Not optimal: matrix is constructed and destructed immediately,
-- which is costly when evaluating delta expressions. The transposes
-- may not be optimal, either. This goes down to individual deltas
-- of scalars, which is horrible for performance. Unlike @corr1@
-- this uses the slow dot product instead of the fast matrix-vector
-- (or matrix-matrix) multiplication.
corr2 :: forall d r. ADModeAndNum d r
      => ADVal d (Matrix r) -> ADVal d (Matrix r)
      -> ADVal d (Matrix r)
corr2 ker@(D u _) m@(D v _) =
  let (rowsK, colsK) = LA.size u
      (rowsM, colsM) = LA.size v
      rr = rowsM - rowsK + 1
      rc = colsM - colsK + 1
  in if | rowsK <= 0 || colsK <= 0 ->
          error $ "corr2: empty kernel not handled: " ++ show (rowsK, colsK)
        | rr <= 0 || rc <= 0 ->
          error $ "corr2: dim kernel " ++ show (rowsK, colsK)
                  ++ " > dim matrix " ++ show (rowsM, colsM)
        | otherwise ->
          let kerTransV = flatten1 (transpose2 ker)
              dotColSlices :: ADVal d (Matrix r) -> [ADVal d r]
              dotColSlices tm =
                let ttm = transpose2 tm
                    colSlices = matrixSlices2 colsK ttm
                    f :: ADVal d (Matrix r) -> ADVal d r
                    f sm = kerTransV <.>! flatten1 sm
                in map f colSlices
              rowSlices = matrixSlices2 rowsK m
              dotSlicesOfSlices = map dotColSlices rowSlices
          in reshape2 rc $ fromList1 $ concat dotSlicesOfSlices

conv2 :: forall d r. ADModeAndNum d r
      => ADVal d (Matrix r) -> ADVal d (Matrix r)
      -> ADVal d (Matrix r)
conv2 ker@(D u _) m@(D v _) =
  let (rowsK, colsK) = LA.size u
      (rowsM, colsM) = LA.size v
  in if | rowsK <= 0 || colsK <= 0 ->
          konst2 0 (rowsM + rowsK - 1, colsM + colsK - 1)
        | otherwise ->
          let zRow = konst2 0 (rowsK - 1, colsM)
              rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
              zCol = konst2 0 (rowsM + 2 * (rowsK - 1), colsK - 1)
              padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
          in corr2 (fliprl2 . flipud2 $ ker) padded

conv2' :: ADModeAndNum d r
       => ADVal d (Matrix r) -> ADVal d (Matrix r)
       -> ADVal d (Matrix r)
conv2' (D u u') (D v v') = dD (LA.conv2 u v) (dAdd (dConv2 u v') (dConv2 v u'))

-- A variant with limited padding, corresponding to SAME padding
-- from Tensorflow. Data size does not change with this padding.
-- It also performs convolution wrt flipped kernel (and so saves
-- on flipping it here), which makes no practical difference when
-- the kernel is initialized randomly.
convSame2 :: forall d r. ADModeAndNum d r
          => ADVal d (Matrix r) -> ADVal d (Matrix r)
          -> ADVal d (Matrix r)
convSame2 ker@(D u _) m@(D v _) =
  let (rowsK, colsK) = LA.size u
      (rowsM, colsM) = LA.size v
  in if | rowsK <= 0 || colsK <= 0 ->
          konst2 0 (rowsM, colsM)
        | otherwise ->
          let zRow = konst2 0 ((rowsK - 1) `div` 2, colsM)
              rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
              zCol = konst2 0 (rowsM + rowsK - 1, (colsK - 1) `div` 2)
              padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
          in corr2 ker padded

-- No padding; remaining areas ignored.
maxPool2 :: forall d r. ADModeAndNum d r
         => Int -> Int -> ADVal d (Matrix r) -> ADVal d (Matrix r)
maxPool2 ksize stride m@(D u _) =
  let (rows, cols) = LA.size u
      colsOut = cols `div` stride
      resultRows = [0, stride .. rows - ksize]
      resultCols = [0, stride .. cols - ksize]
      resultCoords = [(r, c) | r <- resultRows, c <- resultCols]
      getArea :: (Int, Int) -> ADVal d (Vector r)
      getArea (r0, c0) =
        let getAreaAtRow r1 =
              append1 (slice1 (r1 * cols + c0) ksize (flatten1 m))
        in foldr getAreaAtRow (fromVector1 V.empty) [r0 .. r0 + ksize - 1]
      mins = map (maximum0 . getArea) resultCoords
  in reshape2 colsOut $ fromList1 mins

build2Elementwise, build2Closure, build2
  :: ADModeAndNum d r
  => (Int, Int) -> ((Int, Int) -> ADVal d r) -> ADVal d (Matrix r)
build2Elementwise (i, j) f =
  let ijs = [(i1, j1) | i1 <- [0 .. i - 1], j1 <- [0 .. j - 1]]
  in fromList2 (i, j) $ map f ijs

build2Closure (i, j) f =
  let g ij = let D u _ = f ij in u
      h ij = let D _ u' = f ij in u'
      ijs = [(i1, j1) | i1 <- [0 .. i - 1], j1 <- [0 .. j - 1]]
        -- TODO: tests needed to determine if the order of pairs is right
  in dD ((j LA.>< i) $ map g ijs) (dBuild2 (i, j) h)

build2 = build2Closure

map2Elementwise, map2Closure
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (Matrix r)
  -> ADVal d (Matrix r)
map2Elementwise f d@(D v _) =
  build2Elementwise (LA.size v) $ \i -> f (index20 d i)

map2Closure f d@(D v _) =
  build2Closure (LA.size v) $ \i -> f (index20 d i)


-- * Operations resulting in an arbitrary untyped tensor

fromListX :: ADModeAndNum d r
          => OT.ShapeL -> [ADVal d r] -> ADVal d (OT.Array r)
fromListX sh l = dD (OT.fromList sh $ map (\(D u _) -> u) l)
                    (dFromListX sh $ map (\(D _ u') -> u') l)

fromVectorX :: ADModeAndNum d r
            => OT.ShapeL -> Data.Vector.Vector (ADVal d r)
            -> ADVal d (OT.Array r)
fromVectorX sh v = dD (OT.fromVector sh $ V.convert $ V.map (\(D u _) -> u) v)
                      (dFromVectorX sh $ V.map (\(D _ u') -> u') v)

konstX :: ADModeAndNum d r
       => ADVal d r -> OT.ShapeL -> ADVal d (OT.Array r)
konstX (D u u') sh = dD (OT.constant sh u) (dKonstX u' sh)

appendX :: ADModeAndNum d r
        => ADVal d (OT.Array r) -> ADVal d (OT.Array r)
        -> ADVal d (OT.Array r)
appendX (D u u') (D v v') =
  dD (u `OT.append` v) (dAppendX u' (head $ OT.shapeL u) v')

sliceX :: ADModeAndNum d r
       => Int -> Int -> ADVal d (OT.Array r) -> ADVal d (OT.Array r)
sliceX i n (D u u') = dD (OT.slice [(i, n)] u)
                         (dSliceX i n u' (head $ OT.shapeL u))

indexX :: ADModeAndNum d r
       => ADVal d (OT.Array r) -> Int -> ADVal d (OT.Array r)
indexX (D u u') ix = dD (OT.index u ix)
                        (dIndexX u' ix (head $ OT.shapeL u))

ravelFromListX :: ADModeAndNum d r
               => [ADVal d (OT.Array r)] -> ADVal d (OT.Array r)
ravelFromListX ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
      sh = case lu of
        u : _ -> length lu : OT.shapeL u
        [] -> []
  in dD (OT.ravel $ OTB.fromList sh lu) (dRavelFromListX lu')

unravelToListX :: ADModeAndNum d r
               => ADVal d (OT.Array r) -> [ADVal d (OT.Array r)]
unravelToListX (D v v') = case OT.shapeL v of
  k : _ -> let g ix p = dD p (dIndexX v' ix k)
           in imap g $ OTB.toList $ OT.unravel v
  [] -> error "unravelToListX: wrong tensor dimensions"  -- catch early

mapOuterX :: ADModeAndNum d r
     => (ADVal d (OT.Array r) -> ADVal d (OT.Array r))
     -> ADVal d (OT.Array r)
     -> ADVal d (OT.Array r)
mapOuterX f = ravelFromListX . map f . unravelToListX

zipWithOuterX :: ADModeAndNum d r
         => (ADVal d (OT.Array r) -> ADVal d (OT.Array r)
             -> ADVal d (OT.Array r))
         -> ADVal d (OT.Array r) -> ADVal d (OT.Array r)
         -> ADVal d (OT.Array r)
zipWithOuterX f d e =
  ravelFromListX $ zipWith f (unravelToListX d) (unravelToListX e)

reshapeX :: ADModeAndNum d r
         => OT.ShapeL -> ADVal d (OT.Array r) -> ADVal d (OT.Array r)
reshapeX sh' (D u u') = dD (OT.reshape sh' u) (dReshapeX (OT.shapeL u) sh' u')

from0X :: ADModeAndNum d r => ADVal d r -> ADVal d (OT.Array r)
from0X (D u u') = dD (OT.scalar u) (dFrom0X u')

from1X :: ADModeAndNum d r => ADVal d (Vector r) -> ADVal d (OT.Array r)
from1X (D u u') = dD (OT.fromVector [V.length u] u) (dFrom1X u')

from2X :: ADModeAndNum d r => ADVal d (Matrix r) -> ADVal d (OT.Array r)
from2X (D u u') = dD (OT.fromVector [LA.rows u, LA.cols u] $ LA.flatten u)
                     (dFrom2X u' (LA.cols u))

fromSX :: forall sh d r. (ADModeAndNum d r, OS.Shape sh)
       => ADVal d (OS.Array sh r) -> ADVal d (OT.Array r)
fromSX (D u u') = dD (Data.Array.Convert.convert u) (dFromSX u')

buildXElementwise, buildXClosure, buildX
  :: ADModeAndNum d r
  => OT.ShapeL -> ([Int] -> ADVal d r) -> ADVal d (OT.Array r)
buildXElementwise sh f =
  -- Copied from Data.Array.Internal.
  let getStridesT :: OT.ShapeL -> [Int]
      getStridesT = scanr (*) 1
      (s, ss) = case getStridesT sh of
        s2 : ss2 -> (s2, ss2)
        [] -> error "scanr in buildXElementwise"
      toIx [] _ = []
      toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
      ixs = [toIx ss i | i <- [0 .. s - 1]]
  in fromListX sh $ map f ixs

buildXClosure sh f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
      -- Copied from Data.Array.Internal.
      -- This could be replaced by Data.Array.DynamicS.generate,
      -- but it would obfuscate the connection with other similar code.
      getStridesT :: OT.ShapeL -> [Int]
      getStridesT = scanr (*) 1
      (s, ss) = case getStridesT sh of
        s2 : ss2 -> (s2, ss2)
        [] -> error "scanr in buildXClosure"
      toIx [] _ = []
      toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
      ixs = [toIx ss i | i <- [0 .. s - 1]]
  in dD (OT.fromList sh $ map g ixs) (dBuildX sh h)

buildX = buildXClosure

mapXElementwise, mapXClosure
  :: ADModeAndNum d r
  => (ADVal d r -> ADVal d r) -> ADVal d (OT.Array r)
  -> ADVal d (OT.Array r)
mapXElementwise f d@(D v _) =
  buildXElementwise (OT.shapeL v) $ \i -> f (indexX0 d i)

mapXClosure f d@(D v _) =
  buildXClosure (OT.shapeL v) $ \i -> f (indexX0 d i)


#if defined(VERSION_ghc_typelits_natnormalise)
-- * Operations resulting in an arbitrary fully typed Shaped tensor

fromListS :: (ADModeAndNum d r, OS.Shape sh)
          => [ADVal d r] -> ADVal d (OS.Array sh r)
fromListS l = dD (OS.fromList $ map (\(D u _) -> u) l)
                 (dFromListS $ map (\(D _ u') -> u') l)

fromVectorS :: (ADModeAndNum d r, OS.Shape sh)
            => Data.Vector.Vector (ADVal d r)
            -> ADVal d (OS.Array sh r)
fromVectorS v = dD (OS.fromVector $ V.convert $ V.map (\(D u _) -> u) v)
                   (dFromVectorS $ V.map (\(D _ u') -> u') v)

konstS :: (ADModeAndNum d r, OS.Shape sh)
       => ADVal d r -> ADVal d (OS.Array sh r)
konstS (D u u') = dD (OS.constant u) (dKonstS u')

appendS :: (KnownNat m, KnownNat n, ADModeAndNum d r, OS.Shape sh)
        => ADVal d (OS.Array (m ': sh) r)
        -> ADVal d (OS.Array (n ': sh) r)
        -> ADVal d (OS.Array ((m + n) ': sh) r)
appendS (D u u') (D v v') = dD (u `OS.append` v) (dAppendS u' v')

-- The API of this modules should not have proxies (but StaticNat instead).
-- However, lower level APIs are fine with Proxies. Not using StaticNat
-- there may even prevent mixing up high and mid or low APIs
-- and accessing low level APIs directly instead of via higher levels.
sliceS :: forall i n k rest d r.
          (KnownNat i, KnownNat n, KnownNat k, ADModeAndNum d r, OS.Shape rest)
       => ADVal d (OS.Array (i + n + k ': rest) r)
       -> ADVal d (OS.Array (n ': rest) r)
sliceS (D u u') = dD (OS.slice @'[ '(i, n) ] u)
                     (dSliceS (Proxy :: Proxy i) Proxy u')

indexS :: forall ix k rest d r.
          (KnownNat ix, KnownNat k, ADModeAndNum d r, OS.Shape rest)
       => ADVal d (OS.Array (ix + 1 + k ': rest) r)
       -> ADVal d (OS.Array rest r)
indexS (D u u') = dD (OS.index u (valueOf @ix))
                     (dIndexS u' (Proxy :: Proxy ix))

ravelFromListS :: forall rest k d r.
                  (KnownNat k, ADModeAndNum d r, OS.Shape rest)
               => [ADVal d (OS.Array rest r)]
               -> ADVal d (OS.Array (k : rest) r)
ravelFromListS ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
  in dD (OS.ravel $ OSB.fromList lu) (dRavelFromListS lu')

unravelToListS :: forall k rest d r.
                  (KnownNat k, ADModeAndNum d r, OS.Shape rest)
               => ADVal d (OS.Array (k : rest) r)
               -> [ADVal d (OS.Array rest r)]
unravelToListS (D v v') =
  -- @dIndexS@ is rigid, with type-level bound-checking, so we have to switch
  -- to @dIndexX@ for this function.
  let g ix p = dD p (dFromXS $ dIndexX (dFromSX v') ix (valueOf @k))
  in imap g $ OSB.toList $ OS.unravel v

mapOuterS :: forall k sh1 sh d r.
        (KnownNat k, ADModeAndNum d r, OS.Shape sh, OS.Shape sh1)
     => (ADVal d (OS.Array sh1 r) -> ADVal d (OS.Array sh r))
     -> ADVal d (OS.Array (k : sh1) r)
     -> ADVal d (OS.Array (k : sh) r)
mapOuterS f = ravelFromListS . map f . unravelToListS

zipWithOuterS :: forall k sh1 sh2 sh d r.
            ( ADModeAndNum d r
            , KnownNat k, OS.Shape sh, OS.Shape sh1, OS.Shape sh2 )
         => (ADVal d (OS.Array sh1 r) -> ADVal d (OS.Array sh2 r)
             -> ADVal d (OS.Array sh r))
         -> ADVal d (OS.Array (k : sh1) r)
         -> ADVal d (OS.Array (k : sh2) r)
         -> ADVal d (OS.Array (k : sh) r)
zipWithOuterS f d e =
  ravelFromListS $ zipWith f (unravelToListS d) (unravelToListS e)

reshapeS :: forall sh sh' d r.
            ( ADModeAndNum d r
            , OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh' )
         => ADVal d (OS.Array sh r) -> ADVal d (OS.Array sh' r)
reshapeS (D u u') = dD (OS.reshape u) (dReshapeS u')

-- TODO: generalize as broadcast or stretch
asRowS :: forall k n d r. (ADModeAndNum d r, KnownNat k, KnownNat n)
       => ADVal d (OS.Array '[k] r) -> ADVal d (OS.Array '[n, k] r)
asRowS d = from2S $ asRow2 (fromS1 d) (valueOf @n)

asColumnS :: forall k n d r. (ADModeAndNum d r, KnownNat k, KnownNat n)
          => ADVal d (OS.Array '[k] r) -> ADVal d (OS.Array '[k, n] r)
asColumnS d = from2S $ asColumn2 (fromS1 d) (valueOf @n)

from0S :: ADModeAndNum d r => ADVal d r -> ADVal d (OS.Array '[] r)
from0S (D u u') = dD (OS.scalar u) (dFrom0S u')

from1S :: (KnownNat n, ADModeAndNum d r)
       => ADVal d (Vector r) -> ADVal d (OS.Array '[n] r)
from1S (D u u') = dD (OS.fromVector u) (dFrom1S u')

from2S :: (KnownNat rows, KnownNat cols, ADModeAndNum d r)
       => ADVal d (Matrix r) -> ADVal d (OS.Array '[rows, cols] r)
from2S (D u u') = dD (OS.fromVector $ LA.flatten u) (dFrom2S Proxy u')

fromXS :: (ADModeAndNum d r, OS.Shape sh)
       => ADVal d (OT.Array r) -> ADVal d (OS.Array sh r)
fromXS (D u u') = dD (Data.Array.Convert.convert u) (dFromXS u')

-- TODO: generalize to arbitrary permutations of arbitrarily many ranks using https://hackage.haskell.org/package/orthotope/docs/Data-Array-ShapedS.html#v:transpose
transpose2S :: (ADModeAndNum d r, KnownNat rows, KnownNat cols)
            => ADVal d (OS.Array '[rows, cols] r)
            -> ADVal d (OS.Array '[cols, rows] r)
transpose2S = from2S . transpose2 . fromS2

infixr 8 #>$
(#>$) :: (ADModeAndNum d r, KnownNat rows, KnownNat cols)
      => ADVal d (OS.Array '[rows, cols] r)
      -> ADVal d (OS.Array '[cols] r)
      -> ADVal d (OS.Array '[rows] r)
(#>$) d e = from1S $ fromS2 d #>! fromS1 e

infixr 8 <>$
(<>$) :: (ADModeAndNum d r, KnownNat m, KnownNat n, KnownNat p)
      => ADVal d (OS.Array '[m, n] r)
      -> ADVal d (OS.Array '[n, p] r)
      -> ADVal d (OS.Array '[m, p] r)
(<>$) d e = from2S $ fromS2 d <>! fromS2 e

conv2S :: forall d r kheight_minus_1 kwidth_minus_1 in_height in_width.
          ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
          , KnownNat in_height, KnownNat in_width
          , ADModeAndNum d r )
       => ADVal d (OS.Array '[kheight_minus_1 + 1, kwidth_minus_1 + 1] r)
       -> ADVal d (OS.Array '[in_height, in_width] r)
       -> ADVal d (OS.Array '[ in_height + kheight_minus_1
                             , in_width + kwidth_minus_1 ] r)
conv2S ker x = from2S $ conv2' (fromS2 ker) (fromS2 x)

-- Convolution of many matrices at once. Some of the names of dimensions
-- are from https://www.tensorflow.org/api_docs/python/tf/nn/conv2d
conv24 :: forall kheight_minus_1 kwidth_minus_1
                 out_channels in_height in_width batch_size in_channels d r.
          ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
          , KnownNat out_channels, KnownNat in_height, KnownNat in_width
          , KnownNat batch_size, KnownNat in_channels
          , ADModeAndNum d r )
       => ADVal d (OS.Array '[ out_channels, in_channels
                             , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
       -> ADVal d (OS.Array '[ batch_size, in_channels
                             , in_height, in_width ] r)
       -> ADVal d (OS.Array '[ batch_size, out_channels
                             , in_height + kheight_minus_1
                             , in_width + kwidth_minus_1 ] r)
conv24 ker = mapOuterS conv23 where
  conv23 :: ADVal d (OS.Array '[in_channels, in_height, in_width] r)
         -> ADVal d (OS.Array '[ out_channels
                               , in_height + kheight_minus_1
                               , in_width + kwidth_minus_1 ] r)
  conv23 x = mapOuterS (convFilters x) ker
  convFilters
    :: ADVal d (OS.Array '[in_channels, in_height, in_width] r)
    -> ADVal d (OS.Array '[ in_channels
                          , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
    -> ADVal d (OS.Array '[ in_height + kheight_minus_1
                          , in_width + kwidth_minus_1 ] r)
  convFilters x ker1 = sumOutermost $ zipWithOuterS conv2S ker1 x
  sumOutermost :: ADVal d (OS.Array '[ in_channels
                                     , in_height + kheight_minus_1
                                     , in_width + kwidth_minus_1 ] r)
               -> ADVal d (OS.Array '[ in_height + kheight_minus_1
                                     , in_width + kwidth_minus_1 ] r)
  sumOutermost = sum . unravelToListS
    -- slow; should go through Tensor2, or the Num instance when possible

-- No proxies or anything similar needed here, but we may introduce StaticNat
-- regardless, if the implicitly passed tensor sizes become confusing
-- or if they start being passes explicitly via type application too often.
maxPool24
  :: forall ksize_minus_1 stride in_height in_width batch_size channels d r.
     ( KnownNat ksize_minus_1, KnownNat stride
     , KnownNat in_height, KnownNat in_width
     , KnownNat batch_size, KnownNat channels
     , 1 <= stride
     , ksize_minus_1 <= in_height
     , ksize_minus_1 <= in_width
     , 1 <= in_height - ksize_minus_1 + stride
     , 1 <= in_width - ksize_minus_1 + stride
     , ADModeAndNum d r )
     => ADVal d (OS.Array '[batch_size, channels, in_height, in_width] r)
     -> ADVal d
          (OS.Array '[ batch_size, channels
                     , (in_height - ksize_minus_1) `DivRoundUp` stride
                     , (in_width - ksize_minus_1) `DivRoundUp` stride ] r)
maxPool24 d =
  let res = mapOuterS (mapOuterS (from2S
                        . maxPool2 (valueOf @ksize_minus_1 + 1)
                                   (valueOf @stride)
                        . fromS2)) d
  in res

buildSElementwise, buildSClosure, buildS
  :: forall sh d r. (ADModeAndNum d r, OS.Shape sh)
  => ([Int] -> ADVal d r) -> ADVal d (OS.Array sh r)
buildSElementwise f =
  -- Copied from Data.Array.Internal.
  let getStridesT :: OS.ShapeL -> [Int]
      getStridesT = scanr (*) 1
      (s, ss) = case getStridesT sh of
        s2 : ss2 -> (s2, ss2)
        [] -> error "scanr in buildSElementwise"
      toIx [] _ = []
      toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
      sh = OS.shapeP (Proxy :: Proxy sh)
      ixs = [toIx ss i | i <- [0 .. s - 1]]
  in fromListS $ map f ixs

buildSClosure f =
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
      -- Copied from Data.Array.Internal.
      -- This could be replaced by Data.Array.ShapedS.generate,
      -- but it would obfuscate the connection with other similar code.
      getStridesT :: OS.ShapeL -> [Int]
      getStridesT = scanr (*) 1
      (s, ss) = case getStridesT sh of
        s2 : ss2 -> (s2, ss2)
        [] -> error "scanr in buildSClosure"
      toIx [] _ = []
      toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
      sh = OS.shapeP (Proxy :: Proxy sh)
      ixs = [toIx ss i | i <- [0 .. s - 1]]
  in dD (OS.fromList $ map g ixs) (dBuildS h)

buildS = buildSClosure

mapSElementwise, mapSClosure
  :: (ADModeAndNum d r, OS.Shape sh)
  => (ADVal d r -> ADVal d r) -> ADVal d (OS.Array sh r)
  -> ADVal d (OS.Array sh r)
mapSElementwise f d =
  buildSElementwise $ \i -> f (indexS0 d i)

mapSClosure f d =
  buildSClosure $ \i -> f (indexS0 d i)

-- The following are borrowed from https://github.com/benl23x5/adops.

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
conv2d
  :: forall nImgs nCinpA nAh nAw nCoutK nCinpK nKh nKw
            shK shA shB shK1 d r.
     ( ADModeAndNum d r
     , KnownNat nImgs, KnownNat nCinpA, KnownNat nAh, KnownNat nAw
     , KnownNat nCoutK, KnownNat nKh, KnownNat nKw
     , nCinpA ~ nCinpK
     , shK ~ '[nCoutK, nCinpK, nKh, nKw]
     , shA ~ '[nImgs, nCinpA, nAh, nAw]
     , shB ~ '[nImgs, nCoutK, nAh, nAw]
     , shK1 ~ '[1, nCinpK, nKh, nKw] )
  => ADVal d (OS.Array shK r)
  -> ADVal d (OS.Array shA r)
  -> ADVal d (OS.Array shB r)
conv2d arrK arrA =
  buildS $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezS @shK1 arrK [iCout, 0, 0, 0]
      in dotS0 arrAt arrKt
    _ -> error "wrong index length in conv2d"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicezS :: forall shOut sh d r.
           ( ADModeAndNum d r, OS.Shape sh, OS.Shape shOut
           , OS.Rank sh ~ OS.Rank shOut )
        => ADVal d (OS.Array sh r) -> [Int] -> ADVal d (OS.Array shOut r)
slicezS d ixBase =
  buildS $ \ixResult -> indexzS0 d (zipWith (+) ixBase ixResult)
    -- TODO: check at least at runtime that ixBase has the right length;
    -- my version is less precisely typed than the adops original;
    -- to improve, I'd need sized lists, but probably orthotope
    -- doesn't use them (e.g., in @generate@) for a good reason

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexzS0 :: forall sh d r. (ADModeAndNum d r, OS.Shape sh)
         => ADVal d (OS.Array sh r) -> [Int] -> ADVal d r
indexzS0 d ix = if withinOS @sh ix then indexS0 d ix else 0

-- | Given an index and shape, check if the index is fully within the shape.
withinOS :: forall sh. OS.Shape sh => [Int] -> Bool
withinOS ix =
  let sh = OS.shapeP (Proxy :: Proxy sh)
      within i dim = i >= 0 && i < dim
  in and $ zipWith within ix sh

-- | Compute the dot product of elements in two arrays.
--   The arrays have the same shape.
dotS0 :: (ADModeAndNum d r, OS.Shape sh)
      => ADVal d (OS.Array sh r) -> ADVal d (OS.Array sh r) -> ADVal d r
dotS0 d1 d2 = flattenS1 d1 <.>! flattenS1 d2
#endif
