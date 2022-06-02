{-# LANGUAGE AllowAmbiguousTypes, DataKinds, FlexibleInstances,
             FunctionalDependencies, QuantifiedConstraints, RankNTypes,
             TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=16 #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is the high-level API,
-- defined using the low-level API in "HordeAd.Core.DualClass".
module HordeAd.Core.DualNumber
  ( module HordeAd.Core.DualNumber
  , IsScalar, HasDelta, DMode(..)
  , Domain0, Domain1, Domain2, DomainX, Domains  -- an important re-export
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
import           GHC.TypeLits (KnownNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.DualClass
import HordeAd.Internal.Delta
  (CodeOut (..), Domain0, Domain1, Domain2, DomainX, Domains)

-- * The main dual number types

-- | Dual numbers with the second type argument being the primal component.
data DualNumber (d :: DMode) a = D a (Dual d a)

class (IsScalar d r, Monad m, Functor m, Applicative m)
      => DualMonad d r m | m -> d r where
  returnLet :: IsPrimalWithScalar d a r
            => DualNumber d a -> m (DualNumber d a)

addParameters :: (Numeric r, Num (Vector r))
              => Domains r -> Domains r -> Domains r
addParameters (a0, a1, a2, aX) (b0, b1, b2, bX) =
  (a0 + b0, V.zipWith (+) a1 b1, V.zipWith (+) a2 b2, V.zipWith (+) aX bX)

-- Dot product and sum respective ranks and sum it all.
dotParameters :: Numeric r => Domains r -> Domains r -> r
dotParameters (a0, a1, a2, aX) (b0, b1, b2, bX) =
  a0 HM.<.> b0
  + V.sum (V.zipWith (HM.<.>) a1 b1)
  + V.sum (V.zipWith (HM.<.>) (V.map HM.flatten a2) (V.map HM.flatten b2))
  + V.sum (V.zipWith (HM.<.>) (V.map OT.toVector aX) (V.map OT.toVector bX))


-- * General operations, for any tensor rank

-- These instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (DualNumber d a) where

instance Ord (DualNumber d a) where

-- These instances are dangerous due to possible subexpression copies
-- leading to allocation explosion. Expressions should be wrapped in
-- the monadic @returnLet@ whenever there is a possibility they can be
-- used multiple times in a larger expression.
instance (Num a, IsPrimal d a) => Num (DualNumber d a) where
  D u u' + D v v' = D (u + v) (dAdd u' v')
  D u u' - D v v' = D (u - v) (dAdd u' (dScale (-1) v'))
  D u u' * D v v' = D (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = D (negate v) (dScale (-1) v')
  abs (D v v') = D (abs v) (dScale (signum v) v')
  signum (D v _) = D (signum v) dZero
  fromInteger = constant . fromInteger

instance (Real a, IsPrimal d a) => Real (DualNumber d a) where
  toRational = undefined  -- TODO?

instance (Fractional a, IsPrimal d a) => Fractional (DualNumber d a) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
    in D (u / v) (dAdd (dScale (v * recipSq) u') (dScale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (dScale minusRecipSq v')
  fromRational = constant . fromRational

instance (Floating a, IsPrimal d a) => Floating (DualNumber d a) where
  pi = constant pi
  exp (D u u') = let expU = exp u
                 in D expU (dScale expU u')
  log (D u u') = D (log u) (dScale (recip u) u')
  sqrt (D u u') = let sqrtU = sqrt u
                  in D sqrtU (dScale (recip (sqrtU + sqrtU)) u')
  D u u' ** D v v' = D (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                                      (dScale ((u ** v) * log u) v'))
  logBase x y = log y / log x
  sin (D u u') = D (sin u) (dScale (cos u) u')
  cos (D u u') = D (cos u) (dScale (- (sin u)) u')
  tan (D u u') = let cosU = cos u
                 in D (tan u) (dScale (recip (cosU * cosU)) u')
  asin (D u u') = D (asin u) (dScale (recip (sqrt (1 - u*u))) u')
  acos (D u u') = D (acos u) (dScale (- recip (sqrt (1 - u*u))) u')
  atan (D u u') = D (atan u) (dScale (recip (1 + u*u)) u')
  sinh (D u u') = D (sinh u) (dScale (cosh u) u')
  cosh (D u u') = D (cosh u) (dScale (sinh u) u')
  tanh (D u u') = let y = tanh u
                  in D y (dScale (1 - y * y) u')
  asinh (D u u') = D (asinh u) (dScale (recip (sqrt (1 + u*u))) u')
  acosh (D u u') = D (acosh u) (dScale (recip (sqrt (u*u - 1))) u')
  atanh (D u u') = D (atanh u) (dScale (recip (1 - u*u)) u')

instance (RealFrac a, IsPrimal d a) => RealFrac (DualNumber d a) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFloat a, IsPrimal d a) => RealFloat (DualNumber d a) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

constant :: IsPrimal d a => a -> DualNumber d a
constant a = D a dZero

scale :: (Num a, IsPrimal d a) => a -> DualNumber d a -> DualNumber d a
scale a (D u u') = D (a * u) (dScale a u')

tanhAct :: (DualMonad d r m, IsPrimalAndHasFeatures d a r)
        => DualNumber d a -> m (DualNumber d a)
tanhAct = returnLet . tanh

logistic :: (Floating a, IsPrimal d a) => DualNumber d a -> DualNumber d a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in D y (dScale (y * (1 - y)) u')

logisticAct :: (DualMonad d r m, IsPrimalAndHasFeatures d a r)
            => DualNumber d a -> m (DualNumber d a)
logisticAct = returnLet . logistic

-- Optimized and more clearly written @u ** 2@.
square :: (Num a, IsPrimal d a) => DualNumber d a -> DualNumber d a
square (D u u') = D (u * u) (dScale (2 * u) u')

squaredDifference :: (Num a, IsPrimal d a)
                  => a -> DualNumber d a -> DualNumber d a
squaredDifference targ res = square $ res - constant targ

lossSquared :: (DualMonad d r m, IsPrimalAndHasFeatures d a r)
            => a -> DualNumber d a -> m (DualNumber d a)
lossSquared targ res = returnLet $ squaredDifference targ res

reluAct :: (DualMonad d r m, IsPrimalAndHasFeatures d a r)
        => DualNumber d a -> m (DualNumber d a)
reluAct v@(D u _) = do
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) u
  returnLet $ scale oneIfGtZero v

reluLeakyAct :: (DualMonad d r m, IsPrimalAndHasFeatures d a r)
             => DualNumber d a -> m (DualNumber d a)
reluLeakyAct v@(D u _) = do
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) u
  returnLet $ scale oneIfGtZero v


-- * Operations resulting in a scalar

sumElements0 :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d r
sumElements0 (D u u') = D (HM.sumElements u) (dSumElements0 u' (V.length u))

index0 :: IsScalar d r => DualNumber d (Vector r) -> Int -> DualNumber d r
index0 (D u u') ix = D (u V.! ix) (dIndex0 u' ix (V.length u))

minimum0 :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d r
minimum0 (D u u') =
  D (HM.minElement u) (dIndex0 u' (HM.minIndex u) (V.length u))

maximum0 :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d r
maximum0 (D u u') =
  D (HM.maxElement u) (dIndex0 u' (HM.maxIndex u) (V.length u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@.
foldl'0 :: IsScalar d r
        => (DualNumber d r -> DualNumber d r -> DualNumber d r)
        -> DualNumber d r -> DualNumber d (Vector r)
        -> DualNumber d r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (dIndex0 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d r
altSumElements0 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: IsScalar d r
       => DualNumber d (Vector r) -> DualNumber d (Vector r) -> DualNumber d r
(<.>!) (D u u') (D v v') = D (u HM.<.> v) (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: IsScalar d r
        => DualNumber d (Vector r) -> Vector r -> DualNumber d r
(<.>!!) (D u u') v = D (u HM.<.> v) (dDot0 v u')

infixr 8 <.>$
(<.>$) :: (IsScalar d r, KnownNat n)
       => DualNumber d (OS.Array '[n] r) -> DualNumber d (OS.Array '[n] r)
       -> DualNumber d r
(<.>$) d e = fromS1 d <.>! fromS1 e

fromX0 :: IsScalar d r => DualNumber d (OT.Array r) -> DualNumber d r
fromX0 (D u u') = D (OT.unScalar u) (dFromX0 u')

fromS0 :: IsScalar d r => DualNumber d (OS.Array '[] r) -> DualNumber d r
fromS0 (D u u') = D (OS.unScalar u) (dFromS0 u')

sumElementsVectorOfDual
  :: IsScalar d r => Data.Vector.Vector (DualNumber d r) -> DualNumber d r
sumElementsVectorOfDual = V.foldl' (+) 0

softMaxAct :: DualMonad d r m
           => Data.Vector.Vector (DualNumber d r)
           -> m (Data.Vector.Vector (DualNumber d r))
softMaxAct us = do
  expUs <- V.mapM (returnLet . exp) us
  let sumExpUs = sumElementsVectorOfDual expUs
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpUs
  V.mapM (\r -> returnLet $ r * recipSum) expUs

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall d r m. DualMonad d r m
                 => Vector r
                 -> Data.Vector.Vector (DualNumber d r)
                 -> m (DualNumber d r)
lossCrossEntropy targ res = do
  let f :: DualNumber d r -> Int -> DualNumber d r -> DualNumber d r
      f !acc i d = acc + scale (targ V.! i) (log d)
  returnLet $ negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: DualMonad d r m
                  => Vector r
                  -> DualNumber d (Vector r)
                  -> m (DualNumber d r)
lossCrossEntropyV targ res = returnLet $ negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are on-hot.
lossSoftMaxCrossEntropyV
  :: DualMonad d r m
  => Vector r -> DualNumber d (Vector r) -> m (DualNumber d r)
lossSoftMaxCrossEntropyV target (D u u') = do
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - HM.scalar (HM.maxElement u))
      sumExpU = HM.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = HM.scaleRecip sumExpU expU
      softMaxU = HM.scale recipSum expU
  returnLet $ D (negate $ log softMaxU HM.<.> target)  -- TODO: avoid: log . exp
                (dDot0 (softMaxU - target) u')


-- * Operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
seq1 :: IsScalar d r
     => Data.Vector.Vector (DualNumber d r) -> DualNumber d (Vector r)
seq1 v = D (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
           (dSeq1 $ V.map (\(D _ u') -> u') v)

konst1 :: IsScalar d r => DualNumber d r -> Int -> DualNumber d (Vector r)
konst1 (D u u') n = D (HM.konst u n) (dKonst1 u' n)

append1 :: IsScalar d r
        => DualNumber d (Vector r) -> DualNumber d (Vector r)
        -> DualNumber d (Vector r)
append1 (D u u') (D v v') = D (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: IsScalar d r
       => Int -> Int -> DualNumber d (Vector r) -> DualNumber d (Vector r)
slice1 i n (D u u') = D (V.slice i n u) (dSlice1 i n u' (V.length u))

sumRows1 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Vector r)
sumRows1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toRows u)
                      (dSumRows1 u' (HM.cols u))

sumColumns1 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Vector r)
sumColumns1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toColumns u)
                         (dSumColumns1 u' (HM.rows u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@. The detour through a boxed vector (list probably fuses away)
-- is costly, but only matters if @f@ is cheap.
map1 :: IsScalar d r
     => (DualNumber d r -> DualNumber d r) -> DualNumber d (Vector r)
     -> DualNumber d (Vector r)
map1 f (D v v') =
  let k = V.length v
      g ix p = f $ D p (dIndex0 v' ix k)
      ds = imap g $ V.toList v
  in seq1 $ V.fromList ds

-- | Dense matrix-vector product.
infixr 8 #>!
(#>!) :: IsScalar d r
      => DualNumber d (Matrix r) -> DualNumber d (Vector r)
      -> DualNumber d (Vector r)
(#>!) (D u u') (D v v') = D (u HM.#> v) (dAdd (dMD_V1 u' v) (dM_VD1 u v'))

-- | Dense matrix-vector product with a constant vector.
infixr 8 #>!!
(#>!!) :: IsScalar d r
       => DualNumber d (Matrix r) -> Vector r
       -> DualNumber d (Vector r)
(#>!!) (D u u') v = D (u HM.#> v) (dMD_V1 u' v)

fromX1 :: IsScalar d r => DualNumber d (OT.Array r) -> DualNumber d (Vector r)
fromX1 (D u u') = D (OT.toVector u) (dFromX1 u')

fromS1 :: forall len d r. (KnownNat len, IsScalar d r)
       => DualNumber d (OS.Array '[len] r) -> DualNumber d (Vector r)
fromS1 (D u u') = D (OS.toVector u) (dFromS1 u')

reverse1 :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d (Vector r)
reverse1 (D u u') = D (V.reverse u) (dReverse1 u')

flatten1 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Vector r)
flatten1 (D u u') = let (rows, cols) = HM.size u
                    in D (HM.flatten u) (dFlatten1 rows cols u')

flattenX1 :: IsScalar d r => DualNumber d (OT.Array r) -> DualNumber d (Vector r)
flattenX1 (D u u') = let sh = OT.shapeL u
                     in D (OT.toVector u) (dFlattenX1 sh u')

flattenS1 :: (IsScalar d r, OS.Shape sh)
          => DualNumber d (OS.Array sh r) -> DualNumber d (Vector r)
flattenS1 (D u u') = D (OS.toVector u) (dFlattenS1 u')

corr1 :: IsScalar d r
      => DualNumber d (Vector r) -> DualNumber d (Vector r)
      -> DualNumber d (Vector r)
corr1 ker@(D u _) vv@(D v _) = case (V.length u, V.length v) of
  (0, lenV) -> konst1 0 lenV
  (lenK, lenV) -> if lenK <= lenV
                  then vectorSlices2 lenK vv #>! ker
                  else error $ "corr1: len kernel " ++ show lenK
                               ++ " > len vector " ++ show lenV

-- This is not optimally implemented: @append1@ is costly compared
-- to a @mconcat@ counterpart and @z@ is used twice without
-- assigning it to a variable.
conv1 :: IsScalar d r
      => DualNumber d (Vector r) -> DualNumber d (Vector r)
      -> DualNumber d (Vector r)
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
maxPool1 :: IsScalar d r
         => Int -> Int -> DualNumber d (Vector r) -> DualNumber d (Vector r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. V.length u - ksize]]
  in seq1 $ V.fromList $ map maximum0 slices

softMaxActV :: DualMonad d r m
            => DualNumber d (Vector r) -> m (DualNumber d (Vector r))
softMaxActV d@(D u _) = do
  expU <- returnLet $ exp d
  let sumExpU = sumElements0 expU
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpU
  returnLet $ konst1 recipSum (V.length u) * expU

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyL
  :: DualMonad d r m
  => Matrix r
  -> DualNumber d (Matrix r)
  -> m (DualNumber d (Vector r))
lossSoftMaxCrossEntropyL target (D u u') = do
  let expU = exp (u - HM.scalar (HM.maxElement u))  -- vs exploding gradients
      sumExpU = V.fromList $ map HM.sumElements $ HM.toColumns expU
      recipSum = recip sumExpU
      softMaxU = HM.asRow recipSum * expU
                   -- this @asRow@ is safe; multiplied at once
      scaled = D (negate $ log softMaxU * target)
                 (dScale (softMaxU - target) u')
  returnLet $ sumColumns1 scaled


-- * Operations resulting in a matrix

-- @2@ means rank two, so the dual component represents a matrix.
fromRows2 :: IsScalar d r
          => Data.Vector.Vector (DualNumber d (Vector r))
          -> DualNumber d (Matrix r)
fromRows2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                (dFromRows2 $ V.map (\(D _ u') -> u') v)

fromColumns2 :: IsScalar d r
             => Data.Vector.Vector (DualNumber d (Vector r))
             -> DualNumber d (Matrix r)
fromColumns2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                   (dFromColumns2 $ V.map (\(D _ u') -> u') v)

konst2 :: IsScalar d r => DualNumber d r -> (Int, Int) -> DualNumber d (Matrix r)
konst2 (D u u') sz = D (HM.konst u sz) (dKonst2 u' sz)

transpose2 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
transpose2 (D u u') = D (HM.tr' u) (dTranspose2 u')

-- | Dense matrix-matrix product.
--
-- If @u@ is a m x n (number of rows x number of columns) matrix
-- and @v@ is a n x p matrix then the result of @u <>! v@ is a m x p matrix.
infixr 8 <>!
(<>!) :: IsScalar d r
      => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
      -> DualNumber d (Matrix r)
(<>!) (D u u') (D v v') = D (u HM.<> v) (dAdd (dMD_M2 u' v) (dM_MD2 u v'))

-- | Dense matrix-matrix product with a constant matrix.
infixr 8 <>!!
(<>!!) :: IsScalar d r
       => DualNumber d (Matrix r) -> Matrix r
       -> DualNumber d (Matrix r)
(<>!!) (D u u') v = D (u HM.<> v) (dMD_M2 u' v)

rowAppend2 :: IsScalar d r
           => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
           -> DualNumber d (Matrix r)
rowAppend2 (D u u') (D v v') =
  D (u HM.=== v) (dRowAppend2 u' (HM.rows u) v')

columnAppend2 :: IsScalar d r
              => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
              -> DualNumber d (Matrix r)
columnAppend2 (D u u') (D v v') =
  D (u HM.||| v) (dColumnAppend2 u' (HM.cols u) v')

rowSlice2 :: IsScalar d r
          => Int -> Int -> DualNumber d (Matrix r)
          -> DualNumber d (Matrix r)
rowSlice2 i n (D u u') = D (HM.subMatrix (i, 0) (n, HM.cols u) u)
                           (dRowSlice2 i n u' (HM.rows u))

columnSlice2 :: IsScalar d r
             => Int -> Int -> DualNumber d (Matrix r)
             -> DualNumber d (Matrix r)
columnSlice2 i n (D u u') = D (HM.subMatrix (0, i) (HM.rows u, n) u)
                              (dColumnSlice2 i n u' (HM.rows u))

asRow2 :: IsScalar d r
       => DualNumber d (Vector r) -> Int -> DualNumber d (Matrix r)
asRow2 (D u u') n = D (HM.fromRows $ replicate n u) (dAsRow2 u')

asColumn2 :: IsScalar d r
          => DualNumber d (Vector r) -> Int -> DualNumber d (Matrix r)
asColumn2 (D u u') n = D (HM.fromColumns $ replicate n u) (dAsColumn2 u')

fromX2 :: IsScalar d r => DualNumber d (OT.Array r) -> DualNumber d (Matrix r)
fromX2 (D u u') = case OT.shapeL u of
  [_, cols] -> D (HM.reshape cols $ OT.toVector u) (dFromX2 u')
  dims -> error $ "fromX2: the tensor has wrong dimensions " ++ show dims

fromS2 :: forall rows cols d r.
          (KnownNat rows, KnownNat cols, IsScalar d r)
       => DualNumber d (OS.Array '[rows, cols] r) -> DualNumber d (Matrix r)
fromS2 (D u u') = D (HM.reshape (valueOf @cols) $ OS.toVector u) (dFromS2 u')

flipud2 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
flipud2 (D u u') = D (HM.flipud u) (dFlipud2 u')

fliprl2 :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
fliprl2 (D u u') = D (HM.fliprl u) (dFliprl2 u')

vectorSlices2 :: IsScalar d r
              => Int -> DualNumber d (Vector r) -> DualNumber d (Matrix r)
vectorSlices2 n vv@(D v _) =
  fromRows2 $ V.fromList [slice1 i n vv | i <- [0 .. V.length v - n]]

reshape2 :: IsScalar d r
         => Int -> DualNumber d (Vector r) -> DualNumber d (Matrix r)
reshape2 cols (D u u') = D (HM.reshape cols u) (dReshape2 cols u')

-- TODO: This has list of matrices result instead of a cube tensor.
matrixSlices2 :: DualMonad d r m
              => Int -> DualNumber d (Matrix r) -> m [DualNumber d (Matrix r)]
matrixSlices2 dr m@(D u _) = do
  let (rows, cols) = HM.size u
      n = dr * cols
  v <- returnLet $ flatten1 m  -- used many times below
  let f k = returnLet $ reshape2 cols $ slice1 (k * cols) n v
  mapM f [0 .. rows - dr]

-- Not optimal: matrix is constructed and destructed immediately,
-- which is costly when evaluating delta expressions. The transposes
-- may not be optimal, either. This goes down to individual deltas
-- of scalars, which is horrible for performance. Unlike @corr1@
-- this uses the slow dot product instead of the fast matrix-vector
-- (or matrix-matrix) multiplication.
corr2 :: forall d r m. DualMonad d r m
      => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
      -> m (DualNumber d (Matrix r))
corr2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
      rr = rowsM - rowsK + 1
      rc = colsM - colsK + 1
  if | rowsK <= 0 || colsK <= 0 ->
       error $ "corr2: empty kernel not handled: " ++ show (rowsK, colsK)
     | rr <= 0 || rc <= 0 ->
       error $ "corr2: dim kernel " ++ show (rowsK, colsK)
               ++ " > dim matrix " ++ show (rowsM, colsM)
     | otherwise -> do
       kerTransV <- returnLet $ flatten1 (transpose2 ker)
       let dotColSlices :: DualNumber d (Matrix r) -> m [DualNumber d r]
           dotColSlices tm = do
             ttm <- returnLet $ transpose2 tm
             colSlices <- matrixSlices2 colsK ttm
             let f :: DualNumber d (Matrix r) -> DualNumber d r
                 f sm = kerTransV <.>! flatten1 sm
             return $ map f colSlices
       rowSlices <- matrixSlices2 rowsK m
       dotSlicesOfSlices <- mapM dotColSlices rowSlices
       returnLet $ reshape2 rc $ seq1 $ V.fromList $ concat dotSlicesOfSlices

conv2 :: forall d r m. DualMonad d r m
      => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
      -> m (DualNumber d (Matrix r))
conv2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
  if | rowsK <= 0 || colsK <= 0 ->
       returnLet $ konst2 0 (rowsM + rowsK - 1, colsM + colsK - 1)
     | otherwise -> do
       let zRow = konst2 0 (rowsK - 1, colsM)
           rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
           zCol = konst2 0 (rowsM + 2 * (rowsK - 1), colsK - 1)
           padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
       corr2 (fliprl2 . flipud2 $ ker) padded

conv2' :: IsScalar d r
       => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
       -> DualNumber d (Matrix r)
conv2' (D u u') (D v v') = D (HM.conv2 u v) (dAdd (dConv2 u v') (dConv2 v u'))

-- A variant with limited padding, corresponding to SAME padding
-- from Tensorflow. Data size does not change with this padding.
-- It also performs convolution wrt flipped kernel (and so saves
-- on flipping it here), which makes no practical difference when
-- the kernel is initialized randomly.
convSame2 :: forall d r m. DualMonad d r m
          => DualNumber d (Matrix r) -> DualNumber d (Matrix r)
          -> m (DualNumber d (Matrix r))
convSame2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
  if | rowsK <= 0 || colsK <= 0 ->
       returnLet $ konst2 0 (rowsM, colsM)
     | otherwise -> do
       let zRow = konst2 0 ((rowsK - 1) `div` 2, colsM)
           rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
           zCol = konst2 0 (rowsM + rowsK - 1, (colsK - 1) `div` 2)
           padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
       corr2 ker padded

-- No padding; remaining areas ignored.
maxPool2 :: forall d r m. DualMonad d r m
         => Int -> Int -> DualNumber d (Matrix r) -> m (DualNumber d (Matrix r))
maxPool2 ksize stride m@(D u _) = do
  let (rows, cols) = HM.size u
      colsOut = cols `div` stride
      resultRows = [0, stride .. rows - ksize]
      resultCols = [0, stride .. cols - ksize]
      resultCoords = [(r, c) | r <- resultRows, c <- resultCols]
  v <- returnLet $ flatten1 m  -- used many times below
  let getArea :: (Int, Int) -> DualNumber d (Vector r)
      getArea (r0, c0) =
        let getAreaAtRow r1 = append1 (slice1 (r1 * cols + c0) ksize v)
        in foldr getAreaAtRow (seq1 V.empty) [r0 .. r0 + ksize - 1]
      mins = map (maximum0 . getArea) resultCoords
  returnLet $ reshape2 colsOut $ seq1 $ V.fromList mins


-- * Operations resulting in an arbitrary untyped tensor

konstX :: IsScalar d r => DualNumber d r -> OT.ShapeL -> DualNumber d (OT.Array r)
konstX (D u u') sh = D (OT.constant sh u) (dKonstX u' sh)

appendX :: IsScalar d r
        => DualNumber d (OT.Array r) -> DualNumber d (OT.Array r)
        -> DualNumber d (OT.Array r)
appendX (D u u') (D v v') =
  D (u `OT.append` v) (dAppendX u' (head $ OT.shapeL u) v')

sliceX :: IsScalar d r
       => Int -> Int -> DualNumber d (OT.Array r) -> DualNumber d (OT.Array r)
sliceX i n (D u u') = D (OT.slice [(i, n)] u)
                        (dSliceX i n u' (head $ OT.shapeL u))

indexX :: IsScalar d r
       => DualNumber d (OT.Array r) -> Int -> DualNumber d (OT.Array r)
indexX (D u u') ix = D (OT.index u ix)
                       (dIndexX u' ix (head $ OT.shapeL u))

ravelFromListX :: IsScalar d r
               => [DualNumber d (OT.Array r)] -> DualNumber d (OT.Array r)
ravelFromListX ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
      sh = case lu of
        u : _ -> length lu : OT.shapeL u
        [] -> []
  in D (OT.ravel $ OTB.fromList sh lu) (dRavelFromListX lu')

unravelToListX :: IsScalar d r
               => DualNumber d (OT.Array r) -> [DualNumber d (OT.Array r)]
unravelToListX (D v v') = case OT.shapeL v of
  k : _ ->
    let g ix p = D p (dIndexX v' ix k)
    in imap g $ OTB.toList $ OT.unravel v
  [] -> error "unravelToListX: wrong tensor dimensions"  -- catch early

mapX :: IsScalar d r
     => (DualNumber d (OT.Array r) -> DualNumber d (OT.Array r))
     -> DualNumber d (OT.Array r)
     -> DualNumber d (OT.Array r)
mapX f = ravelFromListX . map f . unravelToListX

zipWithX :: IsScalar d r
         => (DualNumber d (OT.Array r) -> DualNumber d (OT.Array r)
             -> DualNumber d (OT.Array r))
         -> DualNumber d (OT.Array r) -> DualNumber d (OT.Array r)
         -> DualNumber d (OT.Array r)
zipWithX f d e =
  ravelFromListX $ zipWith f (unravelToListX d) (unravelToListX e)

reshapeX :: IsScalar d r
         => OT.ShapeL -> DualNumber d (OT.Array r) -> DualNumber d (OT.Array r)
reshapeX sh' (D u u') = D (OT.reshape sh' u) (dReshapeX (OT.shapeL u) sh' u')

from0X :: IsScalar d r => DualNumber d r -> DualNumber d (OT.Array r)
from0X (D u u') = D (OT.scalar u) (dFrom0X u')

from1X :: IsScalar d r => DualNumber d (Vector r) -> DualNumber d (OT.Array r)
from1X (D u u') = D (OT.fromVector [V.length u] u) (dFrom1X u')

from2X :: IsScalar d r => DualNumber d (Matrix r) -> DualNumber d (OT.Array r)
from2X (D u u') = D (OT.fromVector [HM.rows u, HM.cols u] $ HM.flatten u)
                    (dFrom2X u' (HM.cols u))

fromSX :: forall sh d r. (IsScalar d r, OS.Shape sh)
       => DualNumber d (OS.Array sh r) -> DualNumber d (OT.Array r)
fromSX (D u u') = D (Data.Array.Convert.convert u) (dFromSX u')


-- * Operations resulting in an arbitrary fully typed Shaped tensor

konstS :: (IsScalar d r, OS.Shape sh)
       => DualNumber d r -> DualNumber d (OS.Array sh r)
konstS (D u u') = D (OS.constant u) (dKonstS u')

appendS :: (KnownNat m, KnownNat n, IsScalar d r, OS.Shape sh)
        => DualNumber d (OS.Array (m ': sh) r)
        -> DualNumber d (OS.Array (n ': sh) r)
        -> DualNumber d (OS.Array ((m + n) ': sh) r)
appendS (D u u') (D v v') = D (u `OS.append` v) (dAppendS u' v')

sliceS :: forall i n k rest d r.
          (KnownNat i, KnownNat n, KnownNat k, IsScalar d r, OS.Shape rest)
       => DualNumber d (OS.Array (i + n + k ': rest) r)
       -> DualNumber d (OS.Array (n ': rest) r)
sliceS (D u u') = D (OS.slice @'[ '(i, n) ] u)
                    (dSliceS (Proxy :: Proxy i) Proxy u')

indexS :: forall ix k rest d r.
          (KnownNat ix, KnownNat k, IsScalar d r, OS.Shape rest)
       => DualNumber d (OS.Array (ix + 1 + k ': rest) r)
       -> DualNumber d (OS.Array rest r)
indexS (D u u') = D (OS.index u (valueOf @ix))
                    (dIndexS u' (Proxy :: Proxy ix))

ravelFromListS :: forall rest k d r.
                  (KnownNat k, IsScalar d r, OS.Shape rest)
               => [DualNumber d (OS.Array rest r)]
               -> DualNumber d (OS.Array (k : rest) r)
ravelFromListS ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
  in D (OS.ravel $ OSB.fromList lu) (dRavelFromListS lu')

unravelToListS :: forall k rest d r.
                  (KnownNat k, IsScalar d r, OS.Shape rest)
               => DualNumber d (OS.Array (k : rest) r)
               -> [DualNumber d (OS.Array rest r)]
unravelToListS (D v v') =
  -- @dIndexS@ is rigid, with type-level bound-checking, so we have to switch
  -- to @dIndexX@ for this function.
  let g ix p = D p (dFromXS $ dIndexX (dFromSX v') ix (valueOf @k))
  in imap g $ OSB.toList $ OS.unravel v

mapS :: forall k sh1 sh d r. (KnownNat k, IsScalar d r, OS.Shape sh, OS.Shape sh1)
     => (DualNumber d (OS.Array sh1 r) -> DualNumber d (OS.Array sh r))
     -> DualNumber d (OS.Array (k : sh1) r)
     -> DualNumber d (OS.Array (k : sh) r)
mapS f = ravelFromListS . map f . unravelToListS

mapMS :: forall k sh1 sh d r m.
         (Monad m, KnownNat k, IsScalar d r, OS.Shape sh, OS.Shape sh1)
      => (DualNumber d (OS.Array sh1 r) -> m (DualNumber d (OS.Array sh r)))
      -> DualNumber d (OS.Array (k : sh1) r)
      -> m (DualNumber d (OS.Array (k : sh) r))
mapMS f d = do
  let ld = unravelToListS d
  ld2 <- mapM f ld
  return $! ravelFromListS ld2

zipWithS :: forall k sh1 sh2 sh d r.
            ( KnownNat k, IsScalar d r, OS.Shape sh, OS.Shape sh1, OS.Shape sh2)
         => (DualNumber d (OS.Array sh1 r) -> DualNumber d (OS.Array sh2 r)
             -> DualNumber d (OS.Array sh r))
         -> DualNumber d (OS.Array (k : sh1) r)
         -> DualNumber d (OS.Array (k : sh2) r)
         -> DualNumber d (OS.Array (k : sh) r)
zipWithS f d e =
  ravelFromListS $ zipWith f (unravelToListS d) (unravelToListS e)

reshapeS :: (IsScalar d r, OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
         => DualNumber d (OS.Array sh r) -> DualNumber d (OS.Array sh' r)
reshapeS (D u u') = D (OS.reshape u) (dReshapeS u')

-- TODO: generalize as broadcast or stretch
asRowS :: forall k n d r. (IsScalar d r, KnownNat k, KnownNat n)
       => DualNumber d (OS.Array '[k] r) -> DualNumber d (OS.Array '[n, k] r)
asRowS d = from2S $ asRow2 (fromS1 d) (valueOf @n)

asColumnS :: forall k n d r. (IsScalar d r, KnownNat k, KnownNat n)
          => DualNumber d (OS.Array '[k] r) -> DualNumber d (OS.Array '[k, n] r)
asColumnS d = from2S $ asColumn2 (fromS1 d) (valueOf @n)

from0S :: IsScalar d r => DualNumber d r -> DualNumber d (OS.Array '[] r)
from0S (D u u') = D (OS.scalar u) (dFrom0S u')

from1S :: (KnownNat n, IsScalar d r)
       => DualNumber d (Vector r) -> DualNumber d (OS.Array '[n] r)
from1S (D u u') = D (OS.fromVector u) (dFrom1S u')

from2S :: (KnownNat rows, KnownNat cols, IsScalar d r)
       => DualNumber d (Matrix r) -> DualNumber d (OS.Array '[rows, cols] r)
from2S (D u u') = D (OS.fromVector $ HM.flatten u) (dFrom2S Proxy u')

fromXS :: (IsScalar d r, OS.Shape sh)
       => DualNumber d (OT.Array r) -> DualNumber d (OS.Array sh r)
fromXS (D u u') = D (Data.Array.Convert.convert u) (dFromXS u')

-- TODO: generalize to arbitrary permutations of arbitrarily many ranks using https://hackage.haskell.org/package/orthotope/docs/Data-Array-ShapedS.html#v:transpose
transpose2S :: (IsScalar d r, KnownNat rows, KnownNat cols)
            => DualNumber d (OS.Array '[rows, cols] r)
            -> DualNumber d (OS.Array '[cols, rows] r)
transpose2S = from2S . transpose2 . fromS2

infixr 8 #>$
(#>$) :: (IsScalar d r, KnownNat rows, KnownNat cols)
      => DualNumber d (OS.Array '[rows, cols] r)
      -> DualNumber d (OS.Array '[cols] r)
      -> DualNumber d (OS.Array '[rows] r)
(#>$) d e = from1S $ fromS2 d #>! fromS1 e

infixr 8 <>$
(<>$) :: (IsScalar d r, KnownNat m, KnownNat n, KnownNat p)
      => DualNumber d (OS.Array '[m, n] r)
      -> DualNumber d (OS.Array '[n, p] r)
      -> DualNumber d (OS.Array '[m, p] r)
(<>$) d e = from2S $ fromS2 d <>! fromS2 e

conv2S :: forall d r kheight_minus_1 kwidth_minus_1 in_height in_width.
          ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
          , KnownNat in_height, KnownNat in_width
          , IsScalar d r )
       => DualNumber d (OS.Array '[kheight_minus_1 + 1, kwidth_minus_1 + 1] r)
       -> DualNumber d (OS.Array '[in_height, in_width] r)
       -> DualNumber d (OS.Array '[ in_height + kheight_minus_1
                                 , in_width + kwidth_minus_1 ] r)
conv2S ker x = from2S $ conv2' (fromS2 ker) (fromS2 x)

-- Convolution of many matrices at once. Some of the names of dimensions
-- are from https://www.tensorflow.org/api_docs/python/tf/nn/conv2d
conv24 :: forall kheight_minus_1 kwidth_minus_1
                 out_channels in_height in_width batch_size in_channels d r.
          ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
          , KnownNat out_channels, KnownNat in_height, KnownNat in_width
          , KnownNat batch_size, KnownNat in_channels
          , IsScalar d r )
       => DualNumber d (OS.Array '[ out_channels, in_channels
                                 , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
       -> DualNumber d (OS.Array '[batch_size, in_channels, in_height, in_width] r)
       -> DualNumber d (OS.Array '[ batch_size, out_channels
                                 , in_height + kheight_minus_1
                                 , in_width + kwidth_minus_1 ] r)
conv24 ker = mapS conv23 where
  conv23 :: DualNumber d (OS.Array '[in_channels, in_height, in_width] r)
         -> DualNumber d (OS.Array '[ out_channels
                                   , in_height + kheight_minus_1
                                   , in_width + kwidth_minus_1 ] r)
  conv23 x = mapS (convFilters x) ker
  convFilters
    :: DualNumber d (OS.Array '[in_channels, in_height, in_width] r)
    -> DualNumber d (OS.Array '[ in_channels
                              , kheight_minus_1 + 1, kwidth_minus_1 + 1 ] r)
    -> DualNumber d (OS.Array '[ in_height + kheight_minus_1
                              , in_width + kwidth_minus_1 ] r)
  convFilters x ker1 = sumOutermost $ zipWithS conv2S ker1 x
  sumOutermost :: DualNumber d (OS.Array '[ in_channels
                                         , in_height + kheight_minus_1
                                         , in_width + kwidth_minus_1 ] r)
               -> DualNumber d (OS.Array '[ in_height + kheight_minus_1
                                         , in_width + kwidth_minus_1 ] r)
  sumOutermost = sum . unravelToListS
    -- slow; should go through Tensor2, or the Num instance should when possible

maxPool24
  :: forall ksize_minus_1 stride in_height in_width batch_size channels d r m.
     ( KnownNat ksize_minus_1, KnownNat stride
     , KnownNat in_height, KnownNat in_width
     , KnownNat batch_size, KnownNat channels
     , 1 <= stride
     , ksize_minus_1 <= in_height
     , ksize_minus_1 <= in_width
     , 1 <= in_height - ksize_minus_1 + stride
     , 1 <= in_width - ksize_minus_1 + stride
     , DualMonad d r m )
     => DualNumber d (OS.Array '[batch_size, channels, in_height, in_width] r)
     -> m (DualNumber d
             (OS.Array '[ batch_size, channels
                         , (in_height - ksize_minus_1) `DivRoundUp` stride
                         , (in_width - ksize_minus_1) `DivRoundUp` stride ] r))
maxPool24 d = do
  res <- mapMS (mapMS (fmap from2S
                       . maxPool2 (valueOf @ksize_minus_1 + 1)
                                  (valueOf @stride)
                       . fromS2)) d
  returnLet res


-- * Operations creating delayed/outlined derivatives

-- | The version of the @D@ constructor lazy in the second argument.
-- To be used as in
--
-- > sinDelayed :: (Floating a, IsPrimal d a) => DualNumber d a -> DualNumber d a
-- > sinDelayed (D u u') = delayD (sin u) (dScale (cos u) u')
-- >
-- > plusDelayed :: (Floating a, IsPrimal d a)
-- >             => DualNumber d a -> DualNumber d a -> DualNumber d a
-- > plusDelayed (D u u') (D v v') = delayD (u + v) (dAdd u' v')
-- >
-- > x ** (sinDelayed x `plusDelayed` (id2 $ id2 $ id2 $ konst1 (sumElements0 x) 2))
--
-- The outlining is lost when serializing or logging, unlike with @Out@,
-- @Outline0@, etc.
--
-- Yet another incomparable variant that can't be serialized would be
-- (illustrating with an example of a constructor at rank 0)
--
-- > FromParams0 (Domains -> Delta0 r)
--
-- that expects the initial parameters. But it's more troublesome
-- than @Delay0@ both in implementation and usage.
delayD :: IsPrimal d a => a -> Dual d a -> DualNumber d a
delayD u ~u' = D u (dDelay u')

-- | A wrapper type to delay/outline computation of the derivatives of the given
-- primitive numeric function inside the dual component of the created dual
-- number. The rule is that if all arguments of a function are wrapped
-- in @Out@ then the function gets delayed. Inconsistent wrapping,
-- e.g., only one of the arguments, leads to early type errors.
--
-- To be used as in
--
-- > x ** unOut (sin (Out x) + Out (id $ id $ id $ konst1 (sumElements0 x) 2))
--
-- which delays computing the dual component of sine and of addition
-- (both in rank 1), but not of power, konst and sumElements. The last two
-- can't be currently delayed, because only primitive numeric functions
-- are supported (an attempt would not type-check).
newtype Out a = Out {unOut :: a}
  deriving (Eq, Ord)

returnOut :: (DualMonad d r m, IsPrimalWithScalar d a r)
          => Out (DualNumber d a) -> m (Out (DualNumber d a))
returnOut dOut = do
  dvar <- returnLet $ unOut dOut
  return $ Out dvar

instance (Num a, IsPrimal 'DModeGradient a, HasVariables a)
         => Num (Out (DualNumber 'DModeGradient a)) where
  Out (D u u') + Out (D v v') =
    Out $ D (u + v) (dOutline PlusOut [u, v] [u', v'])
  Out (D u u') - Out (D v v') =
    Out $ D (u - v) (dOutline MinusOut [u, v] [u', v'])
  Out (D u u') * Out (D v v') =
    Out $ D (u * v) (dOutline TimesOut [u, v] [u', v'])
  negate (Out (D v v')) = Out $ D (negate v) (dOutline NegateOut [v] [v'])
  abs (Out (D v v')) = Out $ D (abs v) (dOutline AbsOut [v] [v'])
  signum (Out (D v v')) = Out $ D (signum v) (dOutline SignumOut [v] [v'])
  fromInteger = Out . constant . fromInteger

instance (Real a, IsPrimal 'DModeGradient a, HasVariables a)
         => Real (Out (DualNumber 'DModeGradient a)) where
  toRational = undefined  -- TODO?

instance (Fractional a, IsPrimal 'DModeGradient a, HasVariables a)
         => Fractional (Out (DualNumber 'DModeGradient a)) where
  Out (D u u') / Out (D v v') =
    Out $ D (u / v) (dOutline DivideOut [u, v] [u', v'])
  recip (Out (D v v')) = Out $ D (recip v) (dOutline RecipOut [v] [v'])
  fromRational = Out . constant . fromRational

instance (Floating a, IsPrimal 'DModeGradient a, HasVariables a)
         => Floating (Out (DualNumber 'DModeGradient a)) where
  pi = Out $ constant pi
  exp (Out (D u u')) = Out $ D (exp u) (dOutline ExpOut [u] [u'])
  log (Out (D u u')) = Out $ D (log u) (dOutline LogOut [u] [u'])
  sqrt (Out (D u u')) = Out $ D (sqrt u) (dOutline SqrtOut [u] [u'])
  Out (D u u') ** Out (D v v') =
    Out $ D (u ** v) (dOutline PowerOut [u, v] [u', v'])
  logBase (Out (D u u')) (Out (D v v')) = Out $ D (logBase u v) (dOutline LogBaseOut [u, v] [u', v'])
  sin (Out (D u u')) = Out $ D (sin u) (dOutline SinOut [u] [u'])
  cos (Out (D u u')) = Out $ D (cos u) (dOutline CosOut [u] [u'])
  tan (Out (D u u')) = Out $ D (tan u) (dOutline TanOut [u] [u'])
  asin (Out (D u u')) = Out $ D (asin u) (dOutline AsinOut [u] [u'])
  acos (Out (D u u')) = Out $ D (acos u) (dOutline AcosOut [u] [u'])
  atan (Out (D u u')) = Out $ D (atan u) (dOutline AtanOut [u] [u'])
  sinh (Out (D u u')) = Out $ D (sinh u) (dOutline SinhOut [u] [u'])
  cosh (Out (D u u')) = Out $ D (cosh u) (dOutline CoshOut [u] [u'])
  tanh (Out (D u u')) = Out $ D (tanh u) (dOutline TanhOut [u] [u'])
  asinh (Out (D u u')) = Out $ D (asinh u) (dOutline AsinhOut [u] [u'])
  acosh (Out (D u u')) = Out $ D (acosh u) (dOutline AcoshOut [u] [u'])
  atanh (Out (D u u')) = Out $ D (atanh u) (dOutline AtanhOut [u] [u'])

instance (RealFrac a, IsPrimal 'DModeGradient a, HasVariables a)
         => RealFrac (Out (DualNumber 'DModeGradient a)) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFloat a, IsPrimal 'DModeGradient a, HasVariables a)
         => RealFloat (Out (DualNumber 'DModeGradient a)) where
  atan2 (Out (D u u')) (Out (D v v')) =
    Out $ D (atan2 u v) (dOutline Atan2Out [u, v] [u', v'])
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain


-- * Busywork to let the derivatives mode ignore all outlining

-- | Note that this should apply only when @d@ is @'DModeDerivative@.
-- However, GHC can't tell that @d@ has only two cases. Therefore, we need
-- to overgeneralize these definitions and mark them with @OVERLAPPABLE@
-- or else GHC complains that not enough instances are given
-- whenever type-checking code polymorphic on @d@.
instance {-# OVERLAPPABLE #-} (Num a, IsPrimal d a)
                              => Num (Out (DualNumber d a)) where
  Out d + Out e = Out (d + e)
  Out d - Out e = Out (d - e)
  Out d * Out e = Out (d * e)
  negate (Out e) = Out (negate e)
  abs (Out e) = Out (abs e)
  signum (Out e) = Out (signum e)
  fromInteger = Out . constant . fromInteger

instance {-# OVERLAPPABLE #-} (Real a, IsPrimal d a)
                              => Real (Out (DualNumber d a)) where
  toRational = undefined  -- TODO?

instance {-# OVERLAPPABLE #-} (Fractional a, IsPrimal d a)
                              => Fractional (Out (DualNumber d a)) where
  Out d / Out e = Out (d / e)
  recip (Out e) = Out (recip e)
  fromRational = Out . constant . fromRational

instance {-# OVERLAPPABLE #-} (Floating a, IsPrimal d a)
                              => Floating (Out (DualNumber d a)) where
  pi = Out $ constant pi
  exp (Out d) = Out (exp d)
  log (Out d) = Out (log d)
  sqrt (Out d) = Out (sqrt d)
  Out d ** Out e = Out (d ** e)
  logBase (Out x) (Out y) = Out (logBase x y)
  sin (Out d) = Out (sin d)
  cos (Out d) = Out (cos d)
  tan (Out d) = Out (tan d)
  asin (Out d) = Out (asin d)
  acos (Out d) = Out (acos d)
  atan (Out d) = Out (atan d)
  sinh (Out d) = Out (sinh d)
  cosh (Out d) = Out (cosh d)
  tanh (Out d) = Out (tanh d)
  asinh (Out d) = Out (asinh d)
  acosh (Out d) = Out (acosh d)
  atanh (Out d) = Out (atanh d)

instance {-# OVERLAPPABLE #-} (RealFrac a, IsPrimal d a)
                              => RealFrac (Out (DualNumber d a)) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance {-# OVERLAPPABLE #-} (RealFloat a, IsPrimal d a)
                              => RealFloat (Out (DualNumber d a)) where
  atan2 (Out d) (Out e) = Out (atan2 d e)
