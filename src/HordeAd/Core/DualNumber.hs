{-# LANGUAGE AllowAmbiguousTypes, DataKinds, FunctionalDependencies,
             TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others).
module HordeAd.Core.DualNumber where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.ShapedS as OS
import           Data.List.Index (imap)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Vector, (#>), (<.>))
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.DualClass

-- * The main dual number types

data DualNumber a = D (Primal a) a

class (IsScalar r, Monad m, Functor m, Applicative m)
      => DualMonad r m | m -> r where
  returnLet :: IsDualWithScalar a r
            => DualNumber a -> m (DualNumber a)

type Domain r = Vector (Primal r)

type DomainV r = Data.Vector.Vector (Primal (Tensor1 r))

type DomainL r = Data.Vector.Vector (Primal (Tensor2 r))

type DomainX r = Data.Vector.Vector (Primal (TensorX r))

type Domains r = (Domain r, DomainV r, DomainL r, DomainX r)


-- * General non-monadic operations, for any scalar rank

-- This instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (DualNumber r) where

instance Ord (DualNumber r) where

-- These instances are dangerous. Expressions should be wrapped in
-- the monadic @returnLet@ whenever there is a possibility they can be
-- used multiple times in a larger expression. Safer yet, monadic arithmetic
-- operations that already include @returnLet@ should be used instead,
-- such as @+\@, @*\@, etc.
--
-- @Num (Primal r)@ forces @UndecidableInstances@.
instance (Num (Primal r), IsDual r) => Num (DualNumber r) where
  D u u' + D v v' = D (u + v) (dAdd u' v')
  D u u' - D v v' = D (u - v) (dAdd u' (dScale (-1) v'))
  D u u' * D v v' = D (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = D (- v) (dScale (-1) v')
  abs = undefined  -- TODO
  signum = undefined  -- TODO
  fromInteger = scalar . fromInteger

instance (Real (Primal r), IsDual r) => Real (DualNumber r) where
  toRational = undefined  -- TODO?

instance (Fractional (Primal r), IsDual r) => Fractional (DualNumber r) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
    in D (u / v) (dAdd (dScale (v * recipSq) u') (dScale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (dScale minusRecipSq v')
  fromRational = scalar . fromRational

instance (Floating (Primal r), IsDual r) => Floating (DualNumber r) where
  pi = scalar pi
  exp (D u u') = let expU = exp u
                 in D expU (dScale expU u')
  log (D u u') = D (log u) (dScale (recip u) u')
  sqrt = undefined  -- TODO
  D u u' ** D v v' = D (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                                      (dScale ((u ** v) * log u) v'))
  logBase = undefined  -- TODO
  sin (D u u') = D (sin u) (dScale (cos u) u')
  cos (D u u') = D (cos u) (dScale (- (sin u)) u')
  tan = undefined  -- TODO
  asin = undefined  -- TODO
  acos = undefined  -- TODO
  atan = undefined  -- TODO
  sinh = undefined  -- TODO
  cosh = undefined  -- TODO
  tanh (D u u') = let y = tanh u
                  in D y (dScale (1 - y * y) u')
  asinh = undefined  -- TODO
  acosh = undefined  -- TODO
  atanh = undefined  -- TODO

instance (RealFrac (Primal r), IsDual r) => RealFrac (DualNumber r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFloat (Primal r), IsDual r) => RealFloat (DualNumber r) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

scalar :: IsDual a => Primal a -> DualNumber a
scalar a = D a dZero

scale :: (Num (Primal a), IsDual a) => Primal a -> DualNumber a -> DualNumber a
scale a (D u u') = D (a * u) (dScale a u')


-- * Non-monadic operations resulting in a scalar

sumElements0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
sumElements0 (D u u') = D (HM.sumElements u) (dSumElements0 u' (V.length u))

index0 :: IsScalar r
       => DualNumber (Tensor1 r) -> Int -> DualNumber r
index0 (D u u') ix = D (u V.! ix) (dIndex0 u' ix (V.length u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@.
foldl'0 :: IsScalar r
        => (DualNumber r -> DualNumber r -> DualNumber r)
        -> DualNumber r -> DualNumber (Tensor1 r) -> DualNumber r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (dIndex0 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
altSumElements0 = foldl'0 (+) 0

infixr 8 <.>!
(<.>!) :: IsScalar r
       => DualNumber (Tensor1 r)
       -> DualNumber (Tensor1 r)
       -> DualNumber r
(<.>!) (D u u') (D v v') = D (u <.> v) (dAdd (dDot0 v u') (dDot0 u v'))

infixr 8 <.>!!
(<.>!!) :: IsScalar r
        => DualNumber (Tensor1 r)
        -> Primal (Tensor1 r)
        -> DualNumber r
(<.>!!) (D u u') v = D (u <.> v) (dDot0 v u')

fromX0 :: IsScalar r => DualNumber (TensorX r) -> DualNumber r
fromX0 (D u u') = D (OT.unScalar u) (dFromX0 u')

fromS0 :: IsScalarS '[] r => DualNumber (TensorS '[] r) -> DualNumber r
fromS0 (D u u') = D (OS.unScalar u) (dFromS0 u')


-- * Non-monadic operations resulting in a vector

-- @1@ means rank one, that is, creating delta expression of a vector.
deltaSeq1 :: IsScalar r
          => Data.Vector.Vector (DualNumber r) -> DualNumber (Tensor1 r)
deltaSeq1 v = D (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
                (dSeq1 $ V.map (\(D _ u') -> u') v)

konst1 :: IsScalar r => DualNumber r -> Int -> DualNumber (Tensor1 r)
konst1 (D u u') n = D (HM.konst u n) (dKonst1 u' n)

append1 :: IsScalar r
        => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
        -> DualNumber (Tensor1 r)
append1 (D u u') (D v v') = D (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: IsScalar r
       => Int -> Int -> DualNumber (Tensor1 r)
       -> DualNumber (Tensor1 r)
slice1 i n (D u u') = D (V.slice i n u) (dSlice1 i n u' (V.length u))

sumRows1 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
sumRows1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toRows u)
                      (dSumRows1 u' (HM.cols u))

sumColumns1 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
sumColumns1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toColumns u)
                         (dSumColumns1 u' (HM.rows u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@. The detour through a boxed vector (list probably fuses away)
-- is costly, but only matters if @f@ is cheap.
map1 :: IsScalar r
     => (DualNumber r -> DualNumber r)
     -> DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
map1 f (D v v') =
  let k = V.length v
      g ix p = f $ D p (dIndex0 v' ix k)
      ds = imap g $ V.toList v
  in deltaSeq1 $ V.fromList ds

-- | Dense matrix-vector product.
infixr 8 #>!
(#>!) :: IsScalar r
      => DualNumber (Tensor2 r)
      -> DualNumber (Tensor1 r)
      -> DualNumber (Tensor1 r)
(#>!) (D u u') (D v v') = D (u #> v) (dAdd (dMD_V1 u' v) (dM_VD1 u v'))

-- | Dense matrix-vector product with a constant vector.
infixr 8 #>!!
(#>!!) :: IsScalar r
       => DualNumber (Tensor2 r)
       -> Primal (Tensor1 r)
       -> DualNumber (Tensor1 r)
(#>!!) (D u u') v = D (u #> v) (dMD_V1 u' v)

fromX1 :: IsScalar r => DualNumber (TensorX r) -> DualNumber (Tensor1 r)
fromX1 (D u u') = D (OT.toVector u) (dFromX1 u')

fromS1 :: forall len r. (KnownNat len, IsScalarS '[len] r)
       => DualNumber (TensorS '[len] r) -> DualNumber (Tensor1 r)
fromS1 (D u u') = D (OS.toVector u) (dFromS1 @r @len u')


-- * Non-monadic operations resulting in a matrix

-- @2@ means rank two, that is, creating delta expression of a matrix.
fromRows2 :: IsScalar r
          => Data.Vector.Vector (DualNumber (Tensor1 r))
          -> DualNumber (Tensor2 r)
fromRows2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                (dFromRows2 $ V.map (\(D _ u') -> u') v)

fromColumns2 :: IsScalar r
             => Data.Vector.Vector (DualNumber (Tensor1 r))
             -> DualNumber (Tensor2 r)
fromColumns2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                   (dFromColumns2 $ V.map (\(D _ u') -> u') v)

transpose2 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
transpose2 (D u u') = D (HM.tr' u) (dTranspose2 u')

-- | Dense matrix-matrix product.
--
-- If @u@ is a m x n (number of rows x number of columns) matrix
-- and @v@ is a n x p matrix then the result of @u <>! v@ is a m x p matrix.
-- matrix.
infixr 8 <>!
(<>!) :: IsScalar r
      => DualNumber (Tensor2 r)
      -> DualNumber (Tensor2 r)
      -> DualNumber (Tensor2 r)
(<>!) (D u u') (D v v') = D (u HM.<> v) (dAdd (dMD_M2 u' v) (dM_MD2 u v'))

-- | Dense matrix-matrix product with a constant matrix.
infixr 8 <>!!
(<>!!) :: IsScalar r
       => DualNumber (Tensor2 r)
       -> Primal (Tensor2 r)
       -> DualNumber (Tensor2 r)
(<>!!) (D u u') v = D (u HM.<> v) (dMD_M2 u' v)

rowAppend2 :: IsScalar r
           => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
           -> DualNumber (Tensor2 r)
rowAppend2 (D u u') (D v v') =
  D (u HM.=== v) (dRowAppend2 u' (HM.rows u) v')

columnAppend2 :: IsScalar r
              => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
              -> DualNumber (Tensor2 r)
columnAppend2 (D u u') (D v v') =
  D (u HM.||| v) (dColumnAppend2 u' (HM.cols u) v')

rowSlice2 :: IsScalar r
          => Int -> Int -> DualNumber (Tensor2 r)
          -> DualNumber (Tensor2 r)
rowSlice2 i n (D u u') = D (HM.subMatrix (i, 0) (n, HM.cols u) u)
                           (dRowSlice2 i n u' (HM.rows u))

columnSlice2 :: IsScalar r
             => Int -> Int -> DualNumber (Tensor2 r)
             -> DualNumber (Tensor2 r)
columnSlice2 i n (D u u') = D (HM.subMatrix (0, i) (HM.rows u, n) u)
                              (dColumnSlice2 i n u' (HM.rows u))

asRow2 :: IsScalar r => DualNumber (Tensor1 r) -> Int -> DualNumber (Tensor2 r)
asRow2 (D u u') n = D (HM.fromRows $ replicate n u) (dAsRow2 u')

asColumn2 :: IsScalar r => DualNumber (Tensor1 r) -> Int -> DualNumber (Tensor2 r)
asColumn2 (D u u') n = D (HM.fromColumns $ replicate n u) (dAsColumn2 u')

fromX2 :: IsScalar r => DualNumber (TensorX r) -> DualNumber (Tensor2 r)
fromX2 (D u u') = case OT.shapeL u of
  [_, cols] -> D (HM.reshape cols $ OT.toVector u) (dFromX2 u')
  dims -> error $ "fromX2: the tensor has wrong dimensions" ++ show dims

fromS2 :: forall rows cols r.
          (KnownNat rows, KnownNat cols, IsScalarS '[rows, cols] r)
       => DualNumber (TensorS '[rows, cols] r) -> DualNumber (Tensor2 r)
fromS2 (D u u') = D (HM.reshape (valueOf @cols) $ OS.toVector u)
                    (dFromS2 @r @rows @cols u')

-- * Non-monadic operations resulting in an arbitrary tensor

-- Warning: not tested nor benchmarked.

appendX :: IsScalar r
        => DualNumber (TensorX r) -> DualNumber (TensorX r)
        -> DualNumber (TensorX r)
appendX (D u u') (D v v') =
  D (u `OT.append` v) (dAppendX u' (head $ OT.shapeL u) v')

sliceX :: IsScalar r
       => Int -> Int -> DualNumber (TensorX r) -> DualNumber (TensorX r)
sliceX i n (D u u') = D (OT.slice [(i, n)] u)
                        (dSliceX i n u' (head $ OT.shapeL u))

from0X :: IsScalar r => DualNumber r -> DualNumber (TensorX r)
from0X (D u u') = D (OT.scalar u) (dFrom0X u')

from1X :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber (TensorX r)
from1X (D u u') = D (OT.fromVector [V.length u] u) (dFrom1X u')

from2X :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (TensorX r)
from2X (D u u') = D (OT.fromVector [HM.rows u, HM.cols u] $ HM.flatten u)
                    (dFrom2X u' ( HM.cols u))

fromSX :: forall sh r. (OS.Shape sh, IsScalarS sh r)
       => DualNumber (TensorS sh r) -> DualNumber (TensorX r)
fromSX (D u u') = D (Data.Array.Convert.convert u) (dFromSX @r @sh u')


-- * Non-monadic operations resulting in an arbitrary fully typed Shaped tensor

-- Warning: not tested nor benchmarked.

appendS :: ( OS.Shape sh, KnownNat m, KnownNat n, IsScalarS (m ': sh) r
           , IsScalarS (n ': sh) r, IsScalarS ((m + n) ': sh) r )
        => DualNumber (TensorS (m ': sh) r)
        -> DualNumber (TensorS (n ': sh) r)
        -> DualNumber (TensorS ((m + n) ': sh) r)
appendS (D u u') (D v v') = D (u `OS.append` v) (dAppendS u' v')

sliceS :: forall i n k rest r.
          ( OS.Shape rest, KnownNat i, KnownNat n, KnownNat k
          , IsScalarS (i + n + k ': rest) r, IsScalarS (n ': rest) r )
       => DualNumber (TensorS (i + n + k ': rest) r)
       -> DualNumber (TensorS (n ': rest) r)
sliceS (D u u') = D (OS.slice @'[ '(i, n) ] u) (dSliceS @r @i u')

from0S :: IsScalarS '[] r => DualNumber r -> DualNumber (TensorS '[] r)
from0S (D u u') = D (OS.scalar u) (dFrom0S u')

from1S :: (KnownNat n, IsScalarS '[n] r)
       => DualNumber (Tensor1 r) -> DualNumber (TensorS '[n] r)
from1S (D u u') = D (OS.fromVector u) (dFrom1S u')

from2S :: (KnownNat rows, KnownNat cols, IsScalarS '[rows, cols] r)
       => DualNumber (Tensor2 r) -> DualNumber (TensorS '[rows, cols] r)
from2S (D u u') = D (OS.fromVector $ HM.flatten u) (dFrom2S u')

fromXS :: (OS.Shape sh, IsScalarS sh r)
       => DualNumber (TensorX r) -> DualNumber (TensorS sh r)
fromXS (D u u') = D (Data.Array.Convert.convert u) (dFromXS u')

-- * General monadic operations, for any scalar rank

tanhAct :: (DualMonad r m, IsDualWithScalar a r, Floating (Primal a))
        => DualNumber a -> m (DualNumber a)
tanhAct = returnLet . tanh

logistic :: (Floating (Primal a), IsDual a) => DualNumber a -> DualNumber a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in D y (dScale (y * (1 - y)) u')

logisticAct :: (DualMonad r m, IsDualWithScalar a r, Floating (Primal a))
            => DualNumber a -> m (DualNumber a)
logisticAct = returnLet . logistic

-- Optimized and more clearly written @u ** 2@.
square :: (Num (Primal a), IsDual a) => DualNumber a -> DualNumber a
square (D u u') = D (u * u) (dScale (2 * u) u')

squaredDifference :: (Num (Primal a), IsDual a)
                  => Primal a -> DualNumber a -> DualNumber a
squaredDifference targ res = square $ res - scalar targ

lossSquared :: (DualMonad r m, IsDualWithScalar a r)
            => Primal a -> DualNumber a -> m (DualNumber a)
lossSquared targ res = returnLet $ squaredDifference targ res


-- * Monadic operations resulting in a scalar

-- The type permits other ranks, but it's nonsense.
reluAct :: DualMonad r m
           => DualNumber r -> m (DualNumber r)
reluAct (D u u') = returnLet $ D (max 0 u) (dScale (if u > 0 then 1 else 0) u')

sumElementsVectorOfDelta :: IsScalar r
                         => Data.Vector.Vector (DualNumber r)
                         -> DualNumber r
sumElementsVectorOfDelta = V.foldl' (+) 0

softMaxAct :: (DualMonad r m, Floating (Primal r))
           => Data.Vector.Vector (DualNumber r)
           -> m (Data.Vector.Vector (DualNumber r))
softMaxAct us = do
  expUs <- V.mapM (returnLet . exp) us
  let sumExpUs = sumElementsVectorOfDelta expUs
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpUs
  V.mapM (\r -> returnLet $ r * recipSum) expUs

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall m r. (DualMonad r m, Floating (Primal r))
                 => Primal (Tensor1 r)
                 -> Data.Vector.Vector (DualNumber r)
                 -> m (DualNumber r)
lossCrossEntropy targ res = do
  let f :: DualNumber r -> Int -> DualNumber r -> DualNumber r
      f !acc i d = acc + scale (targ V.! i) (log d)
  returnLet $ negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: (DualMonad r m, Floating (Primal (Tensor1 r)))
                  => Primal (Tensor1 r)
                  -> DualNumber (Tensor1 r)
                  -> m (DualNumber r)
lossCrossEntropyV targ res = returnLet $ negate $ log res <.>!! targ

lossSoftMaxCrossEntropyV :: (DualMonad r m, Fractional (Primal r), Floating (Primal (Tensor1 r)))
                         => Primal (Tensor1 r)
                         -> DualNumber (Tensor1 r)
                         -> m (DualNumber r)
lossSoftMaxCrossEntropyV target (D u u') = do
  let expU = exp u
  -- The following would protect from overflows and exploding gradients,
  -- but I have yet to find a test that requires this and guards
  -- against removing or weakening of this mechanism.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106.
  --  expU = exp (u - HM.scalar (V.maximum u))
      sumExpU = HM.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = HM.scaleRecip sumExpU expU
      softMaxU = HM.scale recipSum expU
  returnLet $ D (negate $ log softMaxU <.> target)
                (dDot0 (softMaxU - target) u')


-- * Monadic operations resulting in a vector

reluActV :: DualMonad r m
         => DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r))
reluActV dn@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0) u
  returnLet $ scale oneIfGtZero dn
    -- I have a bad feeling about this

reluLeakyActV :: (DualMonad r m, Fractional (Primal r))
              => DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r))
reluLeakyActV dn@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0.01) u
  returnLet $ scale oneIfGtZero dn

softMaxActV :: (DualMonad r m, Fractional (Primal r), Floating (Primal (Tensor1 r)))
            => DualNumber (Tensor1 r)
            -> m (DualNumber (Tensor1 r))
softMaxActV d@(D u _) = do
  expU <- returnLet $ exp d
  let sumExpU = sumElements0 expU
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpU
  returnLet $ konst1 recipSum (V.length u) * expU

lossSoftMaxCrossEntropyL
  :: (DualMonad r m, Fractional (Primal r), Floating (Primal (Tensor2 r)))
  => Primal (Tensor2 r)
  -> DualNumber (Tensor2 r)
  -> m (DualNumber (Tensor1 r))
lossSoftMaxCrossEntropyL target (D u u') = do
  let expU = exp u
      sumExpU = V.fromList $ map HM.sumElements $ HM.toColumns expU
      recipSum = recip sumExpU
      softMaxU = HM.asRow recipSum * expU
                   -- this @asRow@ is safe; multiplied at once
      scaled = D (negate $ log softMaxU * target)
                 (dScale (softMaxU - target) u')
  returnLet $ sumColumns1 scaled


-- * Monadic operations resulting in a matrix

-- none so far, usually matrices come from parameters and are reduced
-- and only the results are then bound in the monad
