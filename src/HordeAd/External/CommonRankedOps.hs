{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE ImpredicativeTypes #-}
-- | Commonly used operations on tensors. Too large, too ad hoc or too unlikely
-- to have specialized implementations to be included in the `Tensor` class.
module HordeAd.External.CommonRankedOps
  ( module HordeAd.External.CommonRankedOps
  ) where

import Prelude

import Control.Exception (assert)
import GHC.TypeLits (KnownNat)

import Data.Int (Int64)
import HordeAd.Core.Ast
import HordeAd.Util.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

tminIndexN :: ( RankedTensor ranked, KnownNat n, GoodScalar r
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => ranked r n -> IndexOf ranked n
tminIndexN t = fromLinearIdx (tshape t) (tprimalPart $ tminIndex (tflatten t))

tmaxIndexN :: ( RankedTensor ranked, KnownNat n, GoodScalar r
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => ranked r n -> IndexOf ranked n
tmaxIndexN t = fromLinearIdx (tshape t) (tprimalPart $ tmaxIndex (tflatten t))

tminimum :: ( RankedTensor ranked, KnownNat n, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => ranked r n -> ranked r 0
-- The let is required to preserve the sharing of the argument, which is
-- used twice: in tminIndex and in tindex0.
tminimum t0 = tlet t0 $ \t ->
                tindex0 t $ fromLinearIdx (tshape t)
                                          (tprimalPart $ tminIndex (tflatten t))

tmaximum :: ( RankedTensor ranked, KnownNat n, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => ranked r n -> ranked r 0
tmaximum t0 = tlet t0 $ \t ->
                tindex0 t $ fromLinearIdx (tshape t)
                                          (tprimalPart $ tmaxIndex (tflatten t))

tfromIndex0 :: forall r ranked.
               ( RankedTensor ranked
               , GoodScalar r, RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
            => IntOf ranked -> ranked r 0
tfromIndex0 = tfromIntegral . tconstant

tfromIndex1 :: forall n r ranked.
               ( RankedTensor ranked, RankedTensor (PrimalOf ranked)
               , GoodScalar r, RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
            => IndexOf ranked n -> ranked r 1
tfromIndex1 = tfromIntegral . tconstant . tfromList . indexToList

tint64FromIndex1 :: forall n ranked.
                    ( RankedTensor ranked, RankedTensor (PrimalOf ranked)
                    , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
                 => IndexOf ranked n -> ranked Int64 1
tint64FromIndex1 = tconstant . tfromList . indexToList

tint64ToIndex1 :: forall n ranked.
                  ( KnownNat n
                  , RankedTensor ranked, RankedTensor (PrimalOf ranked)
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => ranked Int64 1 -> IndexOf ranked n
tint64ToIndex1 v =
  let t = tprimalPart v
      l = map (tindex0 t . singletonIndex . fromIntegral) [0 .. tlength v - 1]
  in listToIndex l

tletIx :: ( KnownNat n, KnownNat m, GoodScalar r
          , RankedTensor ranked, RankedTensor (PrimalOf ranked)
          , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
       => IndexOf ranked n -> (IndexOf ranked n -> ranked r m) -> ranked r m
tletIx ix0 f = tlet (tint64FromIndex1 ix0) $ \ixT -> f $ tint64ToIndex1 ixT

scale :: forall ranked r n.
         (ADReady ranked, GoodScalar r, KnownNat n)
      => PrimalOf ranked r n -> ranked r n -> ranked r n
scale a d = tconstant @ranked a * d
-- This should be faster, but is slower. This may be caused by the lets repeated
-- both in primal part and the D constructor.
-- scale a d = tD (a * tprimalPart d) (tScale @r a (tdualPart d))

relu, reluLeaky
  :: forall ranked n r.
     (ADReady ranked, GoodScalar r, KnownNat n, Differentiable r)
  => ranked r n -> ranked r n
relu v0 = tlet v0 $ \v ->
  let oneIfGtZero = tmap0N (\x -> ifF (x <=. 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeaky v0 = tlet v0 $ \v ->
  let oneIfGtZero = tmap0N (\x -> ifF (x <=. 0) 0.01 1.0) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated RankedTensor method would be
logistic :: forall ranked r n.
            ( RankedTensor ranked
            , RankedTensor (PrimalOf ranked), KnownNat n, GoodScalar r
            , Floating (PrimalOf ranked r n), Num (PrimalOf ranked r 0) )
         => ranked r n -> ranked r n
logistic d0 = tlet d0 $ \d ->  -- used in tprimalPart and in tdualPart
  let sh = tshape d
      y0 = recip (treplicate0N sh 1 + exp (- tprimalPart @ranked d))
  in tlet (tconstant @ranked y0)  -- we don't have tletPrimal
     $ \y1 -> let y = tprimalPart @ranked y1
              in tD y (tScale @ranked (y * (treplicate0N sh 1 - y))
                       $ tdualPart @ranked d)

-- TODO: verify how faster a @x * x@ version would be
-- Optimized and more clearly written @u ** 2@.
square :: forall ranked r n.
          ( RankedTensor ranked, KnownNat n, Num (PrimalOf ranked r n)
          , GoodScalar r )
       => ranked r n -> ranked r n
square d = let u = tprimalPart @ranked d
               u' = tdualPart @ranked d
           in tD (u * u) (tScale @ranked (2 * u) u')

squaredDifference
  :: forall ranked n r.
     (RankedTensor ranked, KnownNat n, Num (PrimalOf ranked r n), GoodScalar r)
  => PrimalOf ranked r n -> ranked r n -> ranked r n
squaredDifference targ res = square @ranked $ res - tconstant @ranked targ

lossCrossEntropyV
  :: (RankedTensor ranked, KnownNat n, GoodScalar r, Differentiable r)
  => ranked r n -> ranked r n -> ranked r 0
lossCrossEntropyV targ res = negate $ log res `tdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyR
  :: forall ranked n r.
     ( RankedTensor ranked, RankedTensor (PrimalOf ranked), KnownNat n
     , GoodScalar r, RankedOf (PrimalOf ranked) ~ PrimalOf ranked
     , PrimalOf (PrimalOf ranked) ~ PrimalOf ranked, Differentiable r )
  => PrimalOf ranked r n -> ranked r n -> ranked r 0
lossSoftMaxCrossEntropyR target d' = tlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let softMaxU' =
        let u = tprimalPart @ranked d
            expU' = exp (u - treplicate0N (tshape u) (tminimum u))
        in tlet expU' $ \expU ->
          let sumExpU = tsum0 expU
              recipSum = recip sumExpU
          in tscaleByScalar recipSum expU
               -- not exposed: LA.scaleRecip sumExpU expU
  in tlet (tconstant @ranked softMaxU') $ \softMaxU ->
    tD (negate $ log (tprimalPart @ranked softMaxU) `tdot0` target)
         -- TODO: avoid: log . exp
       (tdualPart @ranked $ (softMaxU - tconstant @ranked target) `tdot0` d)
         -- TODO: probably defining tDot0 would lead to a faster
         -- tDot0 (softMaxU - target) u'

-- No padding; remaining areas ignored.
maxPool1 :: ( RankedTensor ranked, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => Int -> Int -> ranked r 1 -> ranked r 1
maxPool1 ksize stride v =
  let slices = [tslice i ksize v | i <- [0, stride .. tlength v - ksize]]
  in tfromList $ map tmaximum slices

softMax1 :: (RankedTensor ranked, KnownNat n, GoodScalar r, Differentiable r)
         => ranked r n -> ranked r n
softMax1 d =
  let expU0 = exp d
  in tlet expU0 $ \expU -> treplicate0N (tshape d) (recip $ tsum0 expU) * expU

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
--
-- It guards the out of bounds indexing behind a conditional
-- to prevent changed values after vectorization,
-- despite the indexing giving 0 when out of bounds.
-- If another value than 0 was needed, the conditional
-- would be necessary even without vectorization.
conv2dUnpadded
  :: (ADReady ranked, GoodScalar r)
  => ranked r 4 -> ranked r 4 -> ranked r 4
conv2dUnpadded arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = tshape arrA
      [nCoutK, nCinpK, nKh, nKw] = tshape arrK
      nCinp = assert (nCinpA == nCinpK) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in tbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in tdot0 arrAt arrKt
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicez
  :: (ADReady ranked, GoodScalar r, KnownNat n)
  => ShapeInt n -> ranked r n -> IndexOf ranked n -> ranked r n
slicez shOut d ixBase =
  tbuild shOut $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

-- TODO: this makes tests unbearably slow
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0Let
  :: forall ranked r n. (ADReady ranked, GoodScalar r, KnownNat n)
  => ranked r n -> IndexOf ranked n -> ranked r 0
indexz0Let d ix0 = tletIx ix0 $ \ix ->
                     ifF (within0 @ranked (tshape @ranked d) ix) (d ! ix) 0

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- Warning: this uses ix twice and within0 again uses it twice,
-- so this variant without tlet should be used only when it's known
-- that ix is of small constant size (e.g., if it contains conditionals
-- that compare big tensors or their minimal elements, it likely is not,
-- unless the tensors are under tlet and only variables representing them
-- are used).
indexz0
  :: forall ranked r n. (ADReady ranked, GoodScalar r, KnownNat n)
  => ranked r n -> IndexOf ranked n -> ranked r 0
indexz0 d ix = ifF (within0 @ranked (tshape @ranked d) ix) (d ! ix) 0

-- | Given an index and shape, check if the index is fully within the shape.
-- Note that @ix@ is used twice, so should be shared outside.
within0
  :: forall ranked n. ADReady ranked
  => ShapeInt n -> IndexOf ranked n -> BoolOf ranked
within0 sh ix =
  let within :: IntOf ranked -> IntOf ranked -> BoolOf ranked
      within i dim = 0 <=. i &&* dim >. i
  in foldr (&&*) true
     $ zipWith within (indexToList ix) (map fromIntegral $ shapeToList sh)

maxPool2dUnpadded
  :: (ADReady ranked, GoodScalar r)
  => Int -> Int -> ranked r 4 -> ranked r 4
maxPool2dUnpadded ksize stride arr =
  let [batch_size, channels, h, w] = tshape arr
      shOut = [batch_size, channels, h `div` stride, w `div` stride]
      shK1 = [1, 1, ksize, ksize]
  in tbuild shOut $ \case
    [iImg, iChan, iBh, iBw] ->
      let arrt = slicez shK1 arr [ iImg, iChan
                                 , fromIntegral stride * iBh
                                 , fromIntegral stride * iBw ]
      in tmaximum arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"
