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
import Data.Boolean
import GHC.TypeLits (KnownNat)

import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

scale :: forall ranked r n.
         (ADReady ranked r, KnownNat n)
      => PrimalOf ranked r n -> ranked r n -> ranked r n
scale a d = tconstant @ranked a `tmult` d
-- This should be faster, but is slower even before `tmult` is optimized
-- for the scaling case. This may be caused by the lets repeated
-- both in primal part and the D constructor.
-- scale a d = tD (a * tprimalPart d) (tScale @r a (tdualPart d))

relu, reluLeaky
  :: forall ranked n r. (ADReady ranked r, KnownNat n)
  => ranked r n -> ranked r n
relu v =
  let oneIfGtZero = tmap0N (\x -> ifB (x <=* 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeaky v =
  let oneIfGtZero = tmap0N (\x -> ifB (x <=* 0) 0.01 1.0) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated Tensor method would be
logistic :: forall ranked r n.
            ( Tensor ranked
            , Tensor (PrimalOf ranked), KnownNat n, GoodScalar r
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
          (Tensor ranked, KnownNat n, Num (PrimalOf ranked r n), GoodScalar r)
       => ranked r n -> ranked r n
square d = let u = tprimalPart @ranked d
               u' = tdualPart @ranked d
           in tD (u * u) (tScale @ranked (2 * u) u')

squaredDifference
  :: forall ranked n r.
     (Tensor ranked, KnownNat n, Num (PrimalOf ranked r n), GoodScalar r)
  => PrimalOf ranked r n -> ranked r n -> ranked r n
squaredDifference targ res = square @ranked $ res - tconstant @ranked targ

lossCrossEntropyV :: (Tensor ranked, KnownNat n, GoodScalar r)
                  => ranked r n
                  -> ranked r n
                  -> ranked r 0
lossCrossEntropyV targ res = negate $ log res `tdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyR
  :: forall ranked n r.
     (Tensor ranked, Tensor (PrimalOf ranked), KnownNat n, GoodScalar r)
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
maxPool1 :: (Tensor ranked, GoodScalar r)
         => Int -> Int -> ranked r 1 -> ranked r 1
maxPool1 ksize stride v =
  let slices = [tslice i ksize v | i <- [0, stride .. tlength v - ksize]]
  in tfromList $ map tmaximum slices

softMax1 :: (Tensor ranked, KnownNat n, GoodScalar r)
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
  :: ADReady ranked r
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
  :: (ADReady ranked r, KnownNat n)
  => ShapeInt n -> ranked r n -> IndexOf ranked n -> ranked r n
slicez shOut d ixBase =
  tbuild shOut $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0
  :: forall ranked r n. (ADReady ranked r, KnownNat n)
  => ranked r n -> IndexOf ranked n -> ranked r 0
indexz0 d ix = ifB (within0 @ranked @r (tshape @ranked d) ix) (d ! ix) 0

-- | Given an index and shape, check if the index is fully within the shape.
within0
  :: forall ranked r n. ADReady ranked r
  => ShapeInt n -> IndexOf ranked n -> BooleanOf (IntOf ranked)
within0 sh ix =
  let within :: IntOf ranked -> IntOf ranked -> BooleanOf (IntOf ranked)
      within i dim = 0 <=* i &&* dim >* i
  in foldr (&&*) true
     $ zipWith within (indexToList ix) (map fromIntegral $ shapeToList sh)

maxPool2dUnpadded
  :: ADReady ranked r
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
