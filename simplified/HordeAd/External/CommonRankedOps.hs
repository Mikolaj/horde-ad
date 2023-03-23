{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.CommonRankedOps
  ( module HordeAd.External.CommonRankedOps
  ) where

import Prelude

import Data.Boolean
import GHC.TypeLits (KnownNat)

import HordeAd.Core.TensorClass

constant0 :: (Tensor r, Tensor (Primal r))
          => Primal r -> r
constant0 = tunScalar . tconstant . tscalar

constant :: (Tensor r, KnownNat n)
         => TensorOf n (Primal r) -> TensorOf n r
constant = tconstant

scale0 :: Tensor r
       => Primal r -> r -> r
scale0 = tscale0

scale :: (r ~ Primal d, Tensor d, KnownNat n)
      => TensorOf n r -> TensorOf n d -> TensorOf n d
scale a d = tconstant a `tmult` d

relu0
  :: forall r. ADReady r
  => r -> r
relu0 x = ifB (x >* 0) x 0

relu, reluLeaky
  :: forall n r. (ADReady r, KnownNat n)
  => TensorOf n r -> TensorOf n r
relu v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0)
                           (tprimalPart v)
  in scale oneIfGtZero v

reluLeaky v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0.01)
                           (tprimalPart v)
  in scale oneIfGtZero v

-- TODO: verify how faster a dedicated Tensor method would be
logistic :: forall r n. (Tensor r, KnownNat n, Floating (TensorOf n (Primal r)))
         => TensorOf n r -> TensorOf n r
logistic d =
  let y = recip (1 + exp (- tprimalPart d))
  in tD y (tScale @r (y * (1 - y)) $ tdualPart d)

-- TODO: and especially here try a faster approach
logistic0 :: (Tensor r, Floating (TensorOf 0 (Primal r)))
          => r -> r
logistic0 = tunScalar . logistic . tscalar

-- TODO: verify how faster a @x * x@ version would be
-- Optimized and more clearly written @u ** 2@.
square :: forall r n. (Tensor r, KnownNat n, Num (TensorOf n (Primal r)))
       => TensorOf n r -> TensorOf n r
square d = let u = tprimalPart d
               u' = tdualPart d
           in tD (u * u) (tScale @r (2 * u) u')

squaredDifference
  :: (Tensor r, KnownNat n, Num (TensorOf n r), Num (TensorOf n (Primal r)))
  => TensorOf n (Primal r) -> TensorOf n r -> TensorOf n r
squaredDifference targ res = square $ res - tconstant targ

squaredDifference0
  :: (Tensor r, Tensor (Primal r))
  => Primal r -> r -> r
squaredDifference0 targ res =
  tunScalar $ squaredDifference (tscalar targ) (tscalar res)

lossCrossEntropyV :: (Tensor r, KnownNat n, Floating (TensorOf n r))
                  => TensorOf n (Primal r)
                  -> TensorOf n r
                  -> r
lossCrossEntropyV targ res =
  negate $ tunScalar $ log res `tdot0` (tconstant targ)

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyV
  :: ( Tensor r, Tensor (Primal r), KnownNat n
     , Floating (TensorOf n (Primal r))
     , Fractional (TensorOf 0 (Primal r)) )
  => TensorOf n (Primal r) -> TensorOf n r -> r
lossSoftMaxCrossEntropyV target d =
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let u = tprimalPart d
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

-- No padding; remaining areas ignored.
maxPool1 :: Tensor r
         => Int -> Int -> TensorOf 1 r -> TensorOf 1 r
maxPool1 ksize stride v =
  let slices = [tslice i ksize v | i <- [0, stride .. tlength v - ksize]]
  in tfromList $ map tmaximum slices

softMaxV :: ( Tensor r, KnownNat n
            , Floating (TensorOf n r), Fractional (TensorOf 0 r) )
         => TensorOf n r -> TensorOf n r
softMaxV d =
  let expU = exp d  -- shared in 2 places, though cse may do this for us
  in tkonst0N (tshape d) (recip $ tsum0 expU) * expU
