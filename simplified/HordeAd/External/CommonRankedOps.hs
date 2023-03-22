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
