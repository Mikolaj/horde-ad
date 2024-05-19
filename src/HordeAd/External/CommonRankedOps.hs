{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on tensors. Too large, too ad hoc or too unlikely
-- to have specialized implementations to be included in the 'RankedTensor'
-- class. Some of the operations may also depend on more than 'RankedTensor',
-- e.g., also on the 'ConvertTensor' class.
module HordeAd.External.CommonRankedOps
  ( module HordeAd.External.CommonRankedOps
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.RankedS as OR
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import           GHC.TypeLits (KnownNat, sameNat)

import Data.Int (Int64)
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

rminIndexN :: ( RankedTensor ranked, KnownNat n, GoodScalar r
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => ranked r n -> IndexOf ranked n
rminIndexN t = fromLinearIdx (rshape t) (rprimalPart $ rminIndex (rflatten t))

rmaxIndexN :: ( RankedTensor ranked, KnownNat n, GoodScalar r
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => ranked r n -> IndexOf ranked n
rmaxIndexN t = fromLinearIdx (rshape t) (rprimalPart $ rmaxIndex (rflatten t))

rminimum :: ( RankedTensor ranked, KnownNat n, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => ranked r n -> ranked r 0
-- The let is required to preserve the sharing of the argument, which is
-- used twice: in rminIndex and in tindex0.
rminimum t0 = rlet t0 $ \t ->
                rindex0 t $ fromLinearIdx (rshape t)
                                          (rprimalPart $ rminIndex (rflatten t))

rmaximum :: ( RankedTensor ranked, KnownNat n, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => ranked r n -> ranked r 0
rmaximum t0 = rlet t0 $ \t ->
                rindex0 t $ fromLinearIdx (rshape t)
                                          (rprimalPart $ rmaxIndex (rflatten t))

rfromIndex0 :: forall r ranked.
               ( RankedTensor ranked
               , GoodScalar r, RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
            => IntOf ranked -> ranked r 0
rfromIndex0 = rfromIntegral . rconstant

rfromIndex1 :: forall n r ranked.
               ( KnownNat n
               , RankedTensor ranked, RankedTensor (PrimalOf ranked)
               , GoodScalar r, RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
            => IndexOf ranked n -> ranked r 1
rfromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconst $ OR.fromList [0] []
  _ -> rfromIntegral . rconstant . rfromList . NonEmpty.fromList . indexToList

rint64FromIndex1 :: forall n ranked.
                    ( KnownNat n
                    , RankedTensor ranked, RankedTensor (PrimalOf ranked)
                    , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
                 => IndexOf ranked n -> ranked Int64 1
rint64FromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconst $ OR.fromList [0] []
  _ -> rconstant . rfromList . NonEmpty.fromList . indexToList

rint64ToIndex1 :: forall n ranked.
                  ( KnownNat n
                  , RankedTensor ranked, RankedTensor (PrimalOf ranked)
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => ranked Int64 1 -> IndexOf ranked n
rint64ToIndex1 v = listToIndex $ runravelToList $ rprimalPart v

rletIx :: ( KnownNat n, KnownNat m, GoodScalar r
          , RankedTensor ranked, RankedTensor (PrimalOf ranked)
          , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
       => IndexOf ranked n -> (IndexOf ranked n -> ranked r m) -> ranked r m
rletIx ix0 f = rlet (rint64FromIndex1 ix0) $ \ixT -> f $ rint64ToIndex1 ixT

scale :: forall ranked r n.
         (ADReady ranked, GoodScalar r, KnownNat n)
      => PrimalOf ranked r n -> ranked r n -> ranked r n
scale a d = rconstant @ranked a * d
-- This should be faster, but is slower. This may be caused by the lets repeated
-- both in primal part and the D constructor.
-- scale a d = rD (a * rprimalPart d) (rScale @r a (rdualPart d))

relu, reluLeaky
  :: forall ranked n r.
     (ADReady ranked, GoodScalar r, KnownNat n, Differentiable r)
  => ranked r n -> ranked r n
relu v0 = rlet v0 $ \v ->
  let oneIfGtZero = rmap0N (\x -> ifF (x <=. 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeaky v0 = rlet v0 $ \v ->
  let oneIfGtZero = rmap0N (\x -> ifF (x <=. 0) 0.01 1.0) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated RankedTensor method would be
logistic :: forall ranked r n.
            ( RankedTensor ranked
            , RankedTensor (PrimalOf ranked), KnownNat n, GoodScalar r
            , Floating (PrimalOf ranked r n), Num (PrimalOf ranked r 0) )
         => ranked r n -> ranked r n
logistic d0 = rlet d0 $ \d ->  -- used in rprimalPart and in tdualPart
  let sh = rshape d
      y0 = recip (rreplicate0N sh 1 + exp (- rprimalPart @ranked d))
  in rlet (rconstant @ranked y0)  -- we don't have rletPrimal
     $ \y1 -> let y = rprimalPart @ranked y1
              in rD y (rScale @ranked (y * (rreplicate0N sh 1 - y))
                       $ rdualPart @ranked d)

-- TODO: verify how faster a @x * x@ version would be
-- Optimized and more clearly written @u ** 2@.
square :: forall ranked r n.
          ( RankedTensor ranked, KnownNat n, Num (PrimalOf ranked r n)
          , GoodScalar r )
       => ranked r n -> ranked r n
square d = let u = rprimalPart @ranked d
               u' = rdualPart @ranked d
           in rD (u * u) (rScale @ranked (2 * u) u')

squaredDifference
  :: forall ranked n r.
     (RankedTensor ranked, KnownNat n, Num (PrimalOf ranked r n), GoodScalar r)
  => PrimalOf ranked r n -> ranked r n -> ranked r n
squaredDifference targ res = square @ranked $ res - rconstant @ranked targ

lossCrossEntropyV
  :: (RankedTensor ranked, KnownNat n, GoodScalar r, Differentiable r)
  => ranked r n -> ranked r n -> ranked r 0
lossCrossEntropyV targ res = negate $ log res `rdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyR
  :: forall ranked n r.
     ( RankedTensor ranked, RankedTensor (PrimalOf ranked), KnownNat n
     , GoodScalar r
     , RankedOf (PrimalOf (PrimalOf ranked)) ~ PrimalOf (PrimalOf ranked)
     , Differentiable r )
  => PrimalOf ranked r n -> ranked r n -> ranked r 0
lossSoftMaxCrossEntropyR target d' = rlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let softMaxU' =
        let u = rprimalPart @ranked d
            expU' = exp (u - rreplicate0N (rshape u) (rminimum u))
        in rlet expU' $ \expU ->
          let sumExpU = rsum0 expU
              recipSum = recip sumExpU
          in rscaleByScalar recipSum expU
               -- not exposed: LA.scaleRecip sumExpU expU
  in rlet (rconstant @ranked softMaxU') $ \softMaxU ->
    rD (negate $ log (rprimalPart @ranked softMaxU) `rdot0` target)
         -- TODO: avoid: log . exp
       (rdualPart @ranked $ (softMaxU - rconstant @ranked target) `rdot0` d)
         -- TODO: probably defining tDot0 would lead to a faster
         -- tDot0 (softMaxU - target) u'

-- No padding; remaining areas ignored.
maxPool1 :: ( RankedTensor ranked, GoodScalar r
            , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
         => Int -> Int -> ranked r 1 -> ranked r 1
maxPool1 ksize stride v =
  let slices = [rslice i ksize v | i <- [0, stride .. rlength v - ksize]]
  in rfromList $ NonEmpty.fromList $ map rmaximum slices

softMax1 :: (RankedTensor ranked, KnownNat n, GoodScalar r, Differentiable r)
         => ranked r n -> ranked r n
softMax1 d =
  let expU0 = exp d
  in rlet expU0 $ \expU -> rreplicate0N (rshape d) (recip $ rsum0 expU) * expU

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
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCoutK, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rdot0 arrAt arrKt
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
  rbuild shOut $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

-- TODO: this makes tests unbearably slow; does it still?
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0Let
  :: forall ranked r n. (ADReady ranked, GoodScalar r, KnownNat n)
  => ranked r n -> IndexOf ranked n -> ranked r 0
indexz0Let d ix0 = rletIx ix0 $ \ix ->
                     ifF (within0 @ranked (rshape @ranked d) ix) (d ! ix) 0

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- Warning: this uses ix twice and within0 again uses it twice,
-- so this variant without rlet should be used only when it's known
-- that ix is of small constant size (e.g., if it contains conditionals
-- that compare big tensors or their minimal elements, it likely is not,
-- unless the tensors are under rlet and only variables representing them
-- are used).
indexz0
  :: forall ranked r n. (ADReady ranked, GoodScalar r, KnownNat n)
  => ranked r n -> IndexOf ranked n -> ranked r 0
indexz0 d ix = ifF (within0 @ranked (rshape @ranked d) ix) (d ! ix) 0

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
  let [batch_size, channels, h, w] = rshape arr
      shOut = [batch_size, channels, h `div` stride, w `div` stride]
      shK1 = [1, 1, ksize, ksize]
  in rbuild shOut $ \case
    [iImg, iChan, iBh, iBw] ->
      let arrt = slicez shK1 arr [ iImg, iChan
                                 , fromIntegral stride * iBh
                                 , fromIntegral stride * iBw ]
      in rmaximum arrt
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"
