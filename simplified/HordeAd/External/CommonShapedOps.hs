{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on tensors. Too large, too ad hoc
-- or too unlikely to have specialized implementations to be included
-- in the `ShapedTensor` class.
module HordeAd.External.CommonShapedOps
  ( module HordeAd.External.CommonShapedOps
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.Boolean
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import           GHC.TypeLits
  (Div, KnownNat, SomeNat (..), someNatVal, type (-), type (<=))
import           Unsafe.Coerce (unsafeCoerce)

import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass

scaleS :: forall shaped r sh.
          (OS.Shape sh, ADReadyS shaped r)
       => PrimalOf shaped r sh -> shaped r sh -> shaped r sh
scaleS a d = sconstant a `smult` d
-- This should be faster, but is slower even before `tmult` is optimized
-- for the scaling case. This may be caused by the lets repeated
-- both in primal part and the D constructor.
-- scale a d = tD (a * tprimalPart d) (tScale @r a (tdualPart d))

reluS, reluLeakyS
  :: forall shaped sh r. (OS.Shape sh, KnownNat (OS.Rank sh), ADReadyS shaped r)
  => shaped r sh -> shaped r sh
reluS v =
  let oneIfGtZero = smap0N (\x -> ifB (x <=* 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeakyS v =
  let oneIfGtZero = smap0N (\x -> ifB (x <=* 0) 0.01 1.0) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated ShapedTensor method would be
logisticS :: forall shaped r sh.
             ( OS.Shape sh, ShapedTensor shaped, GoodScalar r
             , Floating (PrimalOf shaped r sh) )
          => shaped r sh -> shaped r sh
logisticS d0 = slet d0 $ \d ->  -- used in tprimalPart and in tdualPart
  let y0 = recip (1 + exp (- sprimalPart d))
  in slet (sconstant y0)  -- we don't have sletPrimal
     $ \y1 -> let y = sprimalPart y1
              in sD y (sScale @shaped (y * (1 - y)) $ sdualPart d)

-- TODO: verify how faster a @x * x@ version would be
-- Optimized and more clearly written @u ** 2@.
squareS :: forall shaped r sh.
           ( OS.Shape sh, ShapedTensor shaped, Num (PrimalOf shaped r sh)
           , GoodScalar r )
       => shaped r sh -> shaped r sh
squareS d = let u = sprimalPart d
                u' = sdualPart d
            in sD (u * u) (sScale @shaped (2 * u) u')

squaredDifferenceS
  :: forall shaped sh r.
     ( OS.Shape sh, ShapedTensor shaped, Num (PrimalOf shaped r sh)
     , GoodScalar r )
  => PrimalOf shaped r sh -> shaped r sh -> shaped r sh
squaredDifferenceS targ res = squareS $ res - sconstant targ

lossCrossEntropyVS :: ( OS.Shape sh, KnownNat (OS.Size sh)
                      , ShapedTensor shaped, GoodScalar r )
                   => shaped r sh
                   -> shaped r sh
                   -> shaped r '[]
lossCrossEntropyVS targ res = negate $ log res `sdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyS
  :: forall shaped sh r.
     ( OS.Shape sh, KnownNat (OS.Size sh)
     , ShapedTensor shaped, ShapedTensor (PrimalOf shaped), GoodScalar r)
  => PrimalOf shaped r sh -> shaped r sh -> shaped r '[]
lossSoftMaxCrossEntropyS target d' = slet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let softMaxU' =
        let u = sprimalPart d
            expU' = exp (u - sreplicate0N (sminimum u))
        in slet expU' $ \expU ->
          let sumExpU = ssum0 expU
              recipSum = recip sumExpU
          in sscaleByScalar recipSum expU
               -- not exposed: LA.scaleRecip sumExpU expU
  in slet (sconstant softMaxU') $ \softMaxU ->
    sD (negate $ log (sprimalPart softMaxU) `sdot0` target)
         -- TODO: avoid: log . exp
       (sdualPart $ (softMaxU - sconstant target) `sdot0` d)
         -- TODO: probably defining sDot0 would lead to a faster
         -- sDot0 (softMaxU - target) u'

-- No padding; remaining areas ignored.
maxPool1S :: forall ksize stride m shaped r.
             ( KnownNat ksize, KnownNat stride, KnownNat m
             , ShapedTensor shaped, GoodScalar r )
          => shaped r '[m] -> shaped r '[m]
maxPool1S v =
  let l = [0, valueOf @stride .. slength v - valueOf @ksize]
      maxOfSlice i =
        case someNatVal $ toInteger i of
          Just (SomeNat @i _proxy) ->
            gcastWith (unsafeCoerce Refl :: Compare i m :~: LT) $
            gcastWith (unsafeCoerce Refl :: Compare ksize (m - i) :~: LT) $
            smaximum $ sslice @shaped @r @i @(m - i - ksize) @ksize
                              Proxy Proxy v
          Nothing -> error "maxPool1S: impossible someNatVal error"
  in sfromList $ map maxOfSlice l

softMax1S :: ( OS.Shape sh, KnownNat (OS.Size sh)
             , ShapedTensor shaped, GoodScalar r )
          => shaped r sh -> shaped r sh
softMax1S d =
  let expU0 = exp d
  in slet expU0 $ \expU -> sreplicate0N (recip $ ssum0 expU) * expU

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
--
-- It guards the out of bounds indexing behind a conditional
-- to prevent changed values after vectorization,
-- despite the indexing giving 0 when out of bounds.
-- If another value than 0 was needed, the conditional
-- would be necessary even without vectorization.
conv2dUnpaddedS
  :: forall nCoutK nCinpK nKh nKw nImgs nCinpA nAh nAw shaped r shB shK1.
     ( KnownNat nCoutK, KnownNat nCinpK, KnownNat nKh, KnownNat nKw
     , KnownNat nImgs, KnownNat nAh, KnownNat nAw
     , ADReadyS shaped r
     , nCinpA ~ nCinpK
     , shB ~ '[nImgs, nCoutK, nAh, nAw]
     , shK1 ~ '[1, nCinpA, nKh, nKw]
     )
  => shaped r '[nCoutK, nCinpK, nKh, nKw]
  -> shaped r '[nImgs, nCinpA, nAh, nAw]
  -> shaped r shB
conv2dUnpaddedS arrK arrA =
  sbuild @shaped @r @(OS.Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dUnpaddedS: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicezS
  :: forall shOut sh shaped r.
     ( OS.Shape sh, OS.Shape shOut, OS.Shape (OS.Take (OS.Rank sh) shOut)
     , KnownNat (OS.Rank sh)
     , OS.Rank shOut ~ OS.Rank sh, ADReadyS shaped r )
  => shaped r sh -> IndexSh shaped r sh -> shaped r shOut
slicezS d ixBase =
  gcastWith (unsafeCoerce Refl
             :: OS.Rank (OS.Take (OS.Rank shOut) shOut) :~: OS.Rank shOut) $
  gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) shOut :~: '[]) $
  sbuild @shaped @r @(OS.Rank shOut)
  $ \ixResult ->
      indexz0S @shOut d (zipWith_Index (+)
                                       (ShapedList.shapedListToIndex ixBase)
                                       (ShapedList.shapedListToIndex ixResult))

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- The @ShapedList.listToSized@ in the implementation here should not verify
-- that the index fitw inside the type-level shape, because vectorization
-- may make it not fit and that's fine. In the worst case, indexing ingores
-- such invalid indexes and returns 0.
indexz0S
  :: forall shOut sh shaped r. (OS.Shape shOut, OS.Shape sh, ADReadyS shaped r)
  => shaped r sh -> IndexOf shaped r (OS.Rank shOut) -> shaped r '[]
indexz0S d ix =
  gcastWith (unsafeCoerce Refl :: sh OS.++ '[] :~: sh) $
  ifB (within0S @shOut @shaped @r ix)
      (sindex @shaped @r @sh
              d (ShapedList.listToSized (indexToList ix)))
      0

-- | Given an index and shape, check if the index is fully within the shape.
within0S
  :: forall shOut shaped r. (OS.Shape shOut, ADReadyS shaped r)
  => IndexOf shaped r (OS.Rank shOut)
       -- the indexes may be outside shOut and even negative (e.g., for
       -- convolutions with padding)
  -> BooleanOf (IntOf shaped)
within0S ix =
  let within :: IntOf shaped -> IntOf shaped -> BooleanOf (IntOf shaped)
      within i dim = 0 <=* i &&* dim >* i
  in foldr (&&*) true
     $ zipWith within (indexToList ix) (map fromIntegral $ OS.shapeT @shOut)
       -- or use sfromIndex1 and compare vectors?

maxPool2dUnpaddedS
  :: forall ksize stride batch_size channels h w shaped r shOut shK1.
     ( KnownNat ksize, KnownNat stride, KnownNat batch_size, KnownNat channels
     , KnownNat h, KnownNat w
     , 1 <= stride  -- wrongly reported as redundant due to plugins
     , ADReadyS shaped r
     , shOut ~ '[batch_size, channels, h `Div` stride, w `Div` stride]
     , shK1 ~ '[1, 1, ksize, ksize]
     )
  => shaped r '[batch_size, channels, h, w]
  -> shaped r shOut
maxPool2dUnpaddedS arr =
  let stride = valueOf @stride :: Int
  in sbuild @shaped @r @(OS.Rank shOut) $ \case
    [iImg, iChan, iBh, iBw] ->
      let arrt = slicezS @shK1
                         arr [ iImg, iChan
                             , fromIntegral stride * iBh
                             , fromIntegral stride * iBw ]
      in smaximum arrt
    _ -> error "maxPool2dUnpaddedS: impossible pattern needlessly required"
