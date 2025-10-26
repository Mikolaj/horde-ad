{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on shaped tensors.
module HordeAd.External.CommonShapedOps
  ( module HordeAd.External.CommonShapedOps
  ) where

import Prelude

import Data.List.NonEmpty qualified as NonEmpty
import Data.Type.Equality (gcastWith, (:~:))
import Data.Type.Ord (Compare)
import GHC.Exts (IsList (..))
import GHC.TypeLits
  (Div, KnownNat, SomeNat (..), someNatVal, type (+), type (-), type (<=))

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (ixrFromIxS, ixsFromIxR')
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

sminimum :: forall r sh target. (ADReady target, NumScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
sminimum t | SNat <- shsProduct (knownShS @sh) =
  tlet (sflatten t) $ \tf ->
    sindex0 tf (tplainPart (kfromS (sminIndex tf)) :.$ ZIS)

smaximum :: forall r sh target. (ADReady target, NumScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
smaximum t | SNat <- shsProduct (knownShS @sh) =
  tlet (sflatten t) $ \tf ->
    sindex0 tf (tplainPart (kfromS (smaxIndex tf)) :.$ ZIS)

sfromIndex0 :: forall r target. (ADReady target, NumScalar r)
            => IntOf target -> target (TKS '[] r)
sfromIndex0 = sfromR . rfromIntegral . tfromPlain knownSTK . rfromK

sfromIndex1 :: forall r sh target.
               (ADReady target, NumScalar r, KnownShS sh)
            => IxSOf target sh -> target (TKS '[Rank sh] r)
sfromIndex1 =
  case shsRank (knownShS @sh) of
    SNat' @0 -> const $ sconcrete $ Nested.sfromListPrimLinear knownShS []
    SNat -> sfromR . rfromIntegral . tfromPlain knownSTK . rfromList
            . NonEmpty.fromList . map rfromK . toList

{-
sletIx :: forall r sh n target.
          (ADReady target, NumScalar r, KnownShS sh, KnownNat n)
       => IxROf target n -> (IxROf target n -> target (TKS sh r))
       -> target (TKS sh r)
sletIx ix0 f = tlet (sfromR @target @Int64 @'[n]
                     $ rint64FromIndex1 ix0) $ \ixT ->
                 f $ rint64ToIndex1 $ rfromS @target ixT
-}

reluS, reluLeakyS
  :: forall target sh r.
     (KnownShS sh, ADReady target, NumScalar r, Differentiable r)
  => target (TKS sh r) -> target (TKS sh r)
reluS v0 = tlet v0 $ \v ->
  let oneIfGtZero =
        smap0N (\x -> ifH (x <=. sscalar 0) (sscalar 0.0) (sscalar 1.0)) v
  in oneIfGtZero * v

reluLeakyS v0 = tlet v0 $ \v ->
  let oneIfGtZero =
        smap0N (\x -> ifH (x <=. sscalar 0) (sscalar 00.01) (sscalar 01.0)) v
  in oneIfGtZero * v

logisticS :: forall target r sh.
             ( BaseTensor target, LetTensor target, BaseTensor (PrimalOf target)
             , KnownShS sh, NumScalar r, Differentiable r )
          => target (TKS sh r) -> target (TKS sh r)
logisticS d0 = tlet d0 $ \d ->  -- used in rprimalPart and in sdualPart
  let one = srepl 1
      y0 = recip (one + exp (- sprimalPart d))
  in ttletPrimal y0 $ \y ->
       sfromPrimal y + sfromDual (sScale @target (y * (one - y)) $ sdualPart d)

-- Optimized and more clearly written @u ** 2@. It's not clear if this is
-- currently faster than @u ** 2@ and in which pipelines, but it's different,
-- so useful as a test.
squareS :: forall target r sh.
           ( KnownShS sh, BaseTensor target, LetTensor target
           , Num (PrimalOf target (TKS sh r)), NumScalar r )
        => target (TKS sh r) -> target (TKS sh r)
squareS d' = tlet d' $ \d ->
  let u = sprimalPart d
      u' = sdualPart d
  in tD knownSTK (u * u) (sScale @target (2 * u) u')

squaredDifferenceS
  :: forall target sh r.
     ( KnownShS sh, BaseTensor target, LetTensor target
     , Num (PrimalOf target (TKS sh r)), NumScalar r )
  => PrimalOf target (TKS sh r) -> target (TKS sh r) -> target (TKS sh r)
squaredDifferenceS targ res = squareS $ res - sfromPrimal targ

lossCrossEntropyVS :: ( KnownShS sh, NumScalar r, Differentiable r
                      , BaseTensor target, ConvertTensor target )
                   => target (TKS sh r)
                   -> target (TKS sh r)
                   -> target (TKScalar r)
lossCrossEntropyVS targ res = kfromS $ negate $ log res `sdot0` targ

-- | Note that this is equivalent to a composition of softMax and cross entropy
-- only when @expected@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyS
  :: forall target sh r.
     ( ADReady target, ADReady (PrimalOf target), NumScalar r, KnownShS sh
     , Differentiable r )
  => PrimalOf target (TKS sh r) -> target (TKS sh r) -> target (TKScalar r)
lossSoftMaxCrossEntropyS expected d' = tlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let softMaxU0 =
        let u = sprimalPart d
            expU' = exp (u - sreplicate0N (sminimum u))
        in tlet expU' $ \expU ->
          let sumExpU = ssum0 expU
              recipSum = recip sumExpU
          in sreplicate0N recipSum * expU
  in ttletPrimal softMaxU0 $ \softMaxU -> kfromS $
    tD knownSTK
       (negate $ log softMaxU `sdot0` expected)
         -- TODO: avoid: log . exp
       (sdualPart $ sfromPrimal (softMaxU - expected) `sdot0` d)

-- | No padding; remaining areas ignored.
maxPool1S :: forall ksize stride m target r.
             ( ADReady target, NumScalar r
             , KnownNat ksize, KnownNat stride, KnownNat m )
          => target (TKS '[m] r) -> target (TKS '[m] r)
maxPool1S v =
  let l = [0, valueOf @stride .. swidth v - valueOf @ksize]
      maxOfSlice i =
        case someNatVal $ toInteger i of
          Just (SomeNat @i _proxy) ->
            gcastWith (unsafeCoerceRefl :: Compare i m :~: LT) $
            gcastWith (unsafeCoerceRefl :: Compare ksize (m - i) :~: LT) $
            smaximum $ sslice @i @(m - i - ksize) @ksize SNat SNat SNat v
          Nothing -> error "maxPool1S: impossible someNatVal error"
  in sfromList $ NonEmpty.fromList $ map maxOfSlice l

softMax1S :: forall target sh r.
             ( KnownShS sh, BaseTensor target, LetTensor target
             , NumScalar r, Differentiable r )
          => target (TKS sh r) -> target (TKS sh r)
softMax1S d =
  let expU0 = exp d
  in tlet expU0 $ \expU -> sreplicate0N (recip $ ssum0 expU) * expU

-- | Full convolution, where the output image size is the same
-- as the input size.
conv2dSameS
  :: forall nImgs nCinp nCinpA nCout nAh nAw nKh nKw shK shA shB shK1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh, KnownNat nKw
     , ADReady target, NumScalar r
     , nCinpA ~ nCinp
     , shK  ~ '[nCout, nCinp, nKh, nKw]
     , shA  ~ '[nImgs, nCinp, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh, nAw]
     , shK1 ~ '[1, nCinpA, nKh, nKw]
     )
  => target (TKS shK r) -> target (TKS shA r) -> target (TKS shB r)
conv2dSameS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA
                          [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK
                          [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dSameS: impossible pattern needlessly required"

-- | Full convolution with only enough padding to ensure all output points
-- are affected by the same number of input points,
-- where the output size shrinks depending on the input size and kernel size.
-- Also no input points are ever ignored, though some are read less often.
--
-- This corresponds to
-- https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:corr2
conv2dShrinkingS
  :: forall nImgs nCinp nCinpA nCout nAh_nKh1 nAw_nKw1 nKh1 nKw1
            shK shA shB shK1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh_nKh1, KnownNat nAw_nKw1, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , nCinpA ~ nCinp
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinpA, nAh_nKh1 + nKh1, nAw_nKw1 + nKw1]
     , shB  ~ '[nImgs, nCout, nAh_nKh1, nAw_nKw1]
     , shK1 ~ '[1, nCinpA, nKh1 + 1, nKw1 + 1]
     )
  => target (TKS shK r) -> target (TKS shA r) -> target (TKS shB r)
conv2dShrinkingS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA
                          [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK
                          [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dShrinkingS: impossible pattern needlessly required"

-- | Full convolution with enough padding to apply kernels at all
-- positons that give non-zero results. This corresponds to
-- https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:conv2
-- though it doesn't do the kernel flipping.
conv2dPaddedS
  :: forall nImgs nCinp nCinpA nCout nAh nAw nKh1 nKw1
            shK shA shB shK1
            target r.
     ( KnownNat nImgs, KnownNat nCinp, KnownNat nCout
     , KnownNat nAh, KnownNat nAw, KnownNat nKh1, KnownNat nKw1
     , ADReady target, NumScalar r
     , nCinpA ~ nCinp
     , shK  ~ '[nCout, nCinp, nKh1 + 1, nKw1 + 1]
     , shA  ~ '[nImgs, nCinpA, nAh, nAw]
     , shB  ~ '[nImgs, nCout, nAh + nKh1, nAw + nKw1]
     , shK1 ~ '[1, nCinpA, nKh1 + 1, nKw1 + 1]
     )
  => target (TKS shK r) -> target (TKS shA r) -> target (TKS shB r)
conv2dPaddedS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let nKh1 = valueOf @nKh1
          nKw1 = valueOf @nKw1
          arrAt = slicezS @shK1 arrA
                          [iImg, 0, iBh - nKh1, iBw - nKw1]
          arrKt = slicezS arrK
                          [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dPaddedS: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicezS
  :: forall shOut sh target r.
     ( KnownShS sh, KnownShS shOut, KnownShS (Take (Rank sh) shOut)
     , Rank shOut ~ Rank sh, ADReady target, NumScalar r )
  => target (TKS sh r) -> IxSOf target sh -> target (TKS shOut r)
slicezS d ixBase =
  gcastWith (unsafeCoerceRefl
             :: Rank (Take (Rank shOut) shOut) :~: Rank shOut) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank sh) shOut :~: '[]) $
  sbuild @(Rank shOut)
  $ \ixResult ->
      sindex0 d (ixsFromIxR' knownShS
                 $ ixrZipWith (+) (ixrFromIxS ixBase) (ixrFromIxS ixResult))
      -- TODO: this doesn't work, because ixsZipWith has too strict a type:
      -- sbuild @(Rank shOut) $ \ixResult -> sindex0 d (ixsZipWith (+) ixBase ixResult)

maxPool2dUnpaddedS
  :: forall ksize stride batch_size channels h w target r shOut shK1.
     ( KnownNat ksize, KnownNat stride, KnownNat batch_size, KnownNat channels
     , KnownNat h, KnownNat w
     , 1 <= stride  -- wrongly reported as redundant due to plugins
     , ADReady target, NumScalar r
     , shOut ~ '[batch_size, channels, h `Div` stride, w `Div` stride]
     , shK1 ~ '[1, 1, ksize, ksize]
     )
  => target (TKS '[batch_size, channels, h, w] r)
  -> target (TKS shOut r)
maxPool2dUnpaddedS arr =
  let stride = valueOf @stride :: Int
  in sbuild @(Rank shOut) $ \case
    [iImg, iChan, iBh, iBw] ->
      smaximum $ slicezS @shK1 arr [ iImg, iChan
                                   , fromIntegral stride * iBh
                                   , fromIntegral stride * iBw ]
    _ -> error "maxPool2dUnpaddedS: impossible pattern needlessly required"
