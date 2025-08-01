{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on shaped tensors.
module HordeAd.External.CommonShapedOps
  ( module HordeAd.External.CommonShapedOps
  ) where

import Prelude

import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Type.Ord (Compare)
import GHC.Exts (IsList (..))
import GHC.TypeLits
  ( Div
  , KnownNat
  , SomeNat (..)
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  , type (<=)
  )

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

sminimum :: forall r sh target. (ADReady target, GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
sminimum t | SNat <- shsProduct (knownShS @sh) =
  tlet (sflatten t) $ \tf ->
    sindex0 tf (tprimalPart (kfromS (sminIndex tf)) :.$ ZIS)

smaximum :: forall r sh target. (ADReady target, GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
smaximum t | SNat <- shsProduct (knownShS @sh) =
  tlet (sflatten t) $ \tf ->
    sindex0 tf (tprimalPart (kfromS (smaxIndex tf)) :.$ ZIS)

sfromIndex0 :: forall r target. (ADReady target, GoodScalar r)
            => IntOf target -> target (TKS '[] r)
sfromIndex0 = sfromR . rfromIntegral . rfromPrimal . rfromK

sfromIndex1 :: forall r sh target.
               (ADReady target, GoodScalar r, KnownShS sh)
            => IxSOf target sh -> target (TKS '[Rank sh] r)
sfromIndex1 | SNat <- shsRank (knownShS @sh) =
  case sameNat (Proxy @(Rank sh)) (Proxy @0) of
    Just Refl -> const $ sconcrete $ Nested.sfromListPrimLinear knownShS []
    _ -> sfromR . rfromIntegral . rfromPrimal . rfromList
         . NonEmpty.fromList . map rfromK . toList

{-
sletIx :: forall r sh n target.
          (ADReady target, GoodScalar r, KnownShS sh, KnownNat n)
       => IxROf target n -> (IxROf target n -> target (TKS sh r))
       -> target (TKS sh r)
sletIx ix0 f = tlet (sfromR @target @Int64 @'[n]
                     $ rint64FromIndex1 ix0) $ \ixT ->
                 f $ rint64ToIndex1 $ rfromS @target ixT
-}

reluS, reluLeakyS
  :: forall target sh r.
     (KnownShS sh, ADReady target, GoodScalar r, Differentiable r)
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
             , KnownShS sh, GoodScalar r, Differentiable r )
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
           , Num (PrimalOf target (TKS sh r)), GoodScalar r )
        => target (TKS sh r) -> target (TKS sh r)
squareS d = let u = sprimalPart d
                u' = sdualPart d
            in tD knownSTK (u * u) (sScale @target (2 * u) u')

squaredDifferenceS
  :: forall target sh r.
     ( KnownShS sh, BaseTensor target, LetTensor target
     , Num (PrimalOf target (TKS sh r)), GoodScalar r )
  => PrimalOf target (TKS sh r) -> target (TKS sh r) -> target (TKS sh r)
squaredDifferenceS targ res = squareS $ res - sfromPrimal targ

lossCrossEntropyVS :: ( KnownShS sh, GoodScalar r, Differentiable r
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
     ( ADReady target, ADReady (PrimalOf target), GoodScalar r, KnownShS sh
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
             ( ADReady target, GoodScalar r
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
             , GoodScalar r, Differentiable r )
          => target (TKS sh r) -> target (TKS sh r)
softMax1S d =
  let expU0 = exp d
  in tlet expU0 $ \expU -> sreplicate0N (recip $ ssum0 expU) * expU

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
conv2dUnpaddedS
  :: forall nCoutK nCinpK nKh nKw nImgs nCinpA nAh nAw
            target r shB shK1.
     ( KnownNat nCoutK, KnownNat nCinpK, KnownNat nKh, KnownNat nKw
     , KnownNat nImgs, KnownNat nAh, KnownNat nAw
     , ADReady target, GoodScalar r
     , nCinpA ~ nCinpK
     , shB ~ '[nImgs, nCoutK, nAh, nAw]
     , shK1 ~ '[1, nCinpA, nKh, nKw]
     )
  => target (TKS '[nCoutK, nCinpK, nKh, nKw] r)
  -> target (TKS '[nImgs, nCinpA, nAh, nAw] r)
  -> target (TKS shB r)
conv2dUnpaddedS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dUnpaddedS: impossible pattern needlessly required"

-- | Full convolution with just enough padding to ensure all output points
--   are affected by the same number of input points,
--   where the output size shrinks depending on the input size and kernel size.
--   Also no input points are ever ignored, though some are read less often.
conv2dShrinkingS
  :: forall nCoutK nCinpK nKh nKw nImgs nCinpA nAh_nKh nAw_nKw
            target r shB shK1.
     ( KnownNat nCoutK, KnownNat nCinpK, KnownNat nKh, KnownNat nKw
     , KnownNat nImgs, KnownNat nAh_nKh, KnownNat nAw_nKw
     , ADReady target, GoodScalar r
     , nCinpA ~ nCinpK
     , shB ~ '[nImgs, nCoutK, nAh_nKh, nAw_nKw]
     , shK1 ~ '[1, nCinpA, nKh, nKw]
     )
  => target (TKS '[nCoutK, nCinpK, nKh, nKw] r)
  -> target (TKS '[nImgs, nCinpA, nAh_nKh + nKh, nAw_nKw + nKw] r)
  -> target (TKS shB r)
conv2dShrinkingS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK [iCout, 0, 0, 0]
      in sdot0 arrAt arrKt
    _ -> error "conv2dShrinkingS: impossible pattern needlessly required"

-- | Full convolution with enough padding to apply kernels at all
-- posiitons that give non-zero results. This corresponds to
-- https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:conv2
-- though it doesn't do kernel flipping.
conv2dPaddedS
  :: forall nCoutK nCinpK nKh nKw nImgs nCinpA nAh nAw
            target r shB shK1.
     ( KnownNat nCoutK, KnownNat nCinpK, KnownNat nKh, KnownNat nKw
     , KnownNat nImgs, KnownNat nAh, KnownNat nAw
     , ADReady target, GoodScalar r, 1 <= nKh, 1 <= nKw
     , nCinpA ~ nCinpK
     , shB ~ '[nImgs, nCoutK, nAh + nKh - 1, nAw + nKw - 1]
     , shK1 ~ '[1, nCinpA, nKh, nKw]
     )
  => target (TKS '[nCoutK, nCinpK, nKh, nKw] r)
  -> target (TKS '[nImgs, nCinpA, nAh, nAw] r)
  -> target (TKS shB r)
conv2dPaddedS arrK arrA =
  sbuild @(Rank shB) $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicezS @shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicezS arrK [iCout, 0, 0, 0]
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
     , KnownNat (Rank sh)
     , Rank shOut ~ Rank sh, ADReady target, GoodScalar r )
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
     , ADReady target, GoodScalar r
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
