{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
-- | Commonly used ranked operations on tensors.
module HordeAd.External.CommonRankedOps
  ( module HordeAd.External.CommonRankedOps
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, sameNat)

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

-- This is not only ranked, so move it once we have CommonAnyOps.hs.
assumeEquality :: forall a b r. (a ~ b => r) -> r
assumeEquality = gcastWith (unsafeCoerceRefl :: a :~: b)

rminIndexN :: forall target n r.
              (BaseTensor target, ConvertTensor target, GoodScalar r)
           => target (TKR n r) -> IxROf target n
rminIndexN t =
  fromLinearIdx (tprimalPart @target . kconcrete . fromIntegral)
                (rshape t)
                (tprimalPart @target $ kfromR $ rminIndex (rflatten t))

rmaxIndexN :: forall target n r. (
              BaseTensor target, ConvertTensor target, GoodScalar r)
           => target (TKR n r) -> IxROf target n
rmaxIndexN t =
  fromLinearIdx (tprimalPart @target . kconcrete . fromIntegral)
                (rshape t)
                (tprimalPart @target $ kfromR $ rmaxIndex (rflatten t))

rminimum :: forall target n r.
            ( BaseTensor target, ConvertTensor target, LetTensor target
            , KnownNat n, GoodScalar r )
         => target (TKR n r) -> target (TKR 0 r)
-- The let is required to preserve the sharing of the argument, which is
-- used twice: in rminIndex and in rindex0.
rminimum t0 =
  tlet t0 $ \t ->
    rindex0 t
    $ fromLinearIdx (tprimalPart @target . kconcrete . fromIntegral)
                    (rshape t)
                    (tprimalPart @target $ kfromR $ rminIndex (rflatten t))

rmaximum :: forall target n r.
            ( BaseTensor target, ConvertTensor target, LetTensor target
            , KnownNat n, GoodScalar r )
         => target (TKR n r) -> target (TKR 0 r)
rmaximum t0 =
  tlet t0 $ \t ->
    rindex0 t
    $ fromLinearIdx (tprimalPart @target . kconcrete . fromIntegral)
                    (rshape t)
                    (tprimalPart @target $ kfromR $ rmaxIndex (rflatten t))

rfromIndex0 :: forall r target.
               (BaseTensor target, ConvertTensor target, GoodScalar r)
            => IntOf target -> target (TKR 0 r)
rfromIndex0 = rfromIntegral . rfromK . tfromPrimal STKScalar

rfromIndex1 :: forall n r target.
               ( KnownNat n , BaseTensor target
               , BaseTensor (PrimalOf target), ConvertTensor (PrimalOf target)
               , GoodScalar r )
            => IxROf target n -> target (TKR 1 r)
rfromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconcrete $ Nested.rfromListPrimLinear (0 :$: ZSR) []
  _ -> rfromIntegral . rfromPrimal . rfromList . NonEmpty.fromList
       . map rfromK . toList

{-
rint64FromIndex1 :: forall n target.
                    ( KnownNat n
                    , BaseTensor target, BaseTensor (PrimalOf target) )
                 => IxROf target n -> target (TKR Int64 1)
rint64FromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconcrete $ Nested.rfromListPrimLinear (0 :$: ZSR) []
  _ -> rfromPrimal . rfromList . NonEmpty.fromList . indexToList

rint64ToIndex1 :: forall n target.
                  ( KnownNat n
                  , BaseTensor target, BaseTensor (PrimalOf target) )
               => target (TKR Int64 1) -> IxROf target n
rint64ToIndex1 v = listToIndex $ runravelToList $ rprimalPart v

tletIx :: ( KnownNat n, KnownNat m, GoodScalar r
          , BaseTensor target, BaseTensor (PrimalOf target)
          , LetTensor target )
       => IxROf target n -> (IxROf target n -> target (TKR m r))
       -> target (TKR m r)
tletIx ix0 f = tlet (rint64FromIndex1 ix0) $ \ixT -> f $ rint64ToIndex1 ixT
-}

relu, reluLeaky
  :: forall target n r.
     (ADReady target, GoodScalar r, KnownNat n, Differentiable r)
  => target (TKR n r) -> target (TKR n r)
relu v0 = tlet v0 $ \v ->
  let oneIfGtZero =
        rmap0N (\x -> ifH (x <=. rscalar 0) (rscalar 0.0) (rscalar 1.0)) v
  in oneIfGtZero * v

reluLeaky v0 = tlet v0 $ \v ->
  let oneIfGtZero =
        rmap0N (\x -> ifH (x <=. rscalar 0) (rscalar 0.01) (rscalar 1.0)) v
  in oneIfGtZero * v

logistic :: forall target r n.
            ( BaseTensor target, LetTensor target, BaseTensor (PrimalOf target)
            , KnownNat n, GoodScalar r, Differentiable r )
         => target (TKR n r) -> target (TKR n r)
logistic d0 = tlet d0 $ \d ->  -- used in rprimalPart and in tdualPart
  let one = rrepl (rshape d) 1
      y0 = recip (one + exp (- rprimalPart d))
  in ttletPrimal y0 $ \y ->
       rfromPrimal y + rfromDual (rScale @target (y * (one - y)) $ rdualPart d)

-- Optimized and more clearly written @u ** 2@. It's not clear if this is
-- currently faster than @u ** 2@ and in which pipelines, but it's different,
-- so useful as a test.
square :: forall target r n.
          ( BaseTensor target, LetTensor target
          , KnownNat n, Num (PrimalOf target (TKR n r)), GoodScalar r )
       => target (TKR n r) -> target (TKR n r)
square d = let u = rprimalPart @target d
               u' = rdualPart @target d
           in tD knownSTK (u * u) (rScale @target (2 * u) u')

squaredDifference
  :: forall target n r.
     ( BaseTensor target, LetTensor target
     , KnownNat n, Num (PrimalOf target (TKR n r)), GoodScalar r )
  => PrimalOf target (TKR n r) -> target (TKR n r) -> target (TKR n r)
squaredDifference targ res = square @target $ res - rfromPrimal @target targ

lossCrossEntropyV
  :: ( BaseTensor target, ConvertTensor target
     , KnownNat n, GoodScalar r, Differentiable r )
  => target (TKR n r) -> target (TKR n r) -> target (TKScalar r)
lossCrossEntropyV targ res = kfromR $ negate $ log res `rdot0` targ

-- | Note that this is equivalent to a composition of softMax and cross entropy
-- only when @expected@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyR
  :: forall target n r.
     ( BaseTensor target, ConvertTensor target, LetTensor target
     , BaseTensor (PrimalOf target), ConvertTensor (PrimalOf target)
     , LetTensor (PrimalOf target)
     , KnownNat n, GoodScalar r, Differentiable r )
  => PrimalOf target (TKR n r) -> target (TKR n r) -> target (TKScalar r)
lossSoftMaxCrossEntropyR expected d' = tlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let u = rprimalPart d
      expU' = exp (u - rreplicate0N (rshape u) (rminimum u))
  in ttletPrimal expU' $ \expU ->
    let softMaxU0 =
          let sumExpU = rsum0 expU
              recipSum = recip sumExpU
          in rreplicate0N (rshape u) recipSum * expU
    in ttletPrimal softMaxU0 $ \softMaxU -> kfromR $
      tD knownSTK
         (negate $ log softMaxU `rdot0` expected)
           -- TODO: avoid: log . exp
         (rdualPart $ rfromPrimal (softMaxU - expected) `rdot0` d)

-- | No padding; remaining areas ignored.
maxPool1 :: ( BaseTensor target, ConvertTensor target, LetTensor target
            , GoodScalar r )
         => Int -> Int -> target (TKR 1 r) -> target (TKR 1 r)
maxPool1 ksize stride v =
  let slices = [rslice i ksize v | i <- [0, stride .. rwidth v - ksize]]
  in rfromList $ NonEmpty.fromList $ map rmaximum slices

softMax1 :: ( BaseTensor target, LetTensor target
            , KnownNat n, GoodScalar r, Differentiable r )
         => target (TKR n r) -> target (TKR n r)
softMax1 d =
  let expU0 = exp d
  in tlet expU0 $ \expU -> rreplicate0N (rshape d) (recip $ rsum0 expU) * expU

-- | Unpadded full convolution,
--   where the output size is the same as the input size.
--
-- It guards the out of bounds indexing behind a conditional
-- to prevent changed values after vectorization,
-- despite the indexing giving 0 when out of bounds.
-- If another value than 0 was needed, the conditional
-- would be necessary even without vectorization.
--
-- BTW, the indexing lower bounds in the code are spurious,
-- so they get simplified away in the resulting AST program.
conv2dUnpadded
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dUnpadded arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCoutK, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rdot0 arrAt arrKt
    _ -> error "conv2dUnpadded: impossible pattern needlessly required"

-- | Full convolution with custom padding,
--   where the output size depends on the input size, kernel size and padding.
--
-- Here, if padding is not zero, both upper and lower indexing bound checks
-- are non-trivial.
conv2dCustomPadded
  :: (ADReady target, GoodScalar r)
  => (Int, Int) -> target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dCustomPadded (nPh, nPw) arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCoutK, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      nBh = nAh + 2 * nPh - nKh + 1
      nBw = nAw + 2 * nPw - nKw + 1
      shB = [nImgs, nCoutK, nBh, nBw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let iFh = iBh - fromIntegral nPh
          iFw = iBw - fromIntegral nPw
          arrAt = slicez shK1 arrA [iImg, 0, iFh, iFw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rdot0 arrAt arrKt
    _ -> error "conv2dCustomPadded: impossible pattern needlessly required"

-- | Full convolution with just enough padding to ensure all output points
--   are affected by the same number of input points,
--   where the output size shrinks depending on the input size and kernel size.
--   Also no input points are ever ignored, though some are read less often.
--
--   This amount of padding ensures all bounds checks in the code are spurious
--   and will be simplified away in the resulting AST program.
conv2dShrinking
  :: (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dShrinking arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCoutK, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCoutK, nAh - nKh, nAw - nKw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rdot0 arrAt arrKt
    _ -> error "conv2dShrinking: impossible pattern needlessly required"

-- | Full convolution with just enough extra external zero padding
--   to ensure that the output size is the same as the input size
--   and all input points are read the same number of times.
--
--   The same result could be accomplished by tweaking indexes slightly
--   in conv2dUnpadded, but here additionally all bounds checks in the code
--   are spurious and will be simplified away in the resulting AST program.
conv2dPadded
  :: forall target r. (ADReady target, GoodScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dPadded arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCoutK, nCinpK, nKh, nKw] = rshape arrK
      shAPadded = [nImgs, nCinpA, nAh + nKh, nAw + nKw]
      arrAPadded = rbuild @4 @0 @(TKScalar r) @target shAPadded $ \case
        [iImg, iCinp, iPh, iPw] ->
          ifH (iPh <. fromIntegral (nKh `div` 2)
               ||* iPw <. fromIntegral (nKw `div` 2)
               ||* iPh >=. fromIntegral (nAh + nKh `div` 2)
               ||* iPw >=. fromIntegral (nAw + nKw `div` 2))
              (rscalar 0)
              (arrA ! [ iImg
                      , iCinp
                      , iPh - fromIntegral (nKh `div` 2)
                      , iPw - fromIntegral (nKw `div` 2) ])
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCoutK, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrAPadded [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rdot0 arrAt arrKt
    _ -> error "conv2dPadded: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicez
  :: (ADReady target, GoodScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez shOut d ixBase =
  rbuild shOut $ \ixResult -> indexz0 d (zipWith_Index (+) ixBase ixResult)

{-
-- This makes tests unbearably slow, so not used.
--
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
indexz0Let
  :: forall target r n. (ADReady target, GoodScalar r, KnownNat n)
  => target (TKR n r) -> IxROf target n -> target (TKR 0 r)
indexz0Let d ix0 = tletIx ix0 $ \ix ->
                     ifH (within0 @target (rshape @target d) ix) (d ! ix) 0
-}

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
  :: forall target r n. (ADReady target, GoodScalar r, KnownNat n)
  => target (TKR n r) -> IxROf target n -> target (TKR 0 r)
indexz0 d ix = ifH (within0 @target (rshape @target d) ix) (d ! ix) (rscalar 0)

-- | Given an index and shape, check if the index is fully within the shape.
-- Note that @ix@ is used twice, so should be shared outside.
within0
  :: forall target n. (ADReady target, KnownNat n)
  => IShR n -> IxROf target n -> BoolOf target
within0 sh ix =
  let within :: IntOf target -> IntOf target -> BoolOf target
      within i dim = 0 <=. i &&* dim >. i
  in foldr (&&*) true
     $ zipWith within (toList ix) (map fromIntegral $ toList sh)

maxPool2dUnpadded
  :: (ADReady target, GoodScalar r)
  => Int -> Int -> target (TKR 4 r) -> target (TKR 4 r)
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

xfromIndex0 :: forall r target.
               (BaseTensor target, ConvertTensor target, GoodScalar r)
            => IntOf target -> target (TKX '[] r)
xfromIndex0 = xfromIntegral . xfromK . tfromPrimal STKScalar
