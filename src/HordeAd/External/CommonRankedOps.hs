{-# LANGUAGE OverloadedLists #-}
-- | Commonly used ranked operations on tensors.
module HordeAd.External.CommonRankedOps
  ( module HordeAd.External.CommonRankedOps
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Foldable qualified as Foldable
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import GHC.TypeLits (KnownNat, sameNat)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR)
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

-- This is not only ranked, so move it once we have CommonAnyOps.hs.
assumeEquality :: forall a b r. (a ~ b => r) -> r
assumeEquality = gcastWith (unsafeCoerceRefl :: a :~: b)

rminimum :: forall target n r.
            ( BaseTensor target, ConvertTensor target, LetTensor target
            , NumScalar r )
         => target (TKR n r) -> target (TKScalar r)
rminimum t = tlet (rflatten t) $ \tf ->
               rindex0 tf (tplainPart (kfromR (rargMin tf)) :.: ZIR)

rmaximum :: forall target n r.
            ( BaseTensor target, ConvertTensor target, LetTensor target
            , NumScalar r )
         => target (TKR n r) -> target (TKScalar r)
rmaximum t = tlet (rflatten t) $ \tf ->
               rindex0 tf (tplainPart (kfromR (rargMax tf)) :.: ZIR)

rfromIndex0 :: forall r target.
               (BaseTensor target, ConvertTensor target, NumScalar r)
            => IntOf target -> target (TKR 0 r)
rfromIndex0 = rfromIntegral . rfromK . tfromPlain STKScalar

rfromIndex1 :: forall n r target.
               ( KnownNat n , BaseTensor target
               , BaseTensor (PlainOf target), ConvertTensor (PlainOf target)
               , NumScalar r )
            => IxROf target n -> target (TKR 1 r)
rfromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconcrete $ Nested.remptyArray
  _ -> rfromIntegral . tfromPlain knownSTK . rfromList . NonEmpty.fromList
       . map rfromK . Foldable.toList

{-
rint64FromIndex1 :: forall n target.
                    ( KnownNat n
                    , BaseTensor target, BaseTensor (PrimalOf target) )
                 => IxROf target n -> target (TKR Int 1)
rint64FromIndex1 = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> const $ rconcrete $ Nested.rfromListPrimLinear (0 :$: ZSR) []
  _ -> rfromPrimal . rfromList . NonEmpty.fromList . indexToList

rint64ToIndex1 :: forall n target.
                  ( KnownNat n
                  , BaseTensor target, BaseTensor (PrimalOf target) )
               => target (TKR Int 1) -> IxROf target n
rint64ToIndex1 v = listToIndex $ runravelToList $ rprimalPart v

tletIx :: ( KnownNat n, KnownNat m, NumScalar r
          , BaseTensor target, BaseTensor (PrimalOf target)
          , LetTensor target )
       => IxROf target n -> (IxROf target n -> target (TKR m r))
       -> target (TKR m r)
tletIx ix0 f = tlet (rint64FromIndex1 ix0) $ \ixT -> f $ rint64ToIndex1 ixT
-}

relu, reluLeaky
  :: forall target n r.
     (ADReady target, NumScalar r, KnownNat n, Differentiable r)
  => target (TKR n r) -> target (TKR n r)
relu v0 = tlet v0 $ \v ->
  let oneIfGtZero = rmap0N (\x -> ifH (x <=. 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeaky v0 = tlet v0 $ \v ->
  let oneIfGtZero = rmap0N (\x -> ifH (x <=. 0) 0.01 1.0) v
  in oneIfGtZero * v

logistic :: forall target r n.
            ( BaseTensor target, LetTensor target, BaseTensor (PrimalOf target)
            , KnownNat n, NumScalar r, Differentiable r )
         => target (TKR n r) -> target (TKR n r)
logistic d0 = tlet d0 $ \d ->  -- used in rprimalPart and in tdualPart
  let one = rrepl (rshape d) 1
      y0 = recip (one + exp (- rprimalPart d))
  in tletPrimal y0 $ \y ->
       rfromPrimal y + rfromDual (rScale @target (y * (one - y)) $ rdualPart d)

rsquare :: (NumScalar a, ADReady target)
        => target (TKR n a) -> target (TKR n a)
rsquare x' = tlet x' $ \x -> x * x
  -- slower even symbolically: rsquare x = x ** rrepl (rshape x) 2

-- Optimized and more clearly written @u ** 2@. It's not clear if this is
-- currently faster than @u ** 2@ and in which pipelines, but it's different,
-- so useful as a test.
squareR :: forall target r n.
           ( BaseTensor target, LetTensor target
           , KnownNat n, Num (PrimalOf target (TKR n r)), NumScalar r )
        => target (TKR n r) -> target (TKR n r)
squareR d' = tlet d' $ \d ->
  let u = rprimalPart @target d
      u' = rdualPart @target d
  in tD knownSTK (u * u) (rScale @target (2 * u) u')

squaredDifference
  :: forall target n r.
     ( BaseTensor target, LetTensor target
     , KnownNat n, Num (PrimalOf target (TKR n r)), NumScalar r )
  => PrimalOf target (TKR n r) -> target (TKR n r) -> target (TKR n r)
squaredDifference targ res = squareR @target $ res - rfromPrimal @target targ

lossCrossEntropyV
  :: ( BaseTensor target, ConvertTensor target
     , KnownNat n, NumScalar r, Differentiable r )
  => target (TKR n r) -> target (TKR n r) -> target (TKScalar r)
lossCrossEntropyV targ res = negate $ log res `rdot0` targ

-- | Note that this is equivalent to a composition of softMax and cross entropy
-- only when @expected@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyR
  :: forall target n r.
     ( BaseTensor target, ConvertTensor target, LetTensor target
     , BaseTensor (PrimalOf target), ConvertTensor (PrimalOf target)
     , LetTensor (PrimalOf target)
     , KnownNat n, NumScalar r, Differentiable r )
  => PrimalOf target (TKR n r) -> target (TKR n r) -> target (TKScalar r)
lossSoftMaxCrossEntropyR expected d' = tlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let u = rprimalPart d
      expU' = exp (u - rreplicate0N (rshape u) (rminimum u))
  in tletPrimal expU' $ \expU ->
    let softMaxU0 =
          let sumExpU = rsum0 expU
              recipSum = recip sumExpU
          in rreplicate0N (rshape u) recipSum * expU
    in tletPrimal softMaxU0 $ \softMaxU ->
      tD STKScalar
         (negate $ log softMaxU `rdot0` expected)
           -- TODO: avoid: log . exp
         (kdualPart $ rfromPrimal (softMaxU - expected) `rdot0` d)

-- Fails for empty x'.
logsumexp :: (KnownNat n, NumScalar r, Differentiable r, ADReady target)
          => target (TKR n r) -> target (TKScalar r)
logsumexp x' = tlet x' $ \x -> tlet (rmaximum x) $ \maxx ->
  let shiftedx = x - rreplicate0N (rshape x) maxx
      logged = log (rsum0 (exp shiftedx))
  in logged + maxx

-- | No padding; remaining areas ignored.
maxPool1 :: ( BaseTensor target, ConvertTensor target, LetTensor target
            , NumScalar r )
         => Int -> Int -> target (TKR 1 r) -> target (TKR 1 r)
maxPool1 ksize stride v =
  let slices = [rslice i ksize v | i <- [0, stride .. rwidth v - ksize]]
  in withSNat ((rwidth v - ksize) `div` stride) $ \k ->
       rfromS $ tfromList k STKScalar $ NonEmpty.fromList $ map rmaximum slices

softMax1 :: ( BaseTensor target, LetTensor target, ConvertTensor target
            , KnownNat n, NumScalar r, Differentiable r )
         => target (TKR n r) -> target (TKR n r)
softMax1 d =
  let expU0 = exp d
  in tlet expU0 $ \expU ->
       rreplicate0N (rshape d) (recip $ rsum0 expU) * expU

-- | Unpadded full convolution, where the output image size is the same
-- as the input size.
--
-- BTW, the indexing lower bounds in the code are spurious,
-- so they get simplified away in the resulting AST program.
conv2dSame
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dSame arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCout, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCout, nAh, nAw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rfromK $ rdot0 arrAt arrKt
    _ -> error "conv2dSame: impossible pattern needlessly required"

-- | Full convolution with only enough padding to ensure all output points
-- are affected by the same number of input points,
-- where the output size shrinks depending on the input size and kernel size.
-- Also no input points are ever ignored, though some are read less often.
--
-- This corresponds to
-- https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:corr2
conv2dShrinking
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dShrinking arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCout, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCout, nAh - nKh + 1, nAw - nKw + 1]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [iImg, 0, iBh, iBw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rfromK $ rdot0 arrAt arrKt
    _ -> error "conv2dShrinking: impossible pattern needlessly required"

-- | Full convolution with enough padding to apply kernels at all
-- positions that give non-zero results. This corresponds to
-- https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:conv2
-- though it doesn't do the kernel flipping.
conv2dPadded
  :: (ADReady target, NumScalar r)
  => target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dPadded arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCout, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      shB = [nImgs, nCout, nAh + nKh - 1, nAw + nKw - 1]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let arrAt = slicez shK1 arrA [ iImg, 0
                                   , iBh - fromIntegral nKh + 1
                                   , iBw - fromIntegral nKw + 1 ]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rfromK $ rdot0 arrAt arrKt
    _ -> error "conv2dPadded: impossible pattern needlessly required"

-- | Full convolution with custom padding, where the output image size
-- depends on the input size, kernel size and padding.
conv2dCustomPadded
  :: (ADReady target, NumScalar r)
  => (Int, Int) -> target (TKR 4 r) -> target (TKR 4 r) -> target (TKR 4 r)
conv2dCustomPadded (nPh, nPw) arrK arrA =
  let [nImgs, nCinpA, nAh, nAw] = rshape arrA
      [nCout, nCinpK, nKh, nKw] = rshape arrK
      nCinp = assert (nCinpA == nCinpK `blame` (nCinpA, nCinpK)) nCinpA
      nBh = nAh + 2 * nPh - nKh + 1
      nBw = nAw + 2 * nPw - nKw + 1
      shB = [nImgs, nCout, nBh, nBw]
      shK1 = [1, nCinp, nKh, nKw]
  in rbuild shB $ \case
    [iImg, iCout, iBh, iBw] ->
      let iFh = iBh - fromIntegral nPh
          iFw = iBw - fromIntegral nPw
          arrAt = slicez shK1 arrA [iImg, 0, iFh, iFw]
          arrKt = slicez shK1 arrK [iCout, 0, 0, 0]
      in rfromK $ rdot0 arrAt arrKt
    _ -> error "conv2dCustomPadded: impossible pattern needlessly required"

-- | Slice a section out of a tensor,
--   given a base offset and shape of the section.
--
--   If the slice extends out side the source array then the corresponding
--   elements are set to zero.
slicez
  :: (ADReady target, NumScalar r, KnownNat n)
  => IShR n -> target (TKR n r) -> IxROf target n -> target (TKR n r)
slicez shOut d ixBase =
  rbuild shOut $ \ixResult -> rindex @_ @0 d (ixrZipWith (+) ixBase ixResult)

maxPool2dUnpadded
  :: (ADReady target, NumScalar r)
  => Int -> Int -> target (TKR 4 r) -> target (TKR 4 r)
maxPool2dUnpadded ksize stride arr =
  let [batch_size, channels, h, w] = rshape arr
      shOutR :: IShR 4
      shOutR = [batch_size, channels, h `div` stride, w `div` stride]
      shK1 :: IShR 4
      shK1 = [1, 1, ksize, ksize]
  in
    withShsFromShR shOutR $ \(sh :: ShS shOut) ->
    withKnownShS sh $
    rfromS $ kbuild @shOut $ \case
    [iImg, iChan, iBh, iBw] ->
      rmaximum $ slicez shK1 arr [ iImg, iChan
                                 , fromIntegral stride * iBh
                                 , fromIntegral stride * iBw ]
    _ -> error "maxPool2dUnpadded: impossible pattern needlessly required"

xfromIndex0 :: forall r target.
               (BaseTensor target, ConvertTensor target, NumScalar r)
            => IntOf target -> target (TKX '[] r)
xfromIndex0 = xfromIntegral . xfromK . tfromPlain STKScalar
