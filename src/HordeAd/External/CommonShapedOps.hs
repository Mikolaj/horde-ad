{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on tensors.
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
  (Div, KnownNat, SomeNat (..), sameNat, someNatVal, type (-), type (<=))

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

sminIndexN :: forall target sh r. (ADReady target, GoodScalar r, KnownShS sh)
           => target (TKS sh r) -> IxSOf target sh
sminIndexN t =
  fromLinearIdxS
    (tprimalPart @target . kconcrete . fromIntegral)
    (sshape t)
    (tprimalPart @target $ kfromS $ sminIndex (sflatten t))

smaxIndexN :: forall target sh r. (ADReady target, GoodScalar r, KnownShS sh)
           => target (TKS sh r) -> IxSOf target sh
smaxIndexN t =
  fromLinearIdxS
    (tprimalPart @target . kconcrete . fromIntegral)
    (sshape t)
    (tprimalPart @target $ kfromS $ smaxIndex (sflatten t))

sminimum :: forall r sh target. (ADReady target, GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
sminimum t = sindex0 t (sminIndexN t)

smaximum :: forall r sh target. (ADReady target, GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS '[] r)
smaximum t = sindex0 t (smaxIndexN t)

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
       => IxROf target n -> (IxROf target n -> target (TKS sh r)) -> target (TKS sh r)
sletIx ix0 f = tlet (sfromR @target @Int64 @'[n]
                     $ rint64FromIndex1 ix0) $ \ixT ->
                 f $ rint64ToIndex1 $ rfromS @target ixT
-}

scaleS :: forall target r sh.
          (KnownShS sh, ADReady target, GoodScalar r)
       => PrimalOf target (TKS sh r) -> target (TKS sh r) -> target (TKS sh r)
scaleS a d = sfromPrimal a * d

reluS, reluLeakyS
  :: forall target sh r.
     (KnownShS sh, ADReady target, GoodScalar r, Differentiable r)
  => target (TKS sh r) -> target (TKS sh r)
reluS v0 = tlet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifH (x <=. sscalar 0) (sscalar 0.0) (sscalar 1.0)) v
  in oneIfGtZero * v

reluLeakyS v0 = tlet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifH (x <=. sscalar 0) (sscalar 00.01) (sscalar 01.0)) v
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

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyS
  :: forall target sh r.
     ( ADReady target, ADReady (PrimalOf target), GoodScalar r, KnownShS sh
     , Differentiable r )
  => PrimalOf target (TKS sh r) -> target (TKS sh r) -> target (TKScalar r)
lossSoftMaxCrossEntropyS target d' = tlet d' $ \d ->
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
       (negate $ log softMaxU `sdot0` target)
         -- TODO: avoid: log . exp
       (sdualPart $ sfromPrimal (softMaxU - target) `sdot0` d)

-- No padding; remaining areas ignored.
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
--
-- It guards the out of bounds indexing behind a conditional
-- to prevent changed values after vectorization,
-- despite the indexing giving 0 when out of bounds.
-- If another value than 0 was needed, the conditional
-- would be necessary even without vectorization.
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
      indexz0S @shOut d (zipWith_Index (+)
                                       (ixsToIxr ixBase)
                                       (ixsToIxr ixResult))

{-
-- This makes tests unbearably slow, so not used.
--
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- The @ShapedList.listToIndex@ in the implementation here should not verify
-- that the index fits inside the type-level shape, because vectorization
-- may make it not fit and that's fine. In the worst case, indexing ignores
-- such invalid indexes and returns 0.
indexz0SLet
  :: forall shOut sh target r.
     ( KnownShS shOut, KnownNat (Rank shOut), KnownShS sh
     , ADReady target, GoodScalar r )
  => target (TKS sh r) -> IxSOf target shOut -> target (TKS '[] r)
indexz0SLet d ix0 =
  sletIx ix0 $ \ix ->
    ifH (within0S @shOut @target ix)
        (sindex0 d (ShapedList.listToIndex (indexToList ix)))
        (srepl 0)
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
indexz0S
  :: forall shOut sh target r.
     (KnownShS shOut, KnownShS sh, ADReady target, GoodScalar r)
  => target (TKS sh r) -> IxROf target (Rank shOut) -> target (TKS '[] r)
indexz0S d ix | SNat <- shsRank (knownShS @shOut) =
  ifH (within0S @shOut @target ix)
      (sindex0 d (fromList (toList ix)))
      (srepl 0)

-- | Given an index and shape, check if the index is fully within the shape.
-- Note that @ix@ is used twice, so should be shared outside.
within0S
  :: forall shOut target. (KnownShS shOut, ADReady target)
  => IxROf target (Rank shOut)
       -- the indexes may be outside shOut and even negative (e.g., for
       -- convolutions with padding)
  -> BoolOf target
within0S ix | SNat <- shsRank (knownShS @shOut) =
  let within :: IntOf target -> IntOf target -> BoolOf target
      within i dim = 0 <=. i &&* dim >. i
  in foldr (&&*) true
     $ zipWith within (toList ix) (map fromIntegral $ toList $ knownShS @shOut)
       -- or use sfromIndex1 and compare vectors?

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
      let arrt = slicezS @shK1
                         arr [ iImg, iChan
                             , fromIntegral stride * iBh
                             , fromIntegral stride * iBw ]
      in smaximum arrt
    _ -> error "maxPool2dUnpaddedS: impossible pattern needlessly required"
