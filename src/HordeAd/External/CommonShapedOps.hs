{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on tensors. Too large, too ad hoc or too unlikely
-- to have specialized implementations to be included in the 'BaseTensor'
-- class. Some of the operations may also depend on more than 'BaseTensor',
-- e.g., also on the 'ConvertTensor' class.
module HordeAd.External.CommonShapedOps
  ( module HordeAd.External.CommonShapedOps
  ) where

import Prelude

import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Type.Ord (Compare)
import GHC.TypeLits
  (Div, KnownNat, SomeNat (..), sameNat, someNatVal, type (-), type (<=))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (KnownShS (..), Rank)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

sminIndexN :: ( ADReady target, GoodScalar r
              , KnownShS sh, KnownNat (Nested.Product sh) )
           => target (TKS r sh) -> IxSOf target sh
sminIndexN t =
  ShapedList.fromLinearIdx (sscalar . fromIntegral)
    (sshape t)
    (sprimalPart $ sminIndex (sflatten t))

smaxIndexN :: ( ADReady target, GoodScalar r
              , KnownShS sh, KnownNat (Nested.Product sh) )
           => target (TKS r sh) -> IxSOf target sh
smaxIndexN t =
  ShapedList.fromLinearIdx (sscalar . fromIntegral)
    (sshape t)
    (sprimalPart $ smaxIndex (sflatten t))

sminimum :: forall r sh target.
            (ADReady target, GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
         => target (TKS r sh) -> target (TKS r '[])
sminimum t = sindex0 t (sminIndexN t)

smaximum :: forall r sh target.
            (ADReady target, GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
         => target (TKS r sh) -> target (TKS r '[])
smaximum t = sindex0 t (smaxIndexN t)

sfromIndex0 :: forall r target. (ADReady target, GoodScalar r)
            => IntOf target -> target (TKS r '[])
sfromIndex0 = sfromIntegral . sfromPrimal

sfromIndex1 :: forall r sh target.
               (ADReady target, GoodScalar r, KnownNat (Rank sh))
            => IxSOf target sh -> target (TKS r '[Rank sh])
sfromIndex1 = case sameNat (Proxy @(Rank sh)) (Proxy @0) of
  Just Refl -> const $ sconcrete $ Nested.sfromListPrimLinear knownShS []
  _ -> sfromIntegral . sfromPrimal . sfromList
       . NonEmpty.fromList . ShapedList.indexToList

{-
sletIx :: forall r sh n target.
          (ADReady target, GoodScalar r, KnownShS sh, KnownNat n)
       => IxROf target n -> (IxROf target n -> target (TKS r sh)) -> target (TKS r sh)
sletIx ix0 f = tlet (sfromR @target @Int64 @'[n]
                     $ rint64FromIndex1 ix0) $ \ixT ->
                 f $ rint64ToIndex1 $ rfromS @target ixT
-}

scaleS :: forall target r sh.
          (KnownShS sh, ADReady target, GoodScalar r)
       => PrimalOf target (TKS r sh) -> target (TKS r sh) -> target (TKS r sh)
scaleS a d = sfromPrimal a * d

reluS, reluLeakyS
  :: forall target sh r.
     ( KnownShS sh, KnownNat (Rank sh), ADReady target, GoodScalar r
     , Differentiable r )
  => target (TKS r sh) -> target (TKS r sh)
reluS v0 = tlet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifF (x <=. sscalar 0) (sscalar 0.0) (sscalar 1.0)) v
  in oneIfGtZero * v

reluLeakyS v0 = tlet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifF (x <=. sscalar 0) (sscalar 00.01) (sscalar 01.0)) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated BaseTensor method would be
logisticS :: forall target r sh.
             ( BaseTensor target, LetTensor target
             , KnownShS sh, GoodScalar r
             , Floating (PrimalOf target (TKS r sh)) )
          => target (TKS r sh) -> target (TKS r sh)
logisticS d0 = tlet d0 $ \d ->  -- used in rprimalPart and in sdualPart
  let y0 = recip (sprimalPart @target (srepl 1) + exp (- sprimalPart d))
  in tlet (sfromPrimal y0)  -- we don't have tletPrimal
     $ \y1 -> let y = sprimalPart y1
              in sD y (sScale @target (y * (sprimalPart @target (srepl 1) - y)) $ sdualPart d)

-- TODO: verify how faster a @x * x@ version would be
-- Optimized and more clearly written @u ** 2@.
squareS :: forall target r sh.
           ( KnownShS sh, BaseTensor target, Num (PrimalOf target (TKS r sh))
           , GoodScalar r )
       => target (TKS r sh) -> target (TKS r sh)
squareS d = let u = sprimalPart d
                u' = sdualPart d
            in sD (u * u) (sScale @target (2 * u) u')

squaredDifferenceS
  :: forall target sh r.
     ( KnownShS sh, BaseTensor target, Num (PrimalOf target (TKS r sh))
     , GoodScalar r )
  => PrimalOf target (TKS r sh) -> target (TKS r sh) -> target (TKS r sh)
squaredDifferenceS targ res = squareS $ res - sfromPrimal targ

lossCrossEntropyVS :: ( KnownShS sh, KnownNat (Nested.Product sh)
                      , BaseTensor target, GoodScalar r, Differentiable r )
                   => target (TKS r sh)
                   -> target (TKS r sh)
                   -> target (TKS r '[])
lossCrossEntropyVS targ res = negate $ log res `sdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyS
  :: forall target sh r.
     ( ADReady target, ADReady (PrimalOf target)
     , GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh)
     , Differentiable r )
  => PrimalOf target (TKS r sh) -> target (TKS r sh) -> target (TKS r '[])
lossSoftMaxCrossEntropyS target d' = tlet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let softMaxU' =
        let u = sprimalPart d
            expU' = exp (u - sreplicate0N (sminimum u))
        in tlet expU' $ \expU ->
          let sumExpU = ssum0 expU
              recipSum = recip sumExpU
          in sscaleByScalar recipSum expU
               -- not exposed: LA.scaleRecip sumExpU expU
  in tlet (sfromPrimal softMaxU') $ \softMaxU ->
    sD (negate $ log (sprimalPart softMaxU) `sdot0` target)
         -- TODO: avoid: log . exp
       (sdualPart $ (softMaxU - sfromPrimal target) `sdot0` d)
         -- TODO: probably defining sDot0 would lead to a faster
         -- sDot0 (softMaxU - target) u'

-- No padding; remaining areas ignored.
maxPool1S :: forall ksize stride m target r.
             ( ADReady target, GoodScalar r
             , KnownNat ksize, KnownNat stride, KnownNat m )
          => target (TKS r '[m]) -> target (TKS r '[m])
maxPool1S v =
  let l = [0, valueOf @stride .. slength v - valueOf @ksize]
      maxOfSlice i =
        case someNatVal $ toInteger i of
          Just (SomeNat @i _proxy) ->
            gcastWith (unsafeCoerce Refl :: Compare i m :~: LT) $
            gcastWith (unsafeCoerce Refl :: Compare ksize (m - i) :~: LT) $
            smaximum $ sslice @target @r @i @(m - i - ksize) @ksize
                              Proxy Proxy v
          Nothing -> error "maxPool1S: impossible someNatVal error"
  in sfromList $ NonEmpty.fromList $ map maxOfSlice l

softMax1S :: ( KnownShS sh, KnownNat (Nested.Product sh)
             , BaseTensor target, LetTensor target
             , GoodScalar r, Differentiable r )
          => target (TKS r sh) -> target (TKS r sh)
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
  => target (TKS r '[nCoutK, nCinpK, nKh, nKw])
  -> target (TKS r '[nImgs, nCinpA, nAh, nAw])
  -> target (TKS r shB)
conv2dUnpaddedS arrK arrA =
  sbuild @target @r @(Rank shB) $ \case
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
  => target (TKS r sh) -> IxSOf target sh -> target (TKS r shOut)
slicezS d ixBase =
  gcastWith (unsafeCoerce Refl
             :: Rank (Take (Rank shOut) shOut) :~: Rank shOut) $
  gcastWith (unsafeCoerce Refl :: Drop (Rank sh) shOut :~: '[]) $
  sbuild @target @r @(Rank shOut)
  $ \ixResult ->
      indexz0S @shOut d (zipWith_Index (+)
                                       (ShapedList.shapedToIndex ixBase)
                                       (ShapedList.shapedToIndex ixResult))

{-
-- TODO: this makes tests unbearably slow
--
-- TODO: explain why the argument is not IxSOf but IxROf (is it because
-- of the spurious verification thata index fits in?)
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
  => target (TKS r sh) -> IxROf target (Rank shOut) -> target (TKS r '[])
indexz0SLet d ix0 =
  sletIx ix0 $ \ix ->
    ifF (within0S @shOut @target ix)
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
  => target (TKS r sh) -> IxROf target (Rank shOut) -> target (TKS r '[])
indexz0S d ix =
  ifF (within0S @shOut @target ix)
      (sindex0 d (ShapedList.listToIndex (indexToList ix)))
      (srepl 0)

-- | Given an index and shape, check if the index is fully within the shape.
-- Note that @ix@ is used twice, so should be shared outside.
within0S
  :: forall shOut target. (KnownShS shOut, ADReady target)
  => IxROf target (Rank shOut)
       -- the indexes may be outside shOut and even negative (e.g., for
       -- convolutions with padding)
  -> BoolOf target
within0S ix =
  let within :: IntOf target -> IntOf target -> BoolOf target
      within i dim = 0 <=. i &&* dim >. i
  in foldr (&&*) true
     $ zipWith within (indexToList ix) (map fromIntegral $ shapeT @shOut)
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
  => target (TKS r '[batch_size, channels, h, w])
  -> target (TKS r shOut)
maxPool2dUnpaddedS arr =
  let stride = valueOf @stride :: Int
  in sbuild @target @r @(Rank shOut) $ \case
    [iImg, iChan, iBh, iBw] ->
      let arrt = slicezS @shK1
                         arr [ iImg, iChan
                             , fromIntegral stride * iBh
                             , fromIntegral stride * iBw ]
      in smaximum arrt
    _ -> error "maxPool2dUnpaddedS: impossible pattern needlessly required"
