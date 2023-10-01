{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Commonly used operations on tensors. Too large, too ad hoc or too unlikely
-- to have specialized implementations to be included in the 'ShapedTensor'
-- class. Some of the operations may also depend on more than 'ShapedTensor',
-- e.g., also on the 'ConvertTensor' class.
module HordeAd.External.CommonShapedOps
  ( module HordeAd.External.CommonShapedOps
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.Int (Int64)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import           GHC.TypeLits
  (Div, KnownNat, SomeNat (..), someNatVal, type (-), type (<=))
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.External.CommonRankedOps
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

sminIndexN :: ( ADReadyS shaped, GoodScalar r
              , OS.Shape sh, KnownNat (OS.Size sh) )
           => shaped r sh -> IndexSh shaped sh
sminIndexN t =
  ShapedList.fromLinearIdx
    (sshape t)
    (ShapedList.shapedNat $ tfromS $ sprimalPart $ sminIndex (sflatten t))

smaxIndexN :: ( ADReadyS shaped, GoodScalar r
              , OS.Shape sh, KnownNat (OS.Size sh) )
           => shaped r sh -> IndexSh shaped sh
smaxIndexN t =
  ShapedList.fromLinearIdx
    (sshape t)
    (ShapedList.shapedNat $ tfromS $ sprimalPart $ smaxIndex (sflatten t))

sminimum :: forall r sh shaped.
            (ADReadyS shaped, GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
         => shaped r sh -> shaped r '[]
sminimum t = sindex0 t (sminIndexN t)

smaximum :: forall r sh shaped.
            (ADReadyS shaped, GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
         => shaped r sh -> shaped r '[]
smaximum t = sindex0 t (smaxIndexN t)

sfromIndex0 :: forall n r shaped. (ADReadyS shaped, GoodScalar r)
            => IntSh shaped n -> shaped r '[]
sfromIndex0 = sfromIntegral . sconstant . sfromR . ShapedList.unShapedNat

sfromIndex1 :: forall r sh shaped.
               (ADReadyS shaped, GoodScalar r, KnownNat (OS.Rank sh))
            => IndexSh shaped sh -> shaped r '[OS.Rank sh]
sfromIndex1 =
  sfromIntegral . sconstant . sfromR . rfromList . ShapedList.sizedListToList

sletIx :: forall r sh n shaped.
          (ADReadyS shaped, GoodScalar r, OS.Shape sh, KnownNat n)
       => IndexOf shaped n -> (IndexOf shaped n -> shaped r sh) -> shaped r sh
sletIx ix0 f = slet (sfromR @(RankedOf shaped) @shaped @Int64 @'[n]
                     $ rint64FromIndex1 ix0) $ \ixT ->
                 f $ rint64ToIndex1 $ tfromS ixT

scaleS :: forall shaped r sh.
          (OS.Shape sh, ADReadyS shaped, GoodScalar r)
       => PrimalOf shaped r sh -> shaped r sh -> shaped r sh
scaleS a d = sconstant a * d

reluS, reluLeakyS
  :: forall shaped sh r.
     ( OS.Shape sh, KnownNat (OS.Rank sh), ADReadyS shaped, GoodScalar r
     , Differentiable r )
  => shaped r sh -> shaped r sh
reluS v0 = slet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifF (x <=. 0) 0.0 1.0) v
  in oneIfGtZero * v

reluLeakyS v0 = slet v0 $ \v ->
  let oneIfGtZero = smap0N (\x -> ifF (x <=. 0) 0.01 1.0) v
  in oneIfGtZero * v

-- TODO: verify how faster a dedicated ShapedTensor method would be
logisticS :: forall shaped r sh.
             ( OS.Shape sh, ShapedTensor shaped, GoodScalar r
             , Floating (PrimalOf shaped r sh) )
          => shaped r sh -> shaped r sh
logisticS d0 = slet d0 $ \d ->  -- used in rprimalPart and in sdualPart
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
                      , ShapedTensor shaped, GoodScalar r, Differentiable r )
                   => shaped r sh
                   -> shaped r sh
                   -> shaped r '[]
lossCrossEntropyVS targ res = negate $ log res `sdot0` targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are one-hot.
lossSoftMaxCrossEntropyS
  :: forall shaped sh r.
     ( ADReadyS shaped, GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh)
     , Differentiable r )
  => PrimalOf shaped r sh -> shaped r sh -> shaped r '[]
lossSoftMaxCrossEntropyS target d' = slet d' $ \d ->
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by QuickCheck tests to avoid NaNs, etc., for argument
  -- values we don't fully control.
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
             ( ADReadyS shaped, GoodScalar r
             , KnownNat ksize, KnownNat stride, KnownNat m )
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
             , ShapedTensor shaped, GoodScalar r, Differentiable r )
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
  :: forall nCoutK nCinpK nKh nKw nImgs nCinpA nAh nAw
            (shaped :: ShapedTensorKind) r shB shK1.
     ( KnownNat nCoutK, KnownNat nCinpK, KnownNat nKh, KnownNat nKw
     , KnownNat nImgs, KnownNat nAh, KnownNat nAw
     , ADReadyS shaped, GoodScalar r
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
     , OS.Rank shOut ~ OS.Rank sh, ADReadyS shaped, GoodScalar r )
  => shaped r sh -> IndexSh shaped sh -> shaped r shOut
slicezS d ixBase =
  gcastWith (unsafeCoerce Refl
             :: OS.Rank (OS.Take (OS.Rank shOut) shOut) :~: OS.Rank shOut) $
  gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) shOut :~: '[]) $
  sbuild @shaped @r @(OS.Rank shOut)
  $ \ixResult ->
      indexz0S @shOut d (zipWith_Index (+)
                                       (ShapedList.shapedListToIndex ixBase)
                                       (ShapedList.shapedListToIndex ixResult))

-- TODO: this makes tests unbearably slow
--
-- TODO: explain why the argument is not IndexSh but IndexOf (is it because
-- of the spurious verification thata index fits in?)
--
-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- The @ShapedList.listToSized@ in the implementation here should not verify
-- that the index fits inside the type-level shape, because vectorization
-- may make it not fit and that's fine. In the worst case, indexing ignores
-- such invalid indexes and returns 0.
indexz0SLet
  :: forall shOut sh shaped r.
     ( OS.Shape shOut, KnownNat (OS.Rank shOut), OS.Shape sh
     , ADReadyS shaped, GoodScalar r )
  => shaped r sh -> IndexOf shaped (OS.Rank shOut) -> shaped r '[]
indexz0SLet d ix0 =
  sletIx ix0 $ \ix ->
    ifF (within0S @shOut @shaped ix)
        (sindex0 d (ShapedList.listToSized (indexToList ix)))
        0

-- | Retrieve the element at the given index,
--   returning zero for out of range indices.
--
-- Warning: this uses ix twice and within0 again uses it twice,
-- so this variant without rlet should be used only when it's known
-- that ix is of small constant size (e.g., if it contains conditionals
-- that compare big tensors or their minimal elements, it likely is not,
-- unless the tensors are under rlet and only variables representing them
-- are used).
indexz0S
  :: forall shOut sh shaped r.
     (OS.Shape shOut, OS.Shape sh, ADReadyS shaped, GoodScalar r)
  => shaped r sh -> IndexOf shaped (OS.Rank shOut) -> shaped r '[]
indexz0S d ix =
  ifF (within0S @shOut @shaped ix)
      (sindex0 d (ShapedList.listToSized (indexToList ix)))
      0

-- | Given an index and shape, check if the index is fully within the shape.
-- Note that @ix@ is used twice, so should be shared outside.
within0S
  :: forall shOut shaped. (OS.Shape shOut, ADReadyS shaped)
  => IndexOf shaped (OS.Rank shOut)
       -- the indexes may be outside shOut and even negative (e.g., for
       -- convolutions with padding)
  -> BoolOf shaped
within0S ix =
  let within :: IntOf shaped -> IntOf shaped -> BoolOf shaped
      within i dim = 0 <=. i &&* dim >. i
  in foldr (&&*) true
     $ zipWith within (indexToList ix) (map fromIntegral $ OS.shapeT @shOut)
       -- or use sfromIndex1 and compare vectors?

maxPool2dUnpaddedS
  :: forall ksize stride batch_size channels h w shaped r shOut shK1.
     ( KnownNat ksize, KnownNat stride, KnownNat batch_size, KnownNat channels
     , KnownNat h, KnownNat w
     , 1 <= stride  -- wrongly reported as redundant due to plugins
     , ADReadyS shaped, GoodScalar r
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
