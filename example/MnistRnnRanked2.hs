{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistRnnRanked2 where

import Prelude

import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.List (foldl')
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Vector)

import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

type LayerWeigthsRNNShaped shaped in_width out_width r =
  ( shaped r '[out_width, in_width]   -- input weight
  , shaped r '[out_width, out_width]  -- state weight
  , shaped r '[out_width] )           -- bias

type ADRnnMnistParametersShaped shaped width r =
  ( LayerWeigthsRNNShaped shaped SizeMnistHeight width r
  , LayerWeigthsRNNShaped shaped width width r
  , ( shaped r '[SizeMnistLabel, width]
    , shaped r '[SizeMnistLabel] ) )

type LayerWeigthsRNN ranked r =
  ( ranked r 2
  , ranked r 2
  , ranked r 1 )

-- The differentiable type of all trainable parameters of this nn.
type ADRnnMnistParameters ranked r =
  ( LayerWeigthsRNN ranked r
  , LayerWeigthsRNN ranked r
  , ( ranked r 2
    , ranked r 1 ) )

zeroStateR
  :: (Tensor ranked, GoodScalar r, KnownNat n)
  => ShapeInt n -> (ranked r n  -- state
                    -> a)
  -> a
zeroStateR sh f = f (tzero sh)

unrollLastR :: forall ranked state c w r n.
               (Tensor ranked, GoodScalar r, KnownNat n, KnownNat (1 + n))
            => (state -> ranked r n -> w -> (c, state))
            -> (state -> ranked r (1 + n) -> w -> (c, state))
unrollLastR f s0 xs w =
  let g :: (c, state) -> ranked r n -> (c, state)
      g (_, s) x = f s x w
      projections :: [ranked r n]
      projections = case tshape xs of
        len :$ _ -> map (\i -> tindex xs (fromIntegral i :. ZI)) [0 .. len - 1]
        ZS -> error "impossible pattern needlessly required"
  in foldl' g (undefined, s0) projections

rnnMnistLayerR
  :: ADReady ranked r
  => ranked r 2  -- in state, [out_width, batch_size]
  -> ranked r 2  -- in, [in_width, batch_size]
  -> LayerWeigthsRNN ranked r  -- in_width out_width
  -> ranked r 2  -- out, [out_width, batch_size]
rnnMnistLayerR s x (wX, wS, b) = case tshape s of
  _out_width :$ batch_size :$ ZS ->
    let y = wX `tmatmul2` x + wS `tmatmul2` s
            + ttr (treplicate batch_size b)
    in tanh y
  _ -> error "rnnMnistLayerR: wrong shape of the state"

rnnMnistTwoR
  :: ADReady ranked r
  => ranked r 2  -- initial state, [2 * out_width, batch_size]
  -> PrimalOf ranked r 2  -- [sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNN ranked r  -- sizeMnistHeight out_width
     , LayerWeigthsRNN ranked r )  -- out_width out_width
  -> ( ranked r 2  -- [out_width, batch_size]
     , ranked r 2 )  -- final state, [2 * out_width, batch_size]
rnnMnistTwoR s' x ((wX, wS, b), (wX2, wS2, b2)) = case tshape s' of
  out_width_x_2 :$ _batch_size :$ ZS ->
    let out_width = out_width_x_2 `div` 2
        s3 = tlet s' $ \s ->
          let s1 = tslice 0 out_width s
              s2 = tslice out_width out_width s
              vec1 = rnnMnistLayerR s1 (tconstant x) (wX, wS, b)
              vec2 = rnnMnistLayerR s2 vec1 (wX2, wS2, b2)
          in tappend vec1 vec2
    in (tslice out_width out_width s3, s3)
  _ -> error "rnnMnistTwoR: wrong shape of the state"

rnnMnistZeroR
  :: ADReady ranked r
  => Int
  -> PrimalOf ranked r 3  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters ranked r  -- sizeMnistHeight out_width
  -> ranked r 2  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case tshape b of
  out_width :$ ZS ->
    let sh = 2 * out_width :$ batch_size :$ ZS
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `tmatmul2` out + ttr (treplicate batch_size b3)
  _ -> error "rnnMnistZeroR: wrong shape"

rnnMnistLossFusedR
  :: ADReady ranked r
  => Int
  -> (PrimalOf ranked r 3, PrimalOf ranked r 2)  -- batch_size
  -> ADRnnMnistParameters ranked r  -- SizeMnistHeight out_width
  -> ranked r 0
rnnMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let xs = ttranspose [2, 1, 0] glyphR
      result = rnnMnistZeroR batch_size xs adparameters
      targets = ttr labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in tconstant (recip $ fromIntegral batch_size) * loss

rnnMnistTestR
  :: forall ranked r. (ranked ~ Flip OR.Array, ADReady ranked r)
  => Int
  -> MnistDataBatchR r  -- batch_size
  -> ((ADRnnMnistParameters ranked r  -- SizeMnistHeight out_width
       -> ranked r 2)  -- [SizeMnistLabel, batch_size]
      -> OR.Array 2 r)  -- [SizeMnistLabel, batch_size]
  -> r
{-# INLINE rnnMnistTestR #-}
rnnMnistTestR 0 _ _ = 0
rnnMnistTestR batch_size (glyphR, labelR) evalAtTestParams =
  let xs = Flip $ OR.transpose [2, 1, 0] glyphR
      outputR =
        let nn :: ADRnnMnistParameters ranked r
                    -- SizeMnistHeight out_width
               -> ranked r 2  -- [SizeMnistLabel, batch_size]
            nn = rnnMnistZeroR batch_size xs
        in evalAtTestParams nn
      outputs = map OR.toVector $ ORB.toList $ OR.unravel
                $ OR.transpose [1, 0] outputR
      labels = map OR.toVector $ ORB.toList $ OR.unravel labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
