{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistRnnRanked2 where

import Prelude

import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.List (foldl')
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Domains
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

type LayerWeigthsRNN r =  -- in_width out_width
  ( Ranked r 2  -- input weight, [out_width, in_width]
  , Ranked r 2  -- state weight, [out_width, out_width]
  , Ranked r 1 )  -- bias, [out_width]

-- The differentiable type of all trainable parameters of this nn.
type ADRnnMnistParameters r =  -- sizeMnistHeight out_width
  ( LayerWeigthsRNN r  -- sizeMnistHeight out_width
  , LayerWeigthsRNN r  -- out_width out_width
  , ( Ranked r 2  -- [SizeMnistLabel, out_width]
    , Ranked r 1 ) )  -- [SizeMnistLabel]

zeroStateR
  :: (Tensor r, KnownNat n)
  => ShapeInt n -> (Ranked r n  -- state
                    -> a)
  -> a
zeroStateR sh f = f (tzero sh)

unrollLastR :: forall state c w r n. Numeric r
            => (state -> OR.Array n r -> w -> (c, state))
            -> (state -> OR.Array (1 + n) r -> w -> (c, state))
unrollLastR f s0 xs w =
  let g :: (c, state) -> OR.Array n r -> (c, state)
      g (_, s) x = f s x w
  in foldl' g (undefined, s0) $ ORB.toList $ OR.unravel xs

rnnMnistLayerR
  :: forall r. Tensor r
  => Ranked r 2  -- in state, [out_width, batch_size]
  -> Ranked r 2  -- in, [in_width, batch_size] r)  -- in
  -> LayerWeigthsRNN r  -- in_width out_width
  -> ( Ranked r 2  -- out, [out_width, batch_size]
     , Ranked r 2 )  -- out state, [out_width, batch_size]
rnnMnistLayerR s x (wX, wS, b) = case tshape s of
  _out_width :$  batch_size :$ ZS ->
    let y = wX `tmatmul2` x + wS `tmatmul2` s
            + ttranspose [1, 0] (tkonst @r @1 batch_size b)
        yTanh = tanh y
    in (yTanh, yTanh)
  _ -> error "rnnMnistLayerR: wrong shape of the state"

rnnMnistTwoR
  :: Tensor r
  => Ranked r 2  -- initial state, [2 * out_width, batch_size]
  -> OR.Array 2 (Value r)  -- [sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNN r  -- sizeMnistHeight out_width
     , LayerWeigthsRNN r )  -- out_width out_width
  -> ( Ranked r 2  -- [out_width, batch_size]
     , Ranked r 2 )  -- final state, [2 * out_width, batch_size]
rnnMnistTwoR s x ((wX, wS, b), (wX2, wS2, b2)) = case tshape s of
  out_width_x_2 :$ _batch_size :$ ZS ->
    let out_width = out_width_x_2 `div` 2
        s1 = tslice 0 out_width s
        s2 = tslice out_width out_width s
        (vec1, s1') = rnnMnistLayerR s1 (tconst x) (wX, wS, b)
        (vec2, s2') = rnnMnistLayerR s2 vec1 (wX2, wS2, b2)
        s3 = tappend s1' s2'
    in (vec2, s3)
  _ -> error "rnnMnistTwoR: wrong shape of the state"

rnnMnistZeroR
  :: (Tensor r, Numeric (Value r))
  => Int
  -> OR.Array 3 (Value r)  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters r  -- sizeMnistHeight out_width
  -> Ranked r 2  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case tshape b of
  out_width :$ ZS ->
    let sh = 2 * out_width :$ batch_size :$ ZS
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `tmatmul2` out + ttranspose [1, 0] (tkonst batch_size b3)
  _ -> error "rnnMnistZeroR: wrong shape"

arnnMnistLossFusedR
  :: ( Tensor r, Tensor (Primal r)
     , Ranked (Primal r) 2 ~ OR.Array 2 (Value r), Numeric (Value r) )
  => Int -> MnistDataBatchR (Value r)  -- batch_size
  -> ADRnnMnistParameters r  -- SizeMnistHeight out_width
  -> r
arnnMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let xs = OR.transpose [2, 1, 0] glyphR
      result = rnnMnistZeroR batch_size xs adparameters
      targets2 = OR.transpose [1, 0] labelR
      loss = lossSoftMaxCrossEntropyR targets2 result
  in tscale0 (recip $ fromIntegral batch_size)
             loss

arnnMnistTestR
  :: forall r. (ADReady r, r ~ Value r)
  => Int -> MnistDataBatchR r  -- batch_size
  -> ((ADRnnMnistParameters r  -- SizeMnistHeight out_width
       -> Ranked r 2)  -- [SizeMnistLabel, batch_size]
      -> OR.Array 2 r)  -- [SizeMnistLabel, batch_size]
  -> r
arnnMnistTestR batch_size (glyphS, labelS) evalAtTestParams =
  let xs = OR.transpose [2, 1, 0] glyphS
      outputR =
        let nn :: ADRnnMnistParameters r  -- SizeMnistHeight out_width
               -> Ranked r 2  -- [SizeMnistLabel, batch_size]
            nn = rnnMnistZeroR batch_size xs
        in evalAtTestParams nn
      outputs = map OR.toVector $ ORB.toList $ OR.unravel
                $ OR.transpose [1, 0] outputR
      labels = map OR.toVector $ ORB.toList $ OR.unravel labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
