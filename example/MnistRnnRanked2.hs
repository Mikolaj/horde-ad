{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module MnistRnnRanked2 where

import Prelude

import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.List (foldl')
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import MnistData

type LayerWeigthsRNNShaped in_width out_width r =
  ( Shaped r '[out_width, in_width]   -- input weight
  , Shaped r '[out_width, out_width]  -- state weight
  , Shaped r '[out_width] )           -- bias

type ADRnnMnistParametersShaped width r =
  ( LayerWeigthsRNNShaped SizeMnistHeight width r
  , LayerWeigthsRNNShaped width width r
  , ( Shaped r '[SizeMnistLabel, width]
    , Shaped r '[SizeMnistLabel] ) )

type LayerWeigthsRNN r =
  ( Ranked r 2
  , Ranked r 2
  , Ranked r 1 )

-- The differentiable type of all trainable parameters of this nn.
type ADRnnMnistParameters r =
  ( LayerWeigthsRNN r
  , LayerWeigthsRNN r
  , ( Ranked r 2
    , Ranked r 1 ) )

zeroStateR
  :: (Tensor r, KnownNat n)
  => ShapeInt n -> (Ranked r n  -- state
                    -> a)
  -> a
zeroStateR sh f = f (tzero sh)

unrollLastR :: forall state c w r n.
               (Tensor r, KnownNat n,  KnownNat (1 + n))
            => (state -> Ranked r n -> w -> (c, state))
            -> (state -> Ranked r (1 + n) -> w -> (c, state))
unrollLastR f s0 xs w =
  let g :: (c, state) -> Ranked r n -> (c, state)
      g (_, s) x = f s x w
      projections :: [Ranked r n]
      projections = case tshape xs of
        len :$ _ -> map (\i -> tindex xs (fromIntegral i :. ZI)) [0 .. len - 1]
        ZS -> error "impossible pattern needlessly required"
  in foldl' g (undefined, s0) projections

rnnMnistLayerR
  :: forall r. Tensor r
  => Ranked r 2  -- in state, [out_width, batch_size]
  -> Ranked r 2  -- in, [in_width, batch_size]
  -> LayerWeigthsRNN r  -- in_width out_width
  -> Ranked r 2  -- out, [out_width, batch_size]
rnnMnistLayerR s x (wX, wS, b) = case tshape s of
  _out_width :$ batch_size :$ ZS ->
    let y = wX `tmatmul2` x + wS `tmatmul2` s
            + ttranspose [1, 0] (treplicate @r @1 batch_size b)
    in tanh y
  _ -> error "rnnMnistLayerR: wrong shape of the state"

rnnMnistTwoR
  :: Tensor r
  => Ranked r 2  -- initial state, [2 * out_width, batch_size]
  -> Ranked (Primal r) 2  -- [sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNN r  -- sizeMnistHeight out_width
     , LayerWeigthsRNN r )  -- out_width out_width
  -> ( Ranked r 2  -- [out_width, batch_size]
     , Ranked r 2 )  -- final state, [2 * out_width, batch_size]
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
  :: (Tensor r, Tensor (Primal r))
  => Int
  -> Ranked (Primal r) 3  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters r  -- sizeMnistHeight out_width
  -> Ranked r 2  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case tshape b of
  out_width :$ ZS ->
    let sh = 2 * out_width :$ batch_size :$ ZS
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `tmatmul2` out + ttranspose [1, 0] (treplicate batch_size b3)
  _ -> error "rnnMnistZeroR: wrong shape"

rnnMnistLossFusedR
  :: (Tensor r, Tensor (Primal r))
  => Int
  -> (Ranked (Primal r) 3, Ranked (Primal r) 2)  -- batch_size
  -> ADRnnMnistParameters r  -- SizeMnistHeight out_width
  -> Ranked r 0
rnnMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let xs = ttranspose [2, 1, 0] glyphR
      result = rnnMnistZeroR batch_size xs adparameters
      targets = ttranspose [1, 0] labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in tconstant (recip $ fromIntegral batch_size) * loss

rnnMnistTestR
  :: forall r.
     ( ADReady r, RealFloat r, r ~ Primal r, Numeric r
     , Ranked r ~ Flip OR.Array r )
  => Int
  -> MnistDataBatchR r  -- batch_size
  -> ((ADRnnMnistParameters r  -- SizeMnistHeight out_width
       -> Ranked r 2)  -- [SizeMnistLabel, batch_size]
      -> OR.Array 2 r)  -- [SizeMnistLabel, batch_size]
  -> r
{-# INLINE rnnMnistTestR #-}
rnnMnistTestR 0 _ _ = 0
rnnMnistTestR batch_size (glyphR, labelR) evalAtTestParams =
  let xs = Flip $ OR.transpose [2, 1, 0] glyphR
      outputR =
        let nn :: ADRnnMnistParameters r  -- SizeMnistHeight out_width
               -> Ranked r 2  -- [SizeMnistLabel, batch_size]
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
