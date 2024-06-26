{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistRnnRanked2 where

import Prelude hiding (foldl')

import Data.Kind (Type)
import Data.List (foldl')
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, type (+))
import Numeric.LinearAlgebra (Vector)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.Internal.BackendOX (ORArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))
import HordeAd.Util.SizedList
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADRnnMnistParametersShaped (shaped :: ShapedTensorType) width r =
  ( LayerWeigthsRNNShaped shaped SizeMnistHeight width r
  , LayerWeigthsRNNShaped shaped width width r
  , ( shaped r '[SizeMnistLabel, width]
    , shaped r '[SizeMnistLabel] ) )

type LayerWeigthsRNNShaped :: ShapedTensorType -> Nat -> Nat -> Type -> Type
type LayerWeigthsRNNShaped shaped in_width out_width r =
  ( shaped r '[out_width, in_width]   -- input weight
  , shaped r '[out_width, out_width]  -- state weight
  , shaped r '[out_width] )           -- bias

-- | The differentiable type of all trainable parameters of this nn.
type ADRnnMnistParameters ranked r =
  ( LayerWeigthsRNN ranked r
  , LayerWeigthsRNN ranked r
  , ( ranked r 2
    , ranked r 1 ) )

type LayerWeigthsRNN (ranked :: RankedTensorType) r =
  ( ranked r 2
  , ranked r 2
  , ranked r 1 )

zeroStateR
  :: (RankedTensor ranked, GoodScalar r, KnownNat n)
  => IShR n -> (ranked r n  -- state
                    -> a)
  -> a
zeroStateR sh f = f (rzero sh)

unrollLastR :: forall ranked state c w r n.
               (RankedTensor ranked, GoodScalar r, KnownNat n, KnownNat (1 + n))
            => (state -> ranked r n -> w -> (c, state))
            -> (state -> ranked r (1 + n) -> w -> (c, state))
unrollLastR f s0 xs w =
  let g :: (c, state) -> ranked r n -> (c, state)
      g (_, !s) x = f s x w
      projections :: [ranked r n]
      projections = case rshape xs of
        len :$: _ -> map (\i -> rindex xs (fromIntegral i :.: ZIR)) [0 .. len - 1]
        ZSR -> error "impossible pattern needlessly required"
  in foldl' g (undefined, s0) projections

rnnMnistLayerR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => ranked r 2  -- in state, [out_width, batch_size]
  -> ranked r 2  -- input, [in_width, batch_size]
  -> LayerWeigthsRNN ranked r  -- in_width out_width
  -> ranked r 2  -- output state, [out_width, batch_size]
rnnMnistLayerR s x (wX, wS, b) = case rshape s of
  _out_width :$: batch_size :$: ZSR ->
    let y = wX `rmatmul2` x + wS `rmatmul2` s
            + rtr (rreplicate batch_size b)
    in tanh y
  _ -> error "rnnMnistLayerR: wrong shape of the state"

rnnMnistTwoR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => ranked r 2  -- initial state, [2 * out_width, batch_size]
  -> PrimalOf ranked r 2  -- [sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNN ranked r  -- sizeMnistHeight out_width
     , LayerWeigthsRNN ranked r )  -- out_width out_width
  -> ( ranked r 2  -- [out_width, batch_size]
     , ranked r 2 )  -- final state, [2 * out_width, batch_size]
rnnMnistTwoR s' x ((wX, wS, b), (wX2, wS2, b2)) = case rshape s' of
  out_width_x_2 :$: _batch_size :$: ZSR ->
    let out_width = out_width_x_2 `div` 2
        s3 = rlet s' $ \s ->
          let s1 = rslice 0 out_width s
              s2 = rslice out_width out_width s
              vec1 = rnnMnistLayerR s1 (rconstant x) (wX, wS, b)
              vec2 = rnnMnistLayerR s2 vec1 (wX2, wS2, b2)
          in rappend vec1 vec2
    in (rslice out_width out_width s3, s3)
  _ -> error "rnnMnistTwoR: wrong shape of the state"

rnnMnistZeroR
  :: (ADReady ranked, GoodScalar r, Differentiable r)
  => Int
  -> PrimalOf ranked r 3  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters ranked r  -- sizeMnistHeight out_width
  -> ranked r 2  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case rshape b of
  out_width :$: ZSR ->
    let sh = 2 * out_width :$: batch_size :$: ZSR
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `rmatmul2` out + rtr (rreplicate batch_size b3)
  _ -> error "rnnMnistZeroR: wrong shape"

rnnMnistLossFusedR
  :: (ADReady ranked, ADReady (PrimalOf ranked), GoodScalar r, Differentiable r)
  => Int
  -> (PrimalOf ranked r 3, PrimalOf ranked r 2)  -- batch_size
  -> ADRnnMnistParameters ranked r  -- SizeMnistHeight out_width
  -> ranked r 0
rnnMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let xs = rtranspose [2, 1, 0] glyphR
      result = rnnMnistZeroR batch_size xs adparameters
      targets = rtr labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in rconstant (recip $ fromIntegral batch_size) * loss

rnnMnistTestR
  :: forall ranked r.
     (ranked ~ ORArray, GoodScalar r, Differentiable r)
  => ADRnnMnistParameters ranked r
  -> Int
  -> MnistDataBatchR r  -- batch_size
  -> HVector ORArray
  -> r
rnnMnistTestR _ 0 _ _ = 0
rnnMnistTestR valsInit batch_size (glyphR, labelR) testParams =
  let input :: ranked r 3
      input = rconst $ Nested.rtranspose [2, 1, 0] $ Nested.rfromOrthotope SNat glyphR
      outputR :: FlipR Nested.Ranked r 2
      outputR =
        let nn :: ADRnnMnistParameters ranked r
                    -- SizeMnistHeight out_width
               -> ranked r 2  -- [SizeMnistLabel, batch_size]
            nn = rnnMnistZeroR batch_size input
        in nn $ parseHVector valsInit testParams
      outputs = map (Nested.rtoVector . runFlipR) $ runravelToList
                $ rtranspose [1, 0] outputR
      labels = map (Nested.rtoVector . runFlipR) $ runravelToList
               $ FlipR $ Nested.rfromOrthotope SNat labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
