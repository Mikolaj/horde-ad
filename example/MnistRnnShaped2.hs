{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Shaped tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistRnnShaped2 where

import Prelude hiding (foldl')

import Data.Kind (Type)
import Data.List (foldl')
import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (KnownNat, Nat, fromSNat, type (*))

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Shaped.Shape

import HordeAd
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADRnnMnistParametersShaped
       (target :: Target) sizeMnistHeight width r =
  ( LayerWeigthsRNNShaped target sizeMnistHeight width r
  , LayerWeigthsRNNShaped target width width r
  , ( target (TKS '[SizeMnistLabel, width] r)
    , target (TKS '[SizeMnistLabel] r) ) )

type LayerWeigthsRNNShaped :: Target -> Nat -> Nat -> Type -> Type
type LayerWeigthsRNNShaped target in_width out_width r =
  ( target (TKS '[out_width, in_width] r)   -- input weight
  , target (TKS '[out_width, out_width] r)  -- state weight
  , target (TKS '[out_width] r) )           -- bias

zeroStateS
  :: (BaseTensor target, KnownShS sh, GoodScalar r)
  => (target (TKS sh r)  -- state
      -> a)
  -> a
zeroStateS f = f (srepl 0)

unrollLastS :: forall target state c w r n sh.
               (BaseTensor target, KnownNat n, KnownShS sh, GoodScalar r)
            => (state -> target (TKS sh r) -> w -> (c, state))
            -> (state -> target (TKS (n ': sh) r) -> w -> (c, state))
unrollLastS f s0 xs w =
  let g :: (c, state) -> target (TKS sh r) -> (c, state)
      g (_, !s) x = f s x w
  in foldl' g (undefined, s0) (sunravelToList xs)

-- | A single recurrent layer with @tanh@ activation function.
rnnMnistLayerS
  :: (ADReady target, NumScalar r, Differentiable r)
  => SNat in_width -> SNat out_width -> SNat batch_size
       -- ^ these boilerplate lines tie type parameters to the corresponding
       -- value parameters (@SNat@ below) denoting basic dimensions
  -> target (TKS '[out_width, batch_size] r)  -- state
  -> target (TKS '[in_width, batch_size] r)  -- input
  -> LayerWeigthsRNNShaped target in_width out_width r
  -> target (TKS '[out_width, batch_size] r)  -- output state
rnnMnistLayerS SNat SNat SNat
               s x (wX, wS, b) =
    let y = wX `smatmul2` x + wS `smatmul2` s
            + str (sreplicate {-@batch_size-} b)
    in tanh y

-- TODO: represent state as a pair to avoid appending; tlet now supports this.
-- | Composition of two recurrent layers.
rnnMnistTwoS
  :: (ADReady target, NumScalar r, Differentiable r)
  => SNat out_width -> SNat batch_size -> SNat sizeMnistH
  -> target (TKS '[2 * out_width, batch_size] r)  -- initial state
  -> PrimalOf target (TKS '[sizeMnistH, batch_size] r)
  -> ( LayerWeigthsRNNShaped target sizeMnistH out_width r
     , LayerWeigthsRNNShaped target out_width out_width r )
  -> ( target (TKS '[out_width, batch_size] r)
     , target (TKS '[2 * out_width, batch_size] r) )  -- final state
rnnMnistTwoS out_width@SNat
             batch_size@SNat
             sizeMnistHeightHere@SNat
             s' x ((wX, wS, b), (wX2, wS2, b2)) =
    let s3 = tlet s' $ \s ->
          let s1 = sslice (SNat @0) out_width SNat s
              s2 = sslice out_width out_width SNat s
              vec1 = rnnMnistLayerS sizeMnistHeightHere
                                    out_width
                                    batch_size
                                    s1 (sfromPrimal x) (wX, wS, b)
              vec2 = rnnMnistLayerS out_width
                                    out_width
                                    batch_size
                                    s2 vec1 (wX2, wS2, b2)
          in sappend vec1 vec2
    in (sslice out_width out_width SNat s3, s3)

-- | The two-layer recurrent nn with its state initialized to zero
-- and the result composed with a fully connected layer.
rnnMnistZeroS
  :: (ADReady target, NumScalar r, Differentiable r)
  => SNat out_width
  -> SNat batch_size
  -> SNat sizeMnistH -> SNat sizeMnistW
  -> PrimalOf target (TKS '[sizeMnistW, sizeMnistH, batch_size] r)
  -> ADRnnMnistParametersShaped target sizeMnistH out_width r
  -> target (TKS '[SizeMnistLabel, batch_size] r)
rnnMnistZeroS out_width@SNat
              batch_size@SNat
              sizeMnistHeightHere@SNat _sizeMnistWidthHere@SNat
              xs ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) =
    let rnnMnistTwo = rnnMnistTwoS out_width batch_size sizeMnistHeightHere
        (out, _s) = zeroStateS (unrollLastS rnnMnistTwo) xs
                               ((wX, wS, b), (wX2, wS2, b2))
    in w3 `smatmul2` out + str (sreplicate {-@batch_size-} b3)

-- | The neural network composed with the SoftMax-CrossEntropy loss function.
rnnMnistLossFusedS
  :: forall target h w out_width batch_size r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth, Differentiable r
     , ADReady target, ADReady (PrimalOf target), NumScalar r)
  => SNat out_width
  -> SNat batch_size
  -> ( PrimalOf target (TKS '[batch_size, h, w] r)
     , PrimalOf target (TKS '[batch_size, SizeMnistLabel] r) )
  -> ADRnnMnistParametersShaped target h out_width r
  -> target (TKScalar r)
rnnMnistLossFusedS out_width@SNat
                   batch_size@SNat
                   (glyphS, labelS) adparameters =
  let xs = stranspose @'[2, 1, 0] glyphS
      result = rnnMnistZeroS out_width
                             batch_size
                             (SNat @h) (SNat @w)
                             xs adparameters
      targets = str labelS
      loss = lossSoftMaxCrossEntropyS targets result
  in kfromPrimal (recip $ kconcrete $ fromInteger $ fromSNat batch_size) * loss

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
rnnMnistTestS
  :: forall target h w out_width batch_size r.
     ( h ~ SizeMnistHeight, w ~ SizeMnistWidth
     , target ~ Concrete, Differentiable r, NumScalar r )
  => SNat out_width
  -> SNat batch_size
  -> MnistDataBatchS batch_size r
  -> ADRnnMnistParametersShaped target h out_width r
  -> r
rnnMnistTestS out_width@SNat batch_size@SNat
              (glyphS, labelS) testParams =
  let -- input :: PrimalOf target (TKS '[sizeMnistW, sizeMnistH, batch_size] r)
      input = sconcrete
              $ Nested.stranspose (Permutation.makePerm @'[2, 1, 0]) glyphS
      outputS :: Concrete (TKS '[SizeMnistLabel, batch_size] r)
      outputS =
        let nn :: ADRnnMnistParametersShaped target h out_width r
               -> target (TKS '[SizeMnistLabel, batch_size] r)
            nn = rnnMnistZeroS out_width
                               batch_size
                               (SNat @h) (SNat @w)
                               input
        in nn testParams
      outputs = map stoVector $ sunravelToList
                $ stranspose @'[1, 0] outputS
      labels = map stoVector
               $ sunravelToList @_ @_ @(TKScalar r)
               $ sconcrete labelS
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromInteger (fromSNat batch_size)
