{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Scalar-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.MnistToolsScalar where

import Prelude

import           Control.Exception (assert)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.DualDelta
import HordeAd.Engine
import HordeAd.MnistToolsData
import HordeAd.PairOfVectors (VecDualDelta, var)

-- | Compute the output of a neuron, without applying activation function,
-- from trainable inputs in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons in the middle
-- of the network, receiving inputs from other neurons.
--
-- Note that functions like that, with Delta in the type signature
-- (which is really indispensable due to accessing variable parameters
-- in a special way) make it impossible to implement the function
-- to be differentiated as fully polymorphic @:: Num r => [r] -> m r@
-- function and so have no overhead when computing the value
-- with a dummy monad. Another case is selectively fused operations,
-- unless we include all of them, even very ad hoc ones,
-- in a class with implementations both on @D@ and on plain @r@.
sumTrainableInputs :: forall m r. (DeltaMonad r m, Numeric r)
                   => Data.Vector.Vector (DualDelta r)
                   -> Int
                   -> VecDualDelta r
                   -> m (DualDelta r)
sumTrainableInputs xs offset vec = do
  let bias = var vec offset
      f :: DualDelta r -> Int -> DualDelta r -> DualDelta r
      f !acc i u =
        let v = var vec (offset + 1 + i)
        in acc + u * v
  returnLet $ V.ifoldl' f bias xs

-- | Compute the output of a neuron, without applying activation function,
-- from constant data in @xs@ and parameters (the bias and weights)
-- at @vec@ starting at @offset@. Useful for neurons at the bottom
-- of the network, tasked with ingesting the data.
sumConstantData :: forall m r. (DeltaMonad r m, Numeric r)
                => Vector r
                -> Int
                -> VecDualDelta r
                -> m (DualDelta r)
sumConstantData xs offset vec = do
  let bias = var vec offset
      f :: DualDelta r -> Int -> r -> DualDelta r
      f !acc i r =
        let v = var vec (offset + 1 + i)
        in acc + scale r v
  returnLet $ V.ifoldl' f bias xs

hiddenLayerMnist :: forall m r. (DeltaMonad r m, Numeric r)
                 => (DualDelta r -> m (DualDelta r))
                 -> Vector r
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
hiddenLayerMnist factivation x vec width = do
  let nWeightsAndBias = V.length x + 1
      f :: Int -> m (DualDelta r)
      f i = do
        outSum <- sumConstantData x (i * nWeightsAndBias) vec
        factivation outSum
  V.generateM width f

middleLayerMnist :: forall m r. (DeltaMonad r m, Numeric r)
                 => (DualDelta r -> m (DualDelta r))
                 -> Data.Vector.Vector (DualDelta r)
                 -> Int
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
middleLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualDelta r)
      f i = do
        outSum <- sumTrainableInputs hiddenVec
                                     (offset + i * nWeightsAndBias)
                                     vec
        factivation outSum
  V.generateM width f

outputLayerMnist :: forall m r. (DeltaMonad r m, Numeric r)
                 => (Data.Vector.Vector (DualDelta r)
                     -> m (Data.Vector.Vector (DualDelta r)))
                 -> Data.Vector.Vector (DualDelta r)
                 -> Int
                 -> VecDualDelta r
                 -> Int
                 -> m (Data.Vector.Vector (DualDelta r))
outputLayerMnist factivation hiddenVec offset vec width = do
  let nWeightsAndBias = V.length hiddenVec + 1
      f :: Int -> m (DualDelta r)
      f i = sumTrainableInputs hiddenVec (offset + i * nWeightsAndBias) vec
  vOfSums <- V.generateM width f
  factivation vOfSums

generalTestMnist :: forall r. (Ord r, Fractional r, Numeric r)
                 => (Domain r
                     -> VecDualDelta r
                     -> DeltaMonadValue r
                          (Data.Vector.Vector (DualDelta r)))
                 -> [MnistData r] -> Domain r
                 -> r
{-# INLINE generalTestMnist #-}
generalTestMnist nn xs res =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let value = V.map (\(D r _) -> r)
                    $ valueDual (nn glyph) (res, V.empty, V.empty)
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

lenMnist2 :: Int -> Int -> Int
lenMnist2 widthHidden widthHidden2 =
  widthHidden * (sizeMnistGlyph + 1)
  + widthHidden2 * (widthHidden + 1)
  + sizeMnistLabel * (widthHidden2 + 1)

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2 :: (DeltaMonad r m, Numeric r)
         => (DualDelta r -> m (DualDelta r))
         -> (Data.Vector.Vector (DualDelta r)
             -> m (Data.Vector.Vector (DualDelta r)))
         -> Int
         -> Int
         -> Vector r
         -> VecDualDelta r
         -> m (Data.Vector.Vector (DualDelta r))
nnMnist2 factivationHidden factivationOutput widthHidden widthHidden2
         x vec = do
  let !_A = assert (sizeMnistGlyph == V.length x) ()
  hiddenVec <- inline hiddenLayerMnist factivationHidden x vec widthHidden
  let offsetMiddle = widthHidden * (sizeMnistGlyph + 1)
  middleVec <- inline middleLayerMnist factivationHidden hiddenVec
                                       offsetMiddle vec widthHidden2
  let offsetOutput = offsetMiddle + widthHidden2 * (widthHidden + 1)
  inline outputLayerMnist factivationOutput middleVec
                          offsetOutput vec sizeMnistLabel

nnMnistLoss2 :: (DeltaMonad r m, Floating r, Numeric r)
             => Int
             -> Int
             -> MnistData r
             -> VecDualDelta r
             -> m (DualDelta r)
nnMnistLoss2 widthHidden widthHidden2 (x, targ) vec = do
  res <- inline nnMnist2 logisticAct softMaxAct widthHidden widthHidden2 x vec
  lossCrossEntropy targ res

testMnist2 :: (Ord r, Floating r, Numeric r)
           => Int -> Int -> [MnistData r] -> Domain r -> r
testMnist2 widthHidden widthHidden2 =
  generalTestMnist (inline nnMnist2 logisticAct softMaxAct
                                    widthHidden widthHidden2)
