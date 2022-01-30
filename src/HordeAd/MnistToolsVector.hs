{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Vector-based (meaning that dual numbers for gradient computation
-- consider vectors, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers.
module HordeAd.MnistToolsVector where

import Prelude

import           Control.Exception (assert)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.DualDelta
import HordeAd.Engine
import HordeAd.MnistToolsData
import HordeAd.PairOfVectors (VecDualDelta, varV)

sumTrainableInputsV :: Numeric r
                    => DualDelta (Data.Vector.Storable.Vector r)
                    -> Int
                    -> VecDualDelta r
                    -> DualDelta r
sumTrainableInputsV x offset vec =
  let v = varV vec offset
  in v <.>! x

sumTrainableInputsL :: forall r. Numeric r
                    => DualDelta (Data.Vector.Storable.Vector r)
                    -> Int
                    -> VecDualDelta r
                    -> Int
                    -> DualDelta (Data.Vector.Storable.Vector r)
sumTrainableInputsL x offset vec width =
  let f :: Int -> DualDelta r
      f i = sumTrainableInputsV x (offset + i) vec
  in deltaSeq $ V.generate width f

sumConstantDataV :: Numeric r
                 => Data.Vector.Storable.Vector r
                 -> Int
                 -> VecDualDelta r
                 -> DualDelta r
sumConstantDataV x offset vec =
  let v = varV vec offset
  in v <.>!! x

sumConstantDataL :: forall r. Numeric r
                 => Data.Vector.Storable.Vector r
                 -> Int
                 -> VecDualDelta r
                 -> Int
                 -> DualDelta (Data.Vector.Storable.Vector r)
sumConstantDataL x offset vec width =
  let f :: Int -> DualDelta r
      f i = sumConstantDataV x (offset + i) vec
  in deltaSeq $ V.generate width f

hiddenLayerMnistV :: forall m r.
                       (Numeric r, Num (Data.Vector.Storable.Vector r))
                  => (DualDelta (Data.Vector.Storable.Vector r)
                      -> m (DualDelta (Data.Vector.Storable.Vector r)))
                  -> Data.Vector.Storable.Vector r
                  -> VecDualDelta r
                  -> Int
                  -> m (DualDelta (Data.Vector.Storable.Vector r))
hiddenLayerMnistV factivation x vec width = do
  let multiplied = sumConstantDataL x 0 vec width
      biased = multiplied + varV vec width
  factivation biased

middleLayerMnistV :: forall m r.
                       (Numeric r, Num (Data.Vector.Storable.Vector r))
                  => (DualDelta (Data.Vector.Storable.Vector r)
                      -> m (DualDelta (Data.Vector.Storable.Vector r)))
                  -> DualDelta (Data.Vector.Storable.Vector r)
                  -> Int
                  -> VecDualDelta r
                  -> Int
                  -> m (DualDelta (Data.Vector.Storable.Vector r))
middleLayerMnistV factivation hiddenVec offset vec width = do
  let multiplied = sumTrainableInputsL hiddenVec offset vec width
      biased = multiplied + varV vec (offset + width)
  factivation biased

lenMnist2V :: Int -> Int -> Int
lenMnist2V _widthHidden _widthHidden2 = 0

lenVectorsMnist2V :: Int -> Int -> Data.Vector.Vector Int
lenVectorsMnist2V widthHidden widthHidden2 =
  V.fromList $ replicate widthHidden sizeMnistGlyph ++ [widthHidden]
               ++ replicate widthHidden2 widthHidden ++ [widthHidden2]
               ++ replicate sizeMnistLabel widthHidden2 ++ [sizeMnistLabel]

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2V :: (DeltaMonad r m, Numeric r, Num (Data.Vector.Storable.Vector r))
          => (DualDelta (Data.Vector.Storable.Vector r)
              -> m (DualDelta (Data.Vector.Storable.Vector r)))
          -> (DualDelta (Data.Vector.Storable.Vector r)
              -> m (DualDelta (Data.Vector.Storable.Vector r)))
          -> Int
          -> Int
          -> Data.Vector.Storable.Vector r
          -> VecDualDelta r
          -> m (DualDelta (Data.Vector.Storable.Vector r))
nnMnist2V factivationHidden factivationOutput widthHidden widthHidden2
          x vec = do
  let !_A = assert (sizeMnistGlyph == V.length x) ()
  hiddenVec <- inline hiddenLayerMnistV factivationHidden x vec widthHidden
  let offsetMiddle = widthHidden + 1
  middleVec <- inline middleLayerMnistV factivationHidden hiddenVec
                                        offsetMiddle vec widthHidden2
  let offsetOutput = offsetMiddle + widthHidden2 + 1
  inline middleLayerMnistV factivationOutput middleVec
                           offsetOutput vec sizeMnistLabel

nnMnistLoss2V :: ( DeltaMonad r m, Floating r, Numeric r
                 , Floating (Data.Vector.Storable.Vector r) )
              => Int
              -> Int
              -> MnistData r
              -> VecDualDelta r
              -> m (DualDelta r)
nnMnistLoss2V widthHidden widthHidden2 (x, targ) vec = do
  res <- inline nnMnist2V logisticActV softMaxActV widthHidden widthHidden2
                          x vec
  lossCrossEntropyV targ res

generalTestMnistV :: forall r. (Ord r, Fractional r, Numeric r)
                  => (Data.Vector.Storable.Vector r
                      -> VecDualDelta r
                      -> DeltaMonadValue r
                           (DualDelta (Data.Vector.Storable.Vector r)))
                  -> [MnistData r] -> (Domain r, DomainV r)
                  -> r
{-# INLINE generalTestMnistV #-}
generalTestMnistV nn xs res =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let value = valueDualDelta (nn glyph) res
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

testMnist2V :: ( Ord r, Floating r, Numeric r
               , Floating (Data.Vector.Storable.Vector r) )
            => Int -> Int -> [MnistData r] -> (Domain r, DomainV r) -> r
testMnist2V widthHidden widthHidden2 =
  generalTestMnistV (inline nnMnist2V logisticActV softMaxActV
                                      widthHidden widthHidden2)
