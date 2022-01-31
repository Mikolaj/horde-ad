{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Matrix-based (meaning that dual numbers for gradient computation
-- consider matrices, not scalars, as the primitive differentiable type)
-- implementation of fully connected neutral network for classification
-- of MNIST digits. Sports 2 hidden layers.
module HordeAd.MnistToolsMatrix where

import Prelude

import           Control.Exception (assert)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (inline)
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)

import HordeAd.DualDelta
import HordeAd.Engine
import HordeAd.MnistToolsData
import HordeAd.PairOfVectors (VecDualDelta, varL, varV)

initialLayerMnistL :: forall m r. (Numeric r, Num (Vector r))
                   => (DualDelta (Vector r) -> m (DualDelta (Vector r)))
                   -> Vector r
                   -> DualDelta (Matrix r)
                   -> DualDelta (Vector r)
                   -> m (DualDelta (Vector r))
initialLayerMnistL factivation x weightsL biasesV = do
  let multiplied = weightsL #>!! x
      biased = multiplied + biasesV
  factivation biased

middleLayerMnistL :: forall m r. (Numeric r, Num (Vector r))
                  => (DualDelta (Vector r) -> m (DualDelta (Vector r)))
                  -> DualDelta (Vector r)
                  -> DualDelta (Matrix r)
                  -> DualDelta (Vector r)
                  -> m (DualDelta (Vector r))
middleLayerMnistL factivation hiddenVec weightsL biasesV = do
  let multiplied = weightsL #>! hiddenVec
      biased = multiplied + biasesV
  factivation biased

lenMnist2L :: Int -> Int -> Int
lenMnist2L _widthHidden _widthHidden2 = 0

lenVectorsMnist2L :: Int -> Int -> Data.Vector.Vector Int
lenVectorsMnist2L widthHidden widthHidden2 =
  V.fromList [widthHidden, widthHidden2, sizeMnistLabel]

lenMatrixMnist2L :: Int -> Int -> Data.Vector.Vector (Int, Int)
lenMatrixMnist2L widthHidden widthHidden2 =
  V.fromList $ [ (widthHidden, sizeMnistGlyph)
               , (widthHidden2, widthHidden)
               , (sizeMnistLabel, widthHidden2) ]

-- Two hidden layers of width @widthHidden@ and (the middle one) @widthHidden2@.
-- Both hidden layers use the same activation function.
nnMnist2L :: (DeltaMonad r m, Numeric r, Num (Vector r))
          => (DualDelta (Vector r) -> m (DualDelta (Vector r)))
          -> (DualDelta (Vector r) -> m (DualDelta (Vector r)))
          -> Vector r
          -> VecDualDelta r
          -> m (DualDelta (Vector r))
nnMnist2L factivationHidden factivationOutput x vec = do
  let !_A = assert (sizeMnistGlyph == V.length x) ()
      weightsL0 = varL vec 0
      biasesV0 = varV vec 0
      weightsL1 = varL vec 1
      biasesV1 = varV vec 1
      weightsL2 = varL vec 2
      biasesV2 = varV vec 2
  hiddenVec <- inline initialLayerMnistL factivationHidden x weightsL0 biasesV0
  middleVec <- inline middleLayerMnistL factivationHidden hiddenVec
                                        weightsL1 biasesV1
  inline middleLayerMnistL factivationOutput middleVec weightsL2 biasesV2

nnMnistLoss2L :: ( DeltaMonad r m, Floating r, Numeric r
                 , Floating (Vector r) )
              => MnistData r
              -> VecDualDelta r
              -> m (DualDelta r)
nnMnistLoss2L (x, targ) vec = do
  res <- inline nnMnist2L logisticActV softMaxActV x vec
  lossCrossEntropyV targ res

generalTestMnistL :: forall r. (Ord r, Fractional r, Numeric r)
                  => (Vector r
                      -> VecDualDelta r
                      -> DeltaMonadValue r (DualDelta (Vector r)))
                  -> [MnistData r] -> (Domain r, DomainV r, DomainL r)
                  -> r
{-# INLINE generalTestMnistL #-}
generalTestMnistL nn xs res =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let value = valueDualDelta (nn glyph) res
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels xs)) / fromIntegral (length xs)

testMnist2L :: ( Ord r, Floating r, Numeric r
               , Floating (Vector r) )
            => [MnistData r] -> (Domain r, DomainV r, DomainL r) -> r
testMnist2L = generalTestMnistL (inline nnMnist2L logisticActV softMaxActV)
