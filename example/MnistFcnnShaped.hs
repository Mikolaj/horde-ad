{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers. No mini-batches.
module MnistFcnnShaped where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V

import HordeAd
import MnistData

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The width of the layers is determined by the dimensions of the matrices
-- and vectors given as dual number parameters (inputs).
-- The dimensions, in turn, can be computed by the @len*@ functions
-- on the basis of the requested widths, see above.
fcnnMnistLayersS
  :: forall widthHidden widthHidden2 d r. ADModeAndNum d r
  => SNat widthHidden -> SNat widthHidden2
  -> (forall sh. OS.Shape sh
      => ADVal d (OS.Array sh r) -> ADVal d (OS.Array sh r))
  -> OS.Array '[SizeMnistGlyph] r
  -- All below is the type of all paramters of this nn. The same is reflected
  -- in the length function below and read from inputs further down.
  -> ADFcnnMnistParameters widthHidden widthHidden2 d r
  -> ADVal d (OS.Array '[SizeMnistLabel] r)
fcnnMnistLayersS SNat SNat factivationHidden datum
                 ( (weightsL0, biasesV0)
                 , (weightsL1, biasesV1)
                 , (weightsL2, biasesV2) ) =
  let !_A = assert (sizeMnistGlyphInt == OS.size datum) ()
      hiddenLayer1 = weightsL0 #>$ constant datum + biasesV0
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = weightsL1 #>$ nonlinearLayer1 + biasesV1
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = weightsL2 #>$ nonlinearLayer2 + biasesV2
  in outputLayer

-- The differentiable type of all trainable parameters of this nn.
type ADFcnnMnistParameters widthHidden widthHidden2 d r =
  ( ( ADVal d (OS.Array '[widthHidden, SizeMnistGlyph] r)
    , ADVal d (OS.Array '[widthHidden] r) )
  , ( ADVal d (OS.Array '[widthHidden2, widthHidden] r)
    , ADVal d (OS.Array '[widthHidden2] r) )
  , ( ADVal d (OS.Array '[SizeMnistLabel, widthHidden2] r)
    , ADVal d (OS.Array '[SizeMnistLabel] r) )
  )

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function, using fused
-- softMax and cross entropy as the loss function.
afcnnMnistLossFusedS
  :: forall widthHidden widthHidden2 d r. ADModeAndNum d r
  => SNat widthHidden -> SNat widthHidden2
  -> MnistData r
  -> ADFcnnMnistParameters widthHidden widthHidden2 d r
  -> ADVal d r
afcnnMnistLossFusedS widthHidden widthHidden2 (datum, target) adparameters =
  let result = fcnnMnistLayersS widthHidden widthHidden2
                                logistic (OS.fromVector datum) adparameters
  in lossSoftMaxCrossEntropyV target $ fromS1 result

afcnnMnistLossFusedReluS
  :: forall widthHidden widthHidden2 d r. ADModeAndNum d r
  => SNat widthHidden -> SNat widthHidden2
  -> MnistData r
  -> ADFcnnMnistParameters widthHidden widthHidden2 d r
  -> ADVal d r
afcnnMnistLossFusedReluS widthHidden widthHidden2 (datum, target) adparameters =
  let result = fcnnMnistLayersS widthHidden widthHidden2
                                relu (OS.fromVector datum) adparameters
  in lossSoftMaxCrossEntropyV target $ fromS1 result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTestS
  :: forall widthHidden widthHidden2 r. ADModeAndNum 'ADModeValue r
  => SNat widthHidden -> SNat widthHidden2
  -> [MnistData r]
  -> ((ADFcnnMnistParameters widthHidden widthHidden2 'ADModeValue r
       -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel] r))
      -> OS.Array '[SizeMnistLabel] r)
  -> r
afcnnMnistTestS widthHidden widthHidden2 inputs evalAtTestParams =
  let matchesLabels :: MnistData r -> Bool
      matchesLabels (glyph, label) =
        let nn :: ADFcnnMnistParameters widthHidden widthHidden2 'ADModeValue r
               -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel] r)
            nn = fcnnMnistLayersS widthHidden widthHidden2
                                  logistic (OS.fromVector glyph)
            v = OS.toVector $ evalAtTestParams nn
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
