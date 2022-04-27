{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ImpredicativeTypes,
             TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnShaped where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shape
import qualified Data.Array.ShapedS as OS
import           Data.Proxy (Proxy)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, varS)
import HordeAd.Tool.MnistData

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The width of the layers is determined by the dimensions of the matrices
-- and vectors given as dual number parameters (variables).
-- The dimensions, in turn, can be computed by the @len*@ functions
-- on the basis of the requested widths, see above.
fcnnMnistLayersS
  :: forall widthHidden widthHidden2 r m.
     (DualMonad r m, KnownNat widthHidden, KnownNat widthHidden2)
  => (forall sh. OS.Shape sh
      => DualNumber (TensorS r sh) -> m (DualNumber (TensorS r sh)))
  -> Primal (TensorS r '[SizeMnistGlyph])
  -- All below is the type of all paramters of this nn. The same is reflected
  -- in the length function below and read from variables further down.
  -> DualNumber (TensorS r '[widthHidden, SizeMnistGlyph])
  -> DualNumber (TensorS r '[widthHidden])
  -> DualNumber (TensorS r '[widthHidden2, widthHidden])
  -> DualNumber (TensorS r '[widthHidden2])
  -> DualNumber (TensorS r '[SizeMnistLabel, widthHidden2])
  -> DualNumber (TensorS r '[SizeMnistLabel])
  -> m (DualNumber (TensorS r '[SizeMnistLabel]))
fcnnMnistLayersS factivationHidden input
                 weightsL0 biasesV0 weightsL1 biasesV1 weightsL2 biasesV2 = do
  let !_A = assert (sizeMnistGlyph == OS.size input) ()
  let hiddenLayer1 = weightsL0 #>$ scalar input + biasesV0
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let hiddenLayer2 = weightsL1 #>$ nonlinearLayer1 + biasesV1
  nonlinearLayer2 <- factivationHidden hiddenLayer2
  let outputLayer = weightsL2 #>$ nonlinearLayer2 + biasesV2
  returnLet outputLayer

-- It seems that without plugins or TH we really have to copy-paste
-- the six-element type list from signature of @nnMnistLayersS@.
fcnnMnistLenS
  :: forall widthHidden widthHidden2.
     (KnownNat widthHidden, KnownNat widthHidden2)
  => (Int, [Int], [(Int, Int)], [OT.ShapeL])
fcnnMnistLenS =
  ( 0
  , []
  , []
  , [ Data.Array.Shape.shapeT @'[widthHidden, SizeMnistGlyph]
    , Data.Array.Shape.shapeT @'[widthHidden]
    , Data.Array.Shape.shapeT @'[widthHidden2, widthHidden]
    , Data.Array.Shape.shapeT @'[widthHidden2]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel, widthHidden2]
    , Data.Array.Shape.shapeT @'[SizeMnistLabel]
    ]
  )

fcnnMnistS
  :: forall widthHidden widthHidden2 r m.
     (DualMonad r m, KnownNat widthHidden, KnownNat widthHidden2)
  => (forall sh. OS.Shape sh
      => DualNumber (TensorS r sh) -> m (DualNumber (TensorS r sh)))
  -> Primal (TensorS r '[SizeMnistGlyph])
  -> DualNumberVariables r
  -> m (DualNumber (TensorS r '[SizeMnistLabel]))
{-# INLINE fcnnMnistS #-}
fcnnMnistS factivationHidden input variables = do
  let weightsL0 = varS variables 0
      biasesV0 = varS variables 1
      weightsL1 = varS variables 2
      biasesV1 = varS variables 3
      weightsL2 = varS variables 4
      biasesV2 = varS variables 5
  fcnnMnistLayersS @widthHidden @widthHidden2
                   factivationHidden input
                   weightsL0 biasesV0 weightsL1 biasesV1 weightsL2 biasesV2

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function, using fused
-- softMax and cross entropy as the loss function.
--
-- The silly proxies are needed due to the compilation hiccup
-- from the last example at
-- https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/exts/ambiguous_types.html#extension-AllowAmbiguousTypes
fcnnMnistLossFusedS
  :: forall widthHidden widthHidden2 r m.
     (DualMonad r m, KnownNat widthHidden, KnownNat widthHidden2)
  => Proxy widthHidden -> Proxy widthHidden2
  -> MnistData (Primal r) -> DualNumberVariables r -> m (DualNumber r)
fcnnMnistLossFusedS _ _ (input, target) variables = do
  result <- fcnnMnistS @widthHidden @widthHidden2
                       logisticAct (OS.fromVector input) variables
  lossSoftMaxCrossEntropyV target $ fromS1 result

fcnnMnistLossFusedReluS
  :: forall widthHidden widthHidden2 r m.
     (DualMonad r m, KnownNat widthHidden, KnownNat widthHidden2)
  => Proxy widthHidden -> Proxy widthHidden2
  -> MnistData (Primal r) -> DualNumberVariables r -> m (DualNumber r)
fcnnMnistLossFusedReluS _ _ (input, target) variables = do
  result <- fcnnMnistS @widthHidden @widthHidden2
                       reluAct (OS.fromVector input) variables
  lossSoftMaxCrossEntropyV target $ fromS1 result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
fcnnMnistTestS
  :: forall widthHidden widthHidden2 r.
     (IsScalar r, KnownNat widthHidden, KnownNat widthHidden2)
  => [MnistData (Primal r)] -> Domains r -> Primal r
fcnnMnistTestS inputs parameters =
  let matchesLabels :: MnistData (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = fcnnMnistS @widthHidden @widthHidden2
                            logisticAct (OS.fromVector glyph)
            value = OS.toVector $ primalValue @r nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
