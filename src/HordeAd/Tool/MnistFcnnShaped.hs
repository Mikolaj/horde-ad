{-# LANGUAGE AllowAmbiguousTypes, DataKinds, ImpredicativeTypes, RankNTypes,
             TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Shaped tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers.
module HordeAd.Tool.MnistFcnnShaped where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

-- commented out until inline doesn't break compilation below
-- import           GHC.Exts (inline)

import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors (DualNumberVariables, varS)
import HordeAd.Tool.MnistData

lenMnistFcnnS :: Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
lenMnistFcnnS widthHidden widthHidden2 =
  ( 0
  , []
  , []
  , [ [widthHidden, sizeMnistGlyph], [widthHidden]
    , [widthHidden2, widthHidden], [widthHidden2]
    , [sizeMnistLabel, widthHidden2], [sizeMnistLabel] ]
  )

type SizeMnistGlyph = 28 GHC.TypeLits.* 28
type SizeMnistLabel = 10 :: Nat

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The width of the layers is determined by the dimensions of the matrices
-- and vectors given as dual number parameters (variables).
-- The dimensions, in turn, can be computed by the @len*@ functions
-- on the basis of the requested widths, see above.
nnMnistS :: forall widthHidden widthHidden2 r m.
            (DualMonad r m, KnownNat widthHidden, KnownNat widthHidden2)
         => (forall sh. OS.Shape sh
             => DualNumber (TensorS r sh) -> m (DualNumber (TensorS r sh)))
         -> Primal (TensorS r '[SizeMnistGlyph])
         -> DualNumberVariables r
         -> m (DualNumber (TensorS r '[SizeMnistLabel]))
nnMnistS factivationHidden input variables = do
  let !_A = assert (sizeMnistGlyph == OS.size input) ()
      weightsL0 :: DualNumber (TensorS r '[widthHidden, SizeMnistGlyph])
      weightsL0 = varS variables 0
      biasesV0 :: DualNumber (TensorS r '[widthHidden])
      biasesV0 = varS variables 1
      weightsL1 :: DualNumber (TensorS r '[widthHidden2, widthHidden])
      weightsL1 = varS variables 2
      biasesV1 :: DualNumber (TensorS r '[widthHidden2])
      biasesV1 = varS variables 3
      weightsL2 :: DualNumber (TensorS r '[SizeMnistLabel, widthHidden2])
      weightsL2 = varS variables 4
      biasesV2 :: DualNumber (TensorS r '[SizeMnistLabel])
      biasesV2 = varS variables 5
  let hiddenLayer1 = weightsL0 #>$ (scalar input) + biasesV0
  nonlinearLayer1 <- factivationHidden hiddenLayer1
  let hiddenLayer2 = weightsL1 #>$ nonlinearLayer1 + biasesV1
  nonlinearLayer2 <- factivationHidden hiddenLayer2
  let outputLayer = weightsL2 #>$ nonlinearLayer2 + biasesV2
  returnLet outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function, using fused
-- softMax and cross entropy as the loss function.
nnMnistLossFusedS
  :: forall widthHidden widthHidden2 r m.
     ( DualMonad r m, Floating (Primal (Tensor1 r))
     , KnownNat widthHidden, KnownNat widthHidden2 )
  => MnistData (Primal r) -> DualNumberVariables r -> m (DualNumber r)
nnMnistLossFusedS (input, target) variables = do
  result <- {-inline!!!-} (nnMnistS @widthHidden @widthHidden2)
              logisticAct (OS.fromVector input) variables
  lossSoftMaxCrossEntropyV target $ fromS1 result

nnMnistLossFusedReluS
  :: forall widthHidden widthHidden2 r m.
     ( DualMonad r m, Floating (Primal (Tensor1 r))
     , KnownNat widthHidden, KnownNat widthHidden2 )
  => MnistData (Primal r) -> DualNumberVariables r -> m (DualNumber r)
nnMnistLossFusedReluS (input, target) variables = do
  result <- {-inline!!!-} (nnMnistS @widthHidden @widthHidden2)
              reluActS (OS.fromVector input) variables
  lossSoftMaxCrossEntropyV target $ fromS1 result

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
testMnistS
  :: forall widthHidden widthHidden2 r.
     (IsScalar r, KnownNat widthHidden, KnownNat widthHidden2)
  => [MnistData (Primal r)] -> Domains r -> Primal r
testMnistS inputs parameters =
  let matchesLabels :: MnistData (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = {-inline!!!-} (nnMnistS @widthHidden @widthHidden2)
                   logisticAct (OS.fromVector glyph)
            value = OS.toVector $ primalValue @r nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
