{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of fully connected neutral network
-- for classification of MNIST digits. Sports 2 hidden layers. No mini-batches,
-- so the maximum rank of tensors being used is 2.
module MnistFcnnRanked2 where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.Exts (inline)
import GHC.TypeLits (Nat)
import System.Random

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Ranked.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersAst
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADFcnnMnist2ParametersShaped
       (target :: Target) (widthHidden :: Nat) (widthHidden2 :: Nat) r q =
  ( ( target (TKS '[widthHidden, SizeMnistGlyph] r)
    , target (TKS '[widthHidden] r) )
  , ( target (TKS '[widthHidden2, widthHidden] q)
    , target (TKS '[widthHidden2] r) )
  , ( target (TKS '[SizeMnistLabel, widthHidden2] r)
    , target (TKS '[SizeMnistLabel] r) )
  )

-- | The differentiable type of all trainable parameters of this nn.
type ADFcnnMnist2Parameters (target :: Target) r q =
  ( ( target (TKR 2 r)
    , target (TKR 1 r) )
  , ( target (TKR 2 q)
    , target (TKR 1 r) )
  , ( target (TKR 2 r)
    , target (TKR 1 r) )
  )

type XParams2 r q = X (MnistFcnnRanked2.ADFcnnMnist2Parameters Concrete r q)

-- | Fully connected neural network for the MNIST digit classification task.
-- There are two hidden layers and both use the same activation function.
-- The output layer uses a different activation function.
-- The widths of the two hidden layers are @widthHidden@ and @widthHidden2@,
-- respectively.
afcnnMnist2 :: ( ADReady target, NumScalar r, Differentiable r
               , NumScalar q, Differentiable q )
            => (target (TKR 1 r) -> target (TKR 1 r))
            -> (target (TKR 1 r) -> target (TKR 1 r))
            -> target (TKR 1 r)
            -> ADFcnnMnist2Parameters target r q
            -> target (TKR 1 r)
afcnnMnist2 factivationHidden factivationOutput
            datum ((hidden, bias), (hidden2, bias2), (readout, biasr)) =
  let hiddenLayer1 = rmatvecmul hidden datum + bias
      nonlinearLayer1 = factivationHidden hiddenLayer1
      hiddenLayer2 = rcast (rmatvecmul hidden2 (rcast nonlinearLayer1)) + bias2
      nonlinearLayer2 = factivationHidden hiddenLayer2
      outputLayer = rmatvecmul readout nonlinearLayer2 + biasr
  in factivationOutput outputLayer

-- | The neural network applied to concrete activation functions
-- and composed with the appropriate loss function.
afcnnMnistLoss2
  :: ( ADReady target, NumScalar r, Differentiable r
     , NumScalar q, Differentiable q )
  => (target (TKR 1 r), target (TKR 1 r)) -> ADFcnnMnist2Parameters target r q
  -> target (TKScalar r)
afcnnMnistLoss2 (datum, target) adparams =
  let result = inline afcnnMnist2 logistic softMax1 datum adparams
  in lossCrossEntropyV target result
{-# SPECIALIZE afcnnMnistLoss2 :: (ADVal Concrete (TKR 1 Double), ADVal Concrete (TKR 1 Double)) -> ADFcnnMnist2Parameters (ADVal Concrete) Double Float -> ADVal Concrete (TKScalar Double) #-}
{-# SPECIALIZE afcnnMnistLoss2 :: (ADVal Concrete (TKR 1 Float), ADVal Concrete (TKR 1 Float)) -> ADFcnnMnist2Parameters (ADVal Concrete) Float Float -> ADVal Concrete (TKScalar Float) #-}
{-# SPECIALIZE afcnnMnistLoss2 :: (ADVal Concrete (TKR 1 Double), ADVal Concrete (TKR 1 Double)) -> ADFcnnMnist2Parameters (ADVal Concrete) Double Double -> ADVal Concrete (TKScalar Double) #-}

-- | A function testing the neural network given testing set of inputs
-- and the trained parameters.
afcnnMnistTest2
  :: forall target r q.
     ( target ~ Concrete, NumScalar r, Differentiable r
     , NumScalar q, Differentiable q )
  => [MnistDataLinearR r]
  -> ADFcnnMnist2Parameters target r q
  -> r
afcnnMnistTest2 [] _ = 0
afcnnMnistTest2 dataList testParams =
  let matchesLabels :: MnistDataLinearR r -> Bool
      matchesLabels (glyph, label) =
        let glyph1 = rconcrete glyph
            nn :: ADFcnnMnist2Parameters target r q
               -> target (TKR 1 r)
            nn = inline afcnnMnist2 logistic softMax1 glyph1
            v = rtoVector $ nn testParams
        in V.maxIndex v == V.maxIndex (Nested.rtoVector label)
  in fromIntegral (length (filter matchesLabels dataList))
     / fromIntegral (length dataList)

-- | The loss function applied to randomly generated initial parameters
-- and wrapped in artifact generation. This is helpful to share code
-- between tests and benchmarks and to separate compile-time and run-time
-- for benchmarking (this part is considered compile-time).
mnistTrainBench2VTOGradient
  :: forall r q. ( NumScalar r, Differentiable r
                 , NumScalar q, Differentiable q )
  => Proxy q -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int
  -> ( Concrete (XParams2 r q)
     , AstArtifactRev
         (TKProduct
            (XParams2 r q)
            (TKProduct (TKR2 1 (TKScalar r))
                       (TKR2 1 (TKScalar r))))
         (TKScalar r) )
mnistTrainBench2VTOGradient Proxy cotangentHandling range seed widthHidden widthHidden2 =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  -- Initial parameter generation is counted as part of compilation time.
  let targetInit =
        forgetShape $ fst
        $ randomValue @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   Concrete widthHidden widthHidden2 r q)))
                      range seed
      ftk = tftk @Concrete (knownSTK @(XParams2 r q)) targetInit
      ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                           (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
      f :: ( MnistFcnnRanked2.ADFcnnMnist2Parameters
               (AstTensor AstMethodLet FullSpan) r q
           , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
             , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
        -> AstTensor AstMethodLet FullSpan (TKScalar r)
      f (pars, (glyphR, labelR)) =
        afcnnMnistLoss2 (glyphR, labelR) pars
      artRaw = revArtifactAdapt cotangentHandling f (FTKProduct ftk ftkData)
  in (targetInit, artRaw)
{-# SPECIALIZE mnistTrainBench2VTOGradient :: Proxy Float -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Double Float), AstArtifactRev (TKProduct (XParams2 Double Float) (TKProduct (TKR2 1 (TKScalar Double)) (TKR2 1 (TKScalar Double)))) (TKScalar Double) ) #-}
{-# SPECIALIZE mnistTrainBench2VTOGradient :: Proxy Float -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Float Float), AstArtifactRev (TKProduct (XParams2 Float Float) (TKProduct (TKR2 1 (TKScalar Float)) (TKR2 1 (TKScalar Float)))) (TKScalar Float) ) #-}
{-# SPECIALIZE mnistTrainBench2VTOGradient :: Proxy Double -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Double Double), AstArtifactRev (TKProduct (XParams2 Double Double) (TKProduct (TKR2 1 (TKScalar Double)) (TKR2 1 (TKScalar Double)))) (TKScalar Double) ) #-}

-- | A version of 'mnistTrainBench2VTOGradient' without any simplification,
-- even the AST smart constructors. Intended for benchmarking.
mnistTrainBench2VTOGradientX
  :: forall r q. ( NumScalar r, Differentiable r
                 , NumScalar q, Differentiable q )
  => Proxy q -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int
  -> ( Concrete (XParams2 r q)
     , AstArtifactRev
         (TKProduct
            (XParams2 r q)
            (TKProduct (TKR2 1 (TKScalar r))
                       (TKR2 1 (TKScalar r))))
         (TKScalar r) )
mnistTrainBench2VTOGradientX Proxy cotangentHandling range seed widthHidden widthHidden2 =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  -- Initial parameter generation is counted as part of compilation time.
  let targetInit =
        forgetShape $ fst
        $ randomValue @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   Concrete widthHidden widthHidden2 r q)))
                      range seed
      ftk = tftk @Concrete (knownSTK @(XParams2 r q)) targetInit
      ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                           (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
      f :: ( MnistFcnnRanked2.ADFcnnMnist2Parameters
               (AstTensor AstMethodLet FullSpan) r q
           , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
             , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
        -> AstTensor AstMethodLet FullSpan (TKScalar r)
      f (((hidden, bias), (hidden2, bias2), (readout, biasr)), (glyphR, labelR)) =
        unAstNoSimplify
        $ afcnnMnistLoss2 (AstNoSimplify glyphR, AstNoSimplify labelR)
                          ( (AstNoSimplify hidden, AstNoSimplify bias)
                          , (AstNoSimplify hidden2, AstNoSimplify bias2)
                          , (AstNoSimplify readout, AstNoSimplify biasr) )
      artRaw = revArtifactAdapt cotangentHandling f (FTKProduct ftk ftkData)
  in (targetInit, artRaw)
{-# SPECIALIZE mnistTrainBench2VTOGradientX :: Proxy Float -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Double Float), AstArtifactRev (TKProduct (XParams2 Double Float) (TKProduct (TKR2 1 (TKScalar Double)) (TKR2 1 (TKScalar Double)))) (TKScalar Double) ) #-}
{-# SPECIALIZE mnistTrainBench2VTOGradientX :: Proxy Float -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Float Float), AstArtifactRev (TKProduct (XParams2 Float Float) (TKProduct (TKR2 1 (TKScalar Float)) (TKR2 1 (TKScalar Float)))) (TKScalar Float) ) #-}
{-# SPECIALIZE mnistTrainBench2VTOGradientX :: Proxy Double -> IncomingCotangentHandling -> Double -> StdGen -> Int -> Int -> ( Concrete (XParams2 Double Double), AstArtifactRev (TKProduct (XParams2 Double Double) (TKProduct (TKR2 1 (TKScalar Double)) (TKR2 1 (TKScalar Double)))) (TKScalar Double) ) #-}
