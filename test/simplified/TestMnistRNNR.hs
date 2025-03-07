{-# LANGUAGE OverloadedLists #-}
-- | Tests of "MnistRnnRanked2" neural networks using a few different
-- optimization pipelines.
--
-- *Not* LSTM.
-- Doesn't train without Adam, regardless of whether mini-batches used. It does
-- train with Adam, but only after very carefully tweaking initialization.
-- This is extremely sensitive to initial parameters, more than to anything
-- else. Probably, gradient is vanishing if parameters are initialized
-- with a probability distribution that doesn't have the right variance. See
-- https://stats.stackexchange.com/questions/301285/what-is-vanishing-gradient.
module TestMnistRNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Numeric.LinearAlgebra (Numeric)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested (ShR (..))

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.External.OptimizerTools

import EqEpsilon

import MnistData
import MnistRnnRanked2 (ADRnnMnistParameters, ADRnnMnistParametersShaped)
import MnistRnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNA
  :: forall r.
     ( Differentiable r, GoodScalar r, Numeric r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNA prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  withSNat width $ \(SNat @width) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (ADRnnMnistParametersShaped RepN width r)))
                      0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(X (ADRnnMnistParameters RepN r))
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (X (ADRnnMnistParameters RepN r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (fromTarget @RepN pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           f :: MnistDataBatchR r
             -> ADVal RepN (X (ADRnnMnistParameters RepN r))
             -> ADVal RepN (TKScalar r)
           f (glyphR, labelR) adinputs =
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rconcrete glyphR, rconcrete labelR)
               (fromTarget @(ADVal RepN) adinputs)
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdam (X (ADRnnMnistParameters RepN r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam @(MnistDataBatchR r)
                               @(X (ADRnnMnistParameters RepN r))
                               f chunkR parameters stateAdam
                 trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
           ftk = tftk @RepN (knownSTK @(X (ADRnnMnistParameters RepN r)))
                      targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNA
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNA :: TestTree
tensorADValMnistTestsRNNA = testGroup "RNN ADVal MNIST tests"
  [ mnistTestCaseRNNA "RNNA 1 epoch, 1 batch" 1 1 128 5 50
                       (0.94 :: Double)
  , mnistTestCaseRNNA "RNNA artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNA "RNNA artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNA "RNNA 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNI
  :: forall r.
     ( Differentiable r, GoodScalar r, Numeric r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNI prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  withSNat width $ \(SNat @width) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (ADRnnMnistParametersShaped RepN width r)))
                      0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(X (ADRnnMnistParameters RepN r))
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (X (ADRnnMnistParameters RepN r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (fromTarget @RepN pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           ftk = tftk @RepN (knownSTK @(X (ADRnnMnistParameters RepN r)))
                      targetInit
       (_, _, var, varAst) <- funToAstRevIO ftk
       (varGlyph, astGlyph) <-
         funToAstIO (FTKR (miniBatchSize
                           :$: sizeMnistHeightInt
                           :$: sizeMnistWidthInt
                           :$: ZSR) FTKScalar) id
       (varLabel, astLabel) <-
         funToAstIO (FTKR (miniBatchSize
                           :$: sizeMnistLabelInt
                           :$: ZSR) FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
           ast = MnistRnnRanked2.rnnMnistLossFusedR
                   miniBatchSize (astGlyph, astLabel)
                   (fromTarget varAst)
           f :: MnistDataBatchR r
              -> ADVal RepN (X (ADRnnMnistParameters RepN r))
              -> ADVal RepN (TKScalar r)
           f (glyph, label) varInputs =
             let env = extendEnv var varInputs emptyEnv
                 envMnist = extendEnv varGlyph (rconcrete glyph)
                            $ extendEnv varLabel (rconcrete label) env
             in interpretAst envMnist ast
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdam (X (ADRnnMnistParameters RepN r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam @(MnistDataBatchR r)
                               @(X (ADRnnMnistParameters RepN r))
                               f chunkR parameters stateAdam
                 trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNI
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNI :: TestTree
tensorADValMnistTestsRNNI = testGroup "RNN Intermediate MNIST tests"
  [ mnistTestCaseRNNI "RNNI 1 epoch, 1 batch" 1 1 128 5 50
                       (0.9 :: Double)
  , mnistTestCaseRNNI "RNNI artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNI "RNNI artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNI "RNNI 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNO
  :: forall r.
     ( Differentiable r, GoodScalar r, Numeric r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Int -> r
  -> TestTree
mnistTestCaseRNNO prefix epochs maxBatches width miniBatchSize totalBatchSize
                  expected =
  withSNat width $ \(SNat @width) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (ADRnnMnistParametersShaped RepN width r)))
                      0.4 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(X (ADRnnMnistParameters RepN r))
                        , show (tsize knownSTK targetInit) ]
      ftest :: Int -> MnistDataBatchR r
            -> RepN (X (ADRnnMnistParameters RepN r))
            -> r
      ftest batch_size mnistData pars =
        MnistRnnRanked2.rnnMnistTestR
          batch_size mnistData (fromTarget @RepN pars)
  in testCase name $ do
       hPutStrLn stderr $
         printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                prefix epochs maxBatches
       trainData <- map mkMnistDataR
                    <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map mkMnistDataR . take (totalBatchSize * maxBatches)
                   <$> loadMnistData testGlyphsPath testLabelsPath
       let testDataR = mkMnistDataBatchR testData
           ftk = tftk @RepN (knownSTK @(X (ADRnnMnistParameters RepN r)))
                      targetInit
           ftkData = FTKProduct (FTKR (miniBatchSize
                                       :$: sizeMnistHeightInt
                                       :$: sizeMnistWidthInt
                                       :$: ZSR) FTKScalar)
                                (FTKR (miniBatchSize
                                       :$: sizeMnistLabelInt
                                       :$: ZSR) FTKScalar)
           f :: ( ADRnnMnistParameters (AstTensor AstMethodLet FullSpan) r
                , ( AstTensor AstMethodLet FullSpan (TKR 3 r)
                  , AstTensor AstMethodLet FullSpan (TKR 2 r) ) )
             -> AstTensor AstMethodLet FullSpan (TKScalar r)
           f = \ (pars, (glyphR, labelR)) ->
             MnistRnnRanked2.rnnMnistLossFusedR
               miniBatchSize (rprimalPart glyphR, rprimalPart labelR) pars
           (artRaw, _) = revArtifactAdapt False f (FTKProduct ftk ftkData)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchR r]
              -> ( RepN (X (ADRnnMnistParameters RepN r))
                 , StateAdam (X (ADRnnMnistParameters RepN r)) )
              -> ( RepN (X (ADRnnMnistParameters RepN r))
                 , StateAdam (X (ADRnnMnistParameters RepN r)) )
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let parametersAndInput =
                   tpair parameters (tpair (rconcrete glyph) (rconcrete label))
                 gradient = tproject1 $ fst
                            $ revEvalArtifact art parametersAndInput Nothing
             in go rest (updateWithGradientAdam
                           @(X (ADRnnMnistParameters RepN r))
                           defaultArgsAdam stateAdam knownSTK parameters
                           gradient)
           runBatch :: ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> (Int, [MnistDataR r])
                    -> IO ( RepN (X (ADRnnMnistParameters RepN r))
                          , StateAdam (X (ADRnnMnistParameters RepN r)) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkR = map mkMnistDataBatchR
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkR (parameters, stateAdam)
                 trainScore =
                   ftest (length chunk) (mkMnistDataBatchR chunk) parameters2
                 testScore =
                   ftest (totalBatchSize * maxBatches) testDataR parameters2
                 lenChunk = length chunk
             unless (width < 10) $ do
               hPutStrLn stderr $
                 printf "\n%s: (Batch %d with %d points)"
                        prefix k lenChunk
               hPutStrLn stderr $
                 printf "%s: Training error:   %.2f%%"
                        prefix ((1 - trainScore) * 100)
               hPutStrLn stderr $
                 printf "%s: Validation error: %.2f%%"
                        prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> ( RepN (X (ADRnnMnistParameters RepN r))
                       , StateAdam (X (ADRnnMnistParameters RepN r)) )
                    -> IO (RepN (X (ADRnnMnistParameters RepN r)))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal =
             1 - ftest (totalBatchSize * maxBatches) testDataR res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

{-# SPECIALIZE mnistTestCaseRNNO
  :: String
  -> Int -> Int -> Int -> Int -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNO :: TestTree
tensorADValMnistTestsRNNO = testGroup "RNN Once MNIST tests"
  [ mnistTestCaseRNNO "RNNO 1 epoch, 1 batch" 1 1 128 5 500
                       (0.898 :: Double)
  , mnistTestCaseRNNO "RNNO artificial 1 2 3 4 5" 2 3 4 5 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNO "RNNO artificial 5 4 3 2 1" 5 4 3 2 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNO "RNNO 1 epoch, 0 batch" 1 0 128 5 50
                       (1.0 :: Float)
  ]
