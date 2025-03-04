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
import Data.IntMap.Strict qualified as IM
import Numeric.LinearAlgebra (Numeric)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested (ShR (..))
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.External.OptimizerTools

import EqEpsilon

import MnistData
import MnistRnnRanked2 (ADRnnMnistParameters, ADRnnMnistParametersShaped)
import MnistRnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNA
            , tensorADValMnistTestsRNNI
            , tensorADValMnistTestsRNNO
            , tensorMnistTestsPP
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

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for RNN MNIST tests"
  [ testCase "RNNO PP" testRNNOPP
  , testCase "RNNO PP 2" testRNNOPP2
  ]

valsInitRNNOPP
  :: Int -> Int -> ADRnnMnistParameters RepN Double
valsInitRNNOPP out_width sizeMnistHeightI =
  ( ( RepN
      $ Nested.rfromListPrimLinear [out_width, sizeMnistHeightI]
                    (map fromIntegral [0 .. out_width * sizeMnistHeightI - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width]
                                   (map fromIntegral [0 .. out_width - 1]) )
  , ( RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width, out_width]
                    (map fromIntegral [0 .. out_width * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [out_width]
                                   (map fromIntegral [0 .. out_width - 1]) )
  , ( RepN
       $ Nested.rfromListPrimLinear [sizeMnistLabelInt, out_width]
                    (map fromIntegral [0 .. sizeMnistLabelInt * out_width - 1])
    , RepN
      $ Nested.rfromListPrimLinear [sizeMnistLabelInt]
                    (map fromIntegral [0 .. sizeMnistLabelInt - 1]) ) )

testRNNOPP :: Assertion
testRNNOPP = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 1
      sizeMnistHeightI = 1
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @1) knownSTK
                   $ AstReplicate (SNat @1) knownSTK
                   $ AstReplicate (SNat @1) knownSTK
                       (tconcrete (FTKR ZSR FTKScalar)
                                  (RepN $ Nested.rscalar 7)
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      ftk = tftk @RepN (knownSTK @(X (ADRnnMnistParameters RepN Double)))
                       (toTarget @RepN $ valsInitRNNOPP 1 sizeMnistHeightI)
      (artifactRev, _) = revArtifactAdapt True afcnn2T ftk
  printArtifactPretty renames artifactRev
    @?= "\\m6 m1 -> let m2 = tanh ((ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @1 (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0))))) + ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t3 = str (sreplicate @_ @1 m2) ; m4 = tanh ((ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t3) + ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t5 = str (sreplicate @_ @10 m4) ; m7 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m4 * m4) * ssum @_ @10 (str (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @_ @1 (sfromR m6))) ; t8 = sreplicate @_ @1 m7 ; m9 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m2 * m2) * ssum @_ @1 (str (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t8)) in tpair (tpair (tpair (tpair (rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (str (sreplicate @_ @1 (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0)))) * sreplicate @_ @1 m9))), rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))) * sreplicate @_ @1 m9)))), rfromS (ssum @_ @1 (str m9))), tpair (tpair (rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (t3 * t8))), rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))) * sreplicate @_ @1 m7)))), rfromS (ssum @_ @1 (str m7)))), tpair (rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (t5 * sreplicate @_ @1 (sfromR m6)))), rfromS (ssum @_ @1 (str (sfromR m6)))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 -> let m2 = tanh ((ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @1 (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0))))) + ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t3 = str (sreplicate @_ @1 m2) ; m4 = tanh ((ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t3) + ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @_ @1 (sconcrete (sfromListLinear [1,1] [0.0]))))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t5 = str (sreplicate @_ @10 m4) in rfromS (ssum @_ @1 (stranspose @_ @[2,1,0] (sreplicate @_ @1 (sfromR (tproject1 (tproject2 m1)))) * t5) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m6 m1 -> tfromS (let m2 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [1,1] [0.0]))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m2 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [1,1] [0.0]))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m4 * m4) * smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR m6) ; m9 = (sconcrete (sfromListLinear [1,1] [1.0]) + negate m2 * m2) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m7 in tpair (tpair (tpair (tpair (smatmul2 m9 (str (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0)))), smatmul2 m9 (sconcrete (sfromListLinear [1,1] [0.0]))), ssum @_ @1 (str m9)), tpair (tpair (smatmul2 m7 (str m2), smatmul2 m7 (sconcrete (sfromListLinear [1,1] [0.0]))), ssum @_ @1 (str m7))), tpair (smatmul2 (sfromR m6) (str m4), ssum @_ @1 (str (sfromR m6)))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @1 (sreplicate @_ @1 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [1,1] [0.0]))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [1,1] [0.0]))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @_ @1 (sfromR (tproject2 (tproject2 m1)))))"

testRNNOPP2 :: Assertion
testRNNOPP2 = do
  resetVarCounter
  let renames = IM.empty
      batch_size = 2
      sizeMnistHeightI = 2
      blackGlyph :: AstTensor AstMethodLet PrimalSpan (TKR 3 Double)
      blackGlyph = AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                   $ AstReplicate (SNat @2) knownSTK
                       (tconcrete (FTKR ZSR FTKScalar)
                                  (RepN $ Nested.rscalar 7)
                        :: AstTensor AstMethodLet PrimalSpan (TKR 0 Double))
      afcnn2T :: ADRnnMnistParameters (AstTensor AstMethodLet FullSpan)
                                                      Double
              -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      afcnn2T = MnistRnnRanked2.rnnMnistZeroR batch_size blackGlyph
      ftk = tftk @RepN (knownSTK @(X (ADRnnMnistParameters RepN Double)))
                       (toTarget @RepN $ valsInitRNNOPP 2 sizeMnistHeightI)
      (artifactRev, _) = revArtifactAdapt True afcnn2T ftk
  printArtifactPretty renames artifactRev
    @?= "\\m16 m1 -> let m3 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t5 = str (sreplicate @_ @2 m4) ; m6 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t5) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; t8 = str (sreplicate @_ @2 (sslice m7)) ; m9 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t8)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t10 = str (sreplicate @_ @2 (sslice m7)) ; m11 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t10)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t12 = str (sreplicate @_ @2 m11) ; t13 = str (sreplicate @_ @2 (sslice m7)) ; m14 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t12) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t13)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t15 = str (sreplicate @_ @10 (sslice (sappend m9 m14))) ; m17 = sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (ssum @_ @10 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject2 m1)))) * sreplicate @_ @2 (sfromR m16)))) (sconcrete (sfromListLinear [0,2] []))) ; m18 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m14 * m14) * sslice m17 ; t19 = sreplicate @_ @2 m18 ; t20 = sreplicate @_ @2 m18 ; m21 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m11 * m11) * ssum @_ @2 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t20)) ; t22 = sreplicate @_ @2 m21 ; m23 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m9 * m9) * sslice m17 ; t24 = sreplicate @_ @2 m23 ; m25 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (ssum @_ @2 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t24))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + (sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (ssum @_ @2 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t22))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (ssum @_ @2 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t19))) (sconcrete (sfromListLinear [0,2] [])))) ; m26 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m6 * m6) * sslice m25 ; t27 = sreplicate @_ @2 m26 ; m28 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m4 * m4) * ssum @_ @2 (str (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t27)) ; m29 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m3 * m3) * sslice m25 in tpair (tpair (tpair (tpair (rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) * sreplicate @_ @2 m29)) + (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) * sreplicate @_ @2 m28)) + (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) * sreplicate @_ @2 m23)) + ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) * sreplicate @_ @2 m21))))), rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) * sreplicate @_ @2 m29)) + (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) * sreplicate @_ @2 m28)) + (ssum @_ @2 (stranspose @_ @[2,1,0] (t8 * t24)) + ssum @_ @2 (stranspose @_ @[2,1,0] (t10 * t22)))))), rfromS (ssum @_ @2 (str m29) + (ssum @_ @2 (str m28) + (ssum @_ @2 (str m23) + ssum @_ @2 (str m21))))), tpair (tpair (rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (t5 * t27)) + ssum @_ @2 (stranspose @_ @[2,1,0] (t12 * t20))), rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) * sreplicate @_ @2 m26)) + ssum @_ @2 (stranspose @_ @[2,1,0] (t13 * t19)))), rfromS (ssum @_ @2 (str m26) + ssum @_ @2 (str m18)))), tpair (rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (t15 * sreplicate @_ @2 (sfromR m16)))), rfromS (ssum @_ @2 (str (sfromR m16)))))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 -> let m3 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t5 = str (sreplicate @_ @2 m4) ; m6 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t5) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * str (sreplicate @_ @2 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; t8 = str (sreplicate @_ @2 (sslice m7)) ; m9 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t8)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t10 = str (sreplicate @_ @2 (sslice m7)) ; m11 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1)))))) * str (sreplicate @_ @2 (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))))) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) * t10)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; t12 = str (sreplicate @_ @2 m11) ; t13 = str (sreplicate @_ @2 (sslice m7)) ; m14 = tanh ((ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) * t12) + ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) * t13)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; t15 = str (sreplicate @_ @10 (sslice (sappend m9 m14))) in rfromS (ssum @_ @2 (stranspose @_ @[2,1,0] (sreplicate @_ @2 (sfromR (tproject1 (tproject2 m1)))) * t15) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 m1)))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m16 m1 -> tfromS (let m3 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m4 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m6 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m4 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m7 = sappend m3 m6 ; m9 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m7)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m11 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m7)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m14 = tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) m11 + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m7)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m17 = sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (smatmul2 (str (sfromR (tproject1 (tproject2 m1)))) (sfromR m16)) (sconcrete (sfromListLinear [0,2] []))) ; m18 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m14 * m14) * sslice m17 ; m21 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m11 * m11) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m18 ; m23 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m9 * m9) * sslice m17 ; m25 = sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m23) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + (sappend (sconcrete (sfromListLinear [0,2] [])) (sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1)))))) m21) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + sappend (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) (sappend (smatmul2 (str (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1)))))) m18) (sconcrete (sfromListLinear [0,2] [])))) ; m26 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m6 * m6) * sslice m25 ; m28 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m4 * m4) * smatmul2 (str (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1)))))) m26 ; m29 = (sconcrete (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]) + negate m3 * m3) * sslice m25 in tpair (tpair (tpair (tpair (smatmul2 m29 (str (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) + (smatmul2 m28 (str (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) + (smatmul2 m23 (str (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))) + smatmul2 m21 (str (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0)))))), smatmul2 m29 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + (smatmul2 m28 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + (smatmul2 m23 (str (sslice m7)) + smatmul2 m21 (str (sslice m7))))), ssum @_ @2 (str m29) + (ssum @_ @2 (str m28) + (ssum @_ @2 (str m23) + ssum @_ @2 (str m21)))), tpair (tpair (smatmul2 m26 (str m4) + smatmul2 m18 (str m11), smatmul2 m26 (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])) + smatmul2 m18 (str (sslice m7))), ssum @_ @2 (str m26) + ssum @_ @2 (str m18))), tpair (smatmul2 (sfromR m16) (str m14), ssum @_ @2 (str (sfromR m16)))))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m7 = sappend (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) in smatmul2 (sfromR (tproject1 (tproject2 m1))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject2 (tproject1 m1))))) (tanh ((smatmul2 (sfromR (tproject1 (tproject1 (tproject1 (tproject1 m1))))) (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 7.0))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject1 (tproject1 m1))))) (sslice m7)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject1 (tproject1 m1))))))) + smatmul2 (sfromR (tproject2 (tproject1 (tproject2 (tproject1 m1))))) (sslice m7)) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 (tproject1 m1))))))) + str (sreplicate @_ @2 (sfromR (tproject2 (tproject2 m1)))))"
