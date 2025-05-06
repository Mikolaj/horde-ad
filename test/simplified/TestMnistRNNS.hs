-- | Tests of "MnistRnnShaped2" recurrent neural networks using a few different
-- optimization pipelines.
--
-- Not LSTM.
-- Doesn't train without Adam, regardless of whether mini-batches used. It does
-- train with Adam, but only after very carefully tweaking initialization.
-- This is extremely sensitive to initial parameters, more than to anything
-- else. Probably, gradient is vanishing if parameters are initialized
-- with a probability distribution that doesn't have the right variance. See
-- https://stats.stackexchange.com/questions/301285/what-is-vanishing-gradient.
-- Regularization/normalization might help as well.
module TestMnistRNNS
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import GHC.TypeLits (KnownNat, sameNat)
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Text.Printf

import Data.Array.Nested.Internal.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret

import EqEpsilon

import MnistData
import MnistRnnShaped2 (ADRnnMnistParametersShaped)
import MnistRnnShaped2 qualified

-- TODO: optimize enough that it can run for one full epoch in reasonable time
-- and then verify it trains down to ~20% validation error in a short enough
-- time to include such a training run in tests.

type XParams out_width r =
 X (ADRnnMnistParametersShaped Concrete SizeMnistHeight out_width r)

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTestsRNNSA
            , tensorADValMnistTestsRNNSI
            , tensorADValMnistTestsRNNSO
            ]

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCaseRNNSA
  :: forall width batch_size r.
     (Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r)
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSA prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize expected =
  let targetInit =
        fst $ randomValue @(Concrete (XParams width r)) 0.4 (mkStdGen 44)
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width), show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(XParams width r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: forall batch_size2. KnownNat batch_size2
            => MnistDataBatchS batch_size2 r -> Concrete (XParams width r)
            -> r
      ftest _ _ | Just Refl <- sameNat (Proxy @0) (Proxy @batch_size2) = 0
      ftest mnistData testParams =
        MnistRnnShaped2.rnnMnistTestS
          width (SNat @batch_size2) mnistData (fromTarget @Concrete testParams)
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- map mkMnistDataS
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS @lenTestData testData
           f :: MnistDataBatchS batch_size r
             -> ADVal Concrete (XParams width r)
             -> ADVal Concrete (TKScalar r)
           f (glyphS, labelS) adinputs =
             MnistRnnShaped2.rnnMnistLossFusedS
               width batch_size (sconcrete glyphS, sconcrete labelS)
               (fromTarget @(ADVal Concrete) adinputs)
           runBatch :: ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( Concrete (XParams width r)
                          , StateAdam (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam @(MnistDataBatchS batch_size r)
                               @(XParams width r)
                               f chunkS parameters stateAdam
                 trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 testScore = ftest @lenTestData testDataS parameters2
                 lenChunk = length chunk
             unless (sNatValue width < 10) $ do
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
                    -> ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> IO (Concrete (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
           ftk = tftk @Concrete (knownSTK @(XParams width r))
                      targetInit
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal = 1 - ftest @lenTestData testDataS res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNSA
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSA :: TestTree
tensorADValMnistTestsRNNSA = testGroup "RNNS ADVal MNIST tests"
  [ mnistTestCaseRNNSA "RNNSA 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 5000
                       (0.8846 :: Double)
  , mnistTestCaseRNNSA "RNNSA artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSA "RNNSA artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSA "RNNSA 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCaseRNNSI
  :: forall width batch_size r.
     (Differentiable r, GoodScalar r, PrintfArg r, AssertEqualUpToEpsilon r)
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSI prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize expected =
  let targetInit =
        fst $ randomValue @(Concrete (XParams width r)) 0.4 (mkStdGen 44)
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width), show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(XParams width r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: forall batch_size2. KnownNat batch_size2
            => MnistDataBatchS batch_size2 r -> Concrete (XParams width r)
            -> r
      ftest _ _ | Just Refl <- sameNat (Proxy @0) (Proxy @batch_size2) = 0
      ftest mnistData testParams =
        MnistRnnShaped2.rnnMnistTestS
          width (SNat @batch_size2) mnistData (fromTarget @Concrete testParams)
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- map mkMnistDataS
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS @lenTestData testData
           ftk = tftk @Concrete (knownSTK @(XParams width r)) targetInit
       (_, _, var, varAst) <- funToAstRevIO ftk
       (varGlyph, astGlyph) <- funToAstIO (FTKS knownShS FTKScalar) id
       (varLabel, astLabel) <- funToAstIO (FTKS knownShS FTKScalar) id
       let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
           ast = simplifyInline
                 $ MnistRnnShaped2.rnnMnistLossFusedS
                     width batch_size (astGlyph, astLabel)
                     (fromTarget varAst)
           f :: MnistDataBatchS batch_size r
             -> ADVal Concrete (XParams width r)
             -> ADVal Concrete (TKScalar r)
           f (glyph, label) varInputs =
             let env = extendEnv var varInputs emptyEnv
                 envMnist = extendEnv varGlyph (sconcrete glyph)
                            $ extendEnv varLabel (sconcrete label) env
             in interpretAstFull envMnist ast
           runBatch :: ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( Concrete (XParams width r)
                          , StateAdam (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) =
                   sgdAdam @(MnistDataBatchS batch_size r)
                               @(XParams width r)
                               f chunkS parameters stateAdam
                 trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 testScore = ftest @lenTestData testDataS parameters2
                 lenChunk = length chunk
             unless (sNatValue width < 10) $ do
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
                    -> ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> IO (Concrete (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal = 1 - ftest @lenTestData testDataS res
       testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCaseRNNSI
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSI :: TestTree
tensorADValMnistTestsRNNSI = testGroup "RNNS Intermediate MNIST tests"
  [ mnistTestCaseRNNSI "RNNSI 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 5000
                       (0.8988 :: Double)
  , mnistTestCaseRNNSI "RNNSI artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSI "RNNSI artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.8928571428571429 :: Double)
  , mnistTestCaseRNNSI "RNNSI 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCaseRNNSO
  :: forall width batch_size r.
     ( Differentiable r, GoodScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> r
  -> TestTree
mnistTestCaseRNNSO prefix epochs maxBatches width@SNat batch_size@SNat
                   totalBatchSize expected =
  let targetInit =
        fst $ randomValue @(Concrete (XParams width r)) 0.4 (mkStdGen 44)
      miniBatchSize = sNatValue batch_size
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (sNatValue width), show miniBatchSize
                        , show $ widthSTK
                          $ knownSTK @(XParams width r)
                        , show (tsize knownSTK targetInit) ]
      ftest :: forall batch_size2. KnownNat batch_size2
            => MnistDataBatchS batch_size2 r -> Concrete (XParams width r)
            -> r
      ftest _ _ | Just Refl <- sameNat (Proxy @0) (Proxy @batch_size2) = 0
      ftest mnistData testParams =
        MnistRnnShaped2.rnnMnistTestS
          width (SNat @batch_size2) mnistData (fromTarget @Concrete testParams)
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- map mkMnistDataS
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataS . take (totalBatchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    withSNat (totalBatchSize * maxBatches) $ \(SNat @lenTestData) -> do
       let testDataS = mkMnistDataBatchS @lenTestData testData
           ftk = tftk @Concrete (knownSTK @(XParams width r)) targetInit
           ftkData = FTKProduct (FTKS (batch_size
                                       :$$ sizeMnistHeight
                                       :$$ sizeMnistWidth
                                       :$$ ZSS) FTKScalar)
                                (FTKS (batch_size
                                       :$$ sizeMnistLabel
                                       :$$ ZSS) FTKScalar)
           f :: ( ADRnnMnistParametersShaped (AstTensor AstMethodLet FullSpan)
                    SizeMnistHeight width r
                , ( AstTensor AstMethodLet FullSpan
                      (TKS '[batch_size, SizeMnistHeight, SizeMnistWidth] r)
                  , AstTensor AstMethodLet FullSpan
                      (TKS '[batch_size, SizeMnistLabel] r) ) )
             -> AstTensor AstMethodLet FullSpan (TKScalar r)
           f = \ (pars, (glyphS, labelS)) ->
             MnistRnnShaped2.rnnMnistLossFusedS
               width batch_size (sprimalPart glyphS, sprimalPart labelS) pars
           artRaw = revArtifactAdapt IgnoreIncomingCotangent
                                     f (FTKProduct ftk ftkData)
           art = simplifyArtifactGradient artRaw
           go :: [MnistDataBatchS batch_size r]
              -> ( Concrete (XParams width r)
                 , StateAdam (XParams width r) )
              -> ( Concrete (XParams width r)
                 , StateAdam (XParams width r) )
           go [] (parameters, stateAdam) = (parameters, stateAdam)
           go ((glyph, label) : rest) (!parameters, !stateAdam) =
             let parametersAndInput =
                   tpair parameters (tpair (sconcrete glyph) (sconcrete label))
                 gradient = tproject1 $ fst
                            $ revInterpretArtifact
                                art parametersAndInput Nothing
             in go rest (updateWithGradientAdam
                           @(XParams width r)
                           defaultArgsAdam stateAdam knownSTK parameters
                           gradient)
           runBatch :: ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> (Int, [MnistDataS r])
                    -> IO ( Concrete (XParams width r)
                          , StateAdam (XParams width r) )
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let chunkS = map mkMnistDataBatchS
                          $ filter (\ch -> length ch == miniBatchSize)
                          $ chunksOf miniBatchSize chunk
                 res@(parameters2, _) = go chunkS (parameters, stateAdam)
                 trainScore = withSNat (length chunk) $ \(SNat @len) ->
                   ftest @len (mkMnistDataBatchS chunk) parameters2
                 testScore = ftest @lenTestData testDataS parameters2
                 lenChunk = length chunk
             unless (sNatValue width < 10) $ do
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
                    -> ( Concrete (XParams width r)
                       , StateAdam (XParams width r) )
                    -> IO (Concrete (XParams width r))
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam@(!_, !_) = do
             unless (sNatValue width < 10) $
               hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf totalBatchSize trainDataShuffled
             res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (targetInit, initialStateAdam ftk)
       let testErrorFinal = 1 - ftest @lenTestData testDataS res
       assertEqualUpToEpsilon 1e-1 expected testErrorFinal

{-# SPECIALIZE mnistTestCaseRNNSO
  :: String
  -> Int -> Int -> SNat width -> SNat batch_size -> Int -> Double
  -> TestTree #-}

tensorADValMnistTestsRNNSO :: TestTree
tensorADValMnistTestsRNNSO = testGroup "RNNS Once MNIST tests"
  [ mnistTestCaseRNNSO "RNNSO 1 epoch, 1 batch" 1 1 (SNat @128) (SNat @5) 5000
                       (0.84 :: Double)
  , mnistTestCaseRNNSO "RNNSO artificial 1 2 3 4 5" 2 3 (SNat @4) (SNat @5) 50
                       (0.8933333 :: Float)
  , mnistTestCaseRNNSO "RNNSO artificial 5 4 3 2 1" 5 4 (SNat @3) (SNat @2) 49
                       (0.9336734693877551 :: Double)
  , mnistTestCaseRNNSO "RNNSO 1 epoch, 0 batch" 1 0 (SNat @128) (SNat @5) 50
                       (1.0 :: Float)
  ]
