{-# LANGUAGE OverloadedLists #-}
-- | Tests of "MnistFcnnRanked1" and "MnistFcnnRanked2" neural networks
-- using a few different optimization pipelines.
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.IntMap.Strict qualified as IM
import GHC.Exts (IsList (..))
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)
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
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ tensorADValMnistTests
            , tensorIntermediateMnistTests
            , tensorADOnceMnistTests
            , tensorADValMnistTests2
            , tensorIntermediateMnistTests2
            , tensorADOnceMnistTests2
            , tensorMnistTestsPP
            ]


-- * Using lists of vectors, which is rank 1

type XParams widthHidden widthHidden2 r =
  X (MnistFcnnRanked1.ADFcnnMnist1Parameters RepN widthHidden widthHidden2 r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase1VTA
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r, ADTensorScalar r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTA prefix epochs maxBatches widthHiddenInt widthHidden2Int
                  gamma batchSize expected =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ twidth @RepN
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 RepN widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let f :: MnistDataLinearR r
          -> ADVal RepN (XParams widthHidden widthHidden2 r)
          -> ADVal RepN (TKScalar r)
        f (glyph, label) adinputs =
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
    -- Mimic how backprop tests and display it, even though tests
    -- should not print, in principle.
    let runBatch :: RepN (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runBatch !params (k, chunk) = do
          let res = fst $ sgd gamma f chunk params
              trainScore = ftest chunk (fromTarget res)
              testScore = ftest testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHiddenInt < 10) $ do
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
                 -> RepN (XParams widthHidden widthHidden2 r)
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHiddenInt < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal = 1 - ftest testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTA
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests :: TestTree
tensorADValMnistTests = testGroup "Ranked ADVal MNIST tests"
  [ mnistTestCase1VTA "VTA1 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.19499999999999995 :: Double)
  , mnistTestCase1VTA "VTA1 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase1VTA "VTA1 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase1VTI
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r, ADTensorScalar r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTI prefix epochs maxBatches widthHiddenInt widthHidden2Int
                  gamma batchSize expected =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
      ftk = tftk @RepN (knownSTK @(XParams widthHidden widthHidden2 r))
                       targetInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ twidth @RepN
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 RepN widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    (_, _, var, varAst) <- funToAstRevIO ftk
    (varGlyph, astGlyph) <-
      funToAstIO (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar) id
    (varLabel, astLabel) <-
      funToAstIO (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar) id
    let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
        ast = MnistFcnnRanked1.afcnnMnistLoss1
                widthHiddenSNat widthHidden2SNat (astGlyph, astLabel)
                (fromTarget varAst)
        f :: MnistDataLinearR r
          -> ADVal RepN (XParams widthHidden widthHidden2 r)
          -> ADVal RepN (TKScalar r)
        f (glyph, label) varInputs =
          let env = extendEnv var varInputs emptyEnv
              envMnist = extendEnv varGlyph (rconcrete glyph)
                         $ extendEnv varLabel (rconcrete label) env
          in interpretAst envMnist ast
    let runBatch :: RepN (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runBatch !params (k, chunk) = do
          let res = fst $ sgd gamma f chunk params
              trainScore = ftest chunk (fromTarget res)
              testScore = ftest testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHiddenInt < 10) $ do
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
                 -> RepN (XParams widthHidden widthHidden2 r)
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHiddenInt < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal = 1 - ftest testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTI
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests :: TestTree
tensorIntermediateMnistTests = testGroup "Ranked Intermediate MNIST tests"
  [ mnistTestCase1VTI "VTI1 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.19740000000000002 :: Double)
  , mnistTestCase1VTI "VTI1 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase1VTI "VTI1 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase1VTO
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r, ADTensorScalar r ~ r
     , PrintfArg r, AssertEqualUpToEpsilon r)
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTO prefix epochs maxBatches widthHiddenInt widthHidden2Int
                  gamma batchSize expected =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    RepN widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: RepN (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @RepN valsInit
      ftk = tftk @RepN (knownSTK @(XParams widthHidden widthHidden2 r))
                       targetInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ twidth @RepN
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 RepN widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let ftkData = FTKProduct (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar)
                             (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar)
        f :: ( MnistFcnnRanked1.ADFcnnMnist1Parameters
                 (AstTensor AstMethodLet FullSpan)
                 widthHidden widthHidden2 r
             , ( AstTensor AstMethodLet FullSpan (TKR 1 r)
               , AstTensor AstMethodLet FullSpan (TKR 1 r) ) )
          -> AstTensor AstMethodLet FullSpan (TKScalar r)
        f = \ (pars, (glyphR, labelR)) ->
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            (glyphR, labelR) pars
        (artRaw, _) = revArtifactAdapt False f (FTKProduct ftk ftkData)
        art = simplifyArtifactGradient artRaw
        go :: [MnistDataLinearR r]
           -> RepN (XParams widthHidden widthHidden2 r)
           -> RepN (XParams widthHidden widthHidden2 r)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ fst
                         $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradient)
    let runBatch :: RepN (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runBatch !params (k, chunk) = do
          let res = go chunk params
              trainScore = ftest chunk (fromTarget res)
              testScore = ftest testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHiddenInt < 10) $ do
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
                 -> RepN (XParams widthHidden widthHidden2 r)
                 -> IO (RepN (XParams widthHidden widthHidden2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHiddenInt < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal = 1 - ftest testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase1VTO
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests :: TestTree
tensorADOnceMnistTests = testGroup "Ranked Once MNIST tests"
  [ mnistTestCase1VTO "VTO1 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                      (0.19740000000000002 :: Double)
  , mnistTestCase1VTO "VTO1 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.9108 :: Float)
  , mnistTestCase1VTO "VTO1 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]


-- * Using matrices, which is rank 2

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase2VTA
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      1 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ twidth @RepN $ knownSTK @(XParams2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let f :: MnistDataLinearR r -> ADVal RepN (XParams2 r)
          -> ADVal RepN (TKScalar r)
        f (glyph, label) adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
    let runBatch :: RepN (XParams2 r) -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams2 r))
        runBatch !params (k, chunk) = do
          let res = fst $ sgd gamma f chunk params
              trainScore =
                MnistFcnnRanked2.afcnnMnistTest2 chunk (fromTarget res)
              testScore =
                MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHidden < 10) $ do
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
    let runEpoch :: Int -> RepN (XParams2 r) -> IO (RepN (XParams2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHidden < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal =
          1 - MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTA
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADValMnistTests2 :: TestTree
tensorADValMnistTests2 = testGroup "Ranked2 ADVal MNIST tests"
  [ mnistTestCase2VTA "VTA2 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.536 :: Double)
  , mnistTestCase2VTA "VTA2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.89 :: Float)
  , mnistTestCase2VTA "VTA2 artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.8145:: Double)
  , mnistTestCase2VTA "VTA2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase2VTI
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                                   RepN widthHidden widthHidden2 r)))
                      1 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ twidth @RepN $ knownSTK @(XParams2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let ftk = tftk @RepN (knownSTK @(XParams2 r)) targetInit
    (_, _, var, varAst) <- funToAstRevIO ftk
    (varGlyph, astGlyph) <-
      funToAstIO (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar) id
    (varLabel, astLabel) <-
      funToAstIO (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar) id
    let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
        ast = MnistFcnnRanked2.afcnnMnistLoss2
                (astGlyph, astLabel)
                (fromTarget varAst)
        f :: MnistDataLinearR r -> ADVal RepN (XParams2 r)
          -> ADVal RepN (TKScalar r)
        f (glyph, label) varInputs =
          let env = extendEnv var varInputs emptyEnv
              envMnist = extendEnv varGlyph (rconcrete glyph)
                         $ extendEnv varLabel (rconcrete label) env
          in interpretAst envMnist ast
    let runBatch :: RepN (XParams2 r) -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams2 r))
        runBatch !params (k, chunk) = do
          let res = fst $ sgd gamma f chunk params
              trainScore =
                MnistFcnnRanked2.afcnnMnistTest2 chunk (fromTarget res)
              testScore =
                MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHidden < 10) $ do
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
    let runEpoch :: Int -> RepN (XParams2 r) -> IO (RepN (XParams2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHidden < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal =
          1 - MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTI
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorIntermediateMnistTests2 :: TestTree
tensorIntermediateMnistTests2 = testGroup "Ranked2 Intermediate MNIST tests"
  [ mnistTestCase2VTI "VTI2 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VTI "VTI2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VTI "VTI2 artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.8195 :: Double)
  , mnistTestCase2VTI "VTI2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase2VTO
  :: forall r.
     ( Differentiable r, GoodScalar r, Random r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let (!targetInit, !artRaw) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradient
          1 (mkStdGen 44) widthHidden widthHidden2
      !art = simplifyArtifactGradient artRaw
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ twidth @RepN $ knownSTK @(XParams2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let go :: [MnistDataLinearR r] -> RepN (XParams2 r) -> RepN (XParams2 r)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ fst
                         $ revEvalArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma parameters gradient)
    let runBatch :: RepN (XParams2 r) -> (Int, [MnistDataLinearR r])
                 -> IO (RepN (XParams2 r))
        runBatch !params (k, chunk) = do
          let res = go chunk params
              trainScore =
                MnistFcnnRanked2.afcnnMnistTest2 chunk (fromTarget res)
              testScore =
                MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
              lenChunk = length chunk
          unless (widthHidden < 10) $ do
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
    let runEpoch :: Int -> RepN (XParams2 r) -> IO (RepN (XParams2 r))
        runEpoch n params | n > epochs = return params
        runEpoch n !params = do
          unless (widthHidden < 10) $
            hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 1) trainData
              chunks = take maxBatches
                       $ zip [1 ..] $ chunksOf batchSize
                       $ map mkMnistDataLinearR trainDataShuffled
          res <- foldM runBatch params chunks
          runEpoch (succ n) res
    res <- runEpoch 1 targetInit
    let testErrorFinal =
          1 - MnistFcnnRanked2.afcnnMnistTest2 testData (fromTarget res)
    testErrorFinal @?~ expected

{-# SPECIALIZE mnistTestCase2VTO
  :: String
  -> Int -> Int -> Int -> Int -> Double -> Int -> Double
  -> TestTree #-}

tensorADOnceMnistTests2 :: TestTree
tensorADOnceMnistTests2 = testGroup "Ranked2 Once MNIST tests"
  [ mnistTestCase2VTO "VTO2 1 epoch, 1 batch" 1 1 300 100 0.02 500
                       (0.534 :: Double)
  , mnistTestCase2VTO "VTO2 artificial 1 2 3 4 5" 1 2 3 4 5 500
                       (0.884 :: Float)
  , mnistTestCase2VTO "VTO2 artificial 5 4 3 2 1" 5 4 3 2 1 500
                       (0.6739999999999999 :: Double)
  , mnistTestCase2VTO "VTO2 1 epoch, 0 batch" 1 0 300 100 0.02 500
                       (1 :: Float)
  , testProperty "VTO2 rev vs fwd" $
    \seed0 ->
    forAllShrink (chooseInt (0, 600)) shrinkIntegral $ \width1Hidden ->
    forAllShrink (chooseInt (0, 200)) shrinkIntegral $ \width1Hidden2 ->
    forAllShrink (chooseInt (0, 5)) shrinkIntegral $ \simp ->
    forAll (choose (0.01, 1)) $ \range ->
    forAll (choose (0.01, 1)) $ \range2 ->
    forAll (choose (1 - 1e-7, 1 + 1e-7)) $ \dt ->  -- TODO: "Gradient and derivative agrees" fails for more varied dt, while ds can vary a lot (though it averages out)); also the two occurences of dt amplify the difference instead of counteracting
    forAll (choose (0, 1e-7)) $ \(perturbation :: Double) ->
    withSNat (1 + width1Hidden) $ \(SNat @widthHidden) ->
    withSNat (1 + width1Hidden2) $ \(SNat @widthHidden2) ->
    let (glyph0, seed2) = randomValue @(RepN (TKS '[SizeMnistGlyph] Double))
                                      0.5 (mkStdGen seed0)
        (label0, seed3) = randomValue @(RepN (TKS '[SizeMnistLabel] Double))
                                      5 seed2
        (glyph, label) = ( rmap1 (rscalar 0.5 +) $ forgetShape glyph0
                         , rmap1 (rscalar 5 + ) $ forgetShape label0 )
        ds :: RepN (XParams2 Double)
        (ds, seed4) = first forgetShape $
          randomValue
            @(RepN (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                         RepN widthHidden widthHidden2 Double)))
            range seed3
        (targetInit, artRaw) =
          MnistFcnnRanked2.mnistTrainBench2VTOGradient
            range2 seed4 (1 + width1Hidden) (1 + width1Hidden2)
        art = iterate simplifyArtifactGradient artRaw !! simp
        stk = knownSTK @(XParams2 Double)
        ftk = tftk @RepN stk targetInit
        parametersAndInput = tpair targetInit (tpair glyph label)
        (gradient1, value1) =
          revEvalArtifact art parametersAndInput (Just $ kconcrete dt)
        f :: ADVal RepN (XParams2 Double) -> ADVal RepN (TKScalar Double)
        f adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rfromPrimal glyph, rfromPrimal label) (fromTarget adinputs)
        (derivative2, value2) = cfwdBoth f targetInit ds
        goodPerturbation :: forall r. GoodScalar r => r
        goodPerturbation = ifDifferentiable @r (realToFrac perturbation) 0
        targetPerturbed :: RepN (XParams2 Double)
        targetPerturbed = constantTarget goodPerturbation ftk
        targetInitPerturbed :: RepN (XParams2 Double)
        targetInitPerturbed = addTarget stk targetInit targetPerturbed
        (derivative3, value3) = cfwdBoth f targetInit targetPerturbed
        value4 :: RepN (TKScalar Double)
        value4 = MnistFcnnRanked2.afcnnMnistLoss2
                   (rfromPrimal glyph, rfromPrimal label)
                   (fromTarget targetInitPerturbed)
    in
      conjoin  -- if not for the Float in ADFcnnMnist2Parameters 1e-7 would work
        [ counterexample
            ("Objective function value from rev and fwd matches: "
             ++ show (value1, value2, value1 - value2))
            (abs (value1 - value2) < 1e-3)
        , counterexample
            ("Gradient and derivative agrees: "
             ++ show ( dt, derivative2, dotTarget stk (tproject1 gradient1) ds
                     , kconcrete dt * derivative2
                       - dotTarget stk (tproject1 gradient1) ds ))
            (abs (kconcrete dt * derivative2
                  - dotTarget stk (tproject1 gradient1) ds) < 1e-1)
        , counterexample
            "Objective function value unaffected by derivative perturbation"
            (value2 === value3)
        , counterexample
            ("Derivative approximates the perturbation of value: "
             ++ show ( value2, derivative3, value4
                     , (value3 + derivative3) - value4) )
            (abs ((value3 + derivative3) - value4) < 1e-3)
        ]
  ]


-- * Tests with pretty-printed resulting gradient expressions

tensorMnistTestsPP :: TestTree
tensorMnistTestsPP = testGroup "PP tests for Short Ranked MNIST tests"
  [ testCase "VTO1 PP Lin" testVTOPP
  , testCase "VTO1 PP NonLin" testVTOPPNonLin
  , testCase "VTO2 PP Lin" testVT2OPP
  , testCase "VTO2 PP NonLin" testVT2OPPNonLin
  , testCase "VTO2 PP NonLin2" testVT2OPPNonLin2
  , testCase "VTO2 PP NonLin3" testVT2OPPNonLin3
  ]

valsInitVTOPP :: MnistFcnnRanked1.ADFcnnMnist1Parameters RepN 3 4 Double
valsInitVTOPP =
  ( ( fromList (replicate 3 (RepN $ Nested.sfromList1Prim
                                      (SNat @SizeMnistGlyph)
                                      [1 .. fromIntegral sizeMnistGlyphInt]))
    , RepN $ Nested.sfromList1Prim (SNat @3) [1, 2, 3] )
  , ( fromList (replicate 4 (RepN $ Nested.sfromList1Prim
                                      (SNat @3) [1, 2, 3]))
    , RepN $ Nested.sfromList1Prim (SNat @4) [1, 2, 3, 4] )
  , ( fromList (replicate sizeMnistLabelInt (RepN $ Nested.sfromList1Prim
                                                      (SNat @4) [1, 2, 3, 4]))
    , RepN $ Nested.sfromList1Prim (SNat @SizeMnistLabel)
                                   [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ) )

testVTOPP :: Assertion
testVTOPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      afcnn2T :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                   (AstTensor AstMethodLet FullSpan) 3 4 Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T =
        MnistFcnnRanked1.afcnnMnist1 id id
                                     (SNat @3) (SNat @4) (sfromR blackGlyph)
      ftk = tftk @RepN (knownSTK @(XParams 3 4 Double))
                       (toTarget @RepN valsInitVTOPP)
      (artifactRev, _) = revArtifactAdapt True afcnn2T ftk
  printArtifactPretty renames artifactRev
    @?= "\\v6 v1 -> let v4 = sfromVector (fromList [ssum @_ @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @_ @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @_ @4 (sfromR v6 !$ [9]) ; v8 = sreplicate @_ @4 (sfromR v6 !$ [8]) ; v9 = sreplicate @_ @4 (sfromR v6 !$ [7]) ; v10 = sreplicate @_ @4 (sfromR v6 !$ [6]) ; v11 = sreplicate @_ @4 (sfromR v6 !$ [5]) ; v12 = sreplicate @_ @4 (sfromR v6 !$ [4]) ; v13 = sreplicate @_ @4 (sfromR v6 !$ [3]) ; v14 = sreplicate @_ @4 (sfromR v6 !$ [2]) ; v15 = sreplicate @_ @4 (sfromR v6 !$ [1]) ; v16 = sreplicate @_ @4 (sfromR v6 !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7 ; v18 = sreplicate @_ @3 (v17 !$ [3]) ; v19 = sreplicate @_ @3 (v17 !$ [2]) ; v20 = sreplicate @_ @3 (v17 !$ [1]) ; v21 = sreplicate @_ @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18 in tpair (tpair (tpair (tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [0]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [1]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [2]), Z0))), v22), tpair (tpair (v4 * v21, tpair (v4 * v20, tpair (v4 * v19, tpair (v4 * v18, Z0)))), v17)), tpair (tpair (v5 * v16, tpair (v5 * v15, tpair (v5 * v14, tpair (v5 * v13, tpair (v5 * v12, tpair (v5 * v11, tpair (v5 * v10, tpair (v5 * v9, tpair (v5 * v8, tpair (v5 * v7, Z0)))))))))), sfromR v6))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v1 -> let v4 = sfromVector (fromList [ssum @_ @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [ssum @_ @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v4), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v4)]) + tproject2 (tproject2 (tproject1 v1)) in rfromS (sfromVector (fromList [ssum @_ @4 (tproject1 (tproject1 (tproject2 v1)) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v5), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v5)]) + tproject2 (tproject2 v1))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v6 v1 -> let v4 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) ; v7 = sreplicate @_ @4 (sfromR v6 !$ [9]) ; v8 = sreplicate @_ @4 (sfromR v6 !$ [8]) ; v9 = sreplicate @_ @4 (sfromR v6 !$ [7]) ; v10 = sreplicate @_ @4 (sfromR v6 !$ [6]) ; v11 = sreplicate @_ @4 (sfromR v6 !$ [5]) ; v12 = sreplicate @_ @4 (sfromR v6 !$ [4]) ; v13 = sreplicate @_ @4 (sfromR v6 !$ [3]) ; v14 = sreplicate @_ @4 (sfromR v6 !$ [2]) ; v15 = sreplicate @_ @4 (sfromR v6 !$ [1]) ; v16 = sreplicate @_ @4 (sfromR v6 !$ [0]) ; v17 = tproject1 (tproject1 (tproject2 v1)) * v16 + tproject1 (tproject2 (tproject1 (tproject2 v1))) * v15 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v14 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v13 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v12 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v11 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v10 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v9 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v8 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v7 ; v18 = sreplicate @_ @3 (v17 !$ [3]) ; v19 = sreplicate @_ @3 (v17 !$ [2]) ; v20 = sreplicate @_ @3 (v17 !$ [1]) ; v21 = sreplicate @_ @3 (v17 !$ [0]) ; v22 = tproject1 (tproject1 (tproject2 (tproject1 v1))) * v21 + tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v20 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v18 in tpair (tpair (tpair (tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [0]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [1]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v22 !$ [2]), Z0))), v22), tpair (tpair (v4 * v21, tpair (v4 * v20, tpair (v4 * v19, tpair (v4 * v18, Z0)))), v17)), tpair (tpair (v5 * v16, tpair (v5 * v15, tpair (v5 * v14, tpair (v5 * v13, tpair (v5 * v12, tpair (v5 * v11, tpair (v5 * v10, tpair (v5 * v9, tpair (v5 * v8, tpair (v5 * v7, Z0)))))))))), sfromR v6))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v5 = sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v4, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v4, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v4]) + tproject2 (tproject2 (tproject1 v1)) in sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v5, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v5, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v5]) + tproject2 (tproject2 v1))"

testVTOPPNonLin :: Assertion
testVTOPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @SizeMnistGlyph) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                         (AstTensor AstMethodLet FullSpan) 3 4 Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin =
        MnistFcnnRanked1.afcnnMnist1 logisticS softMax1S
                                     (SNat @3) (SNat @4) (sfromR blackGlyph)
      ftk = tftk @RepN (knownSTK @(XParams 3 4 Double))
                       (toTarget @RepN valsInitVTOPP)
      (artifactRevnonLin, _) = revArtifactAdapt True afcnn2TnonLin ftk
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v32 v1 -> let v11 = sfromVector (fromList [ssum @_ @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v12 = exp (negate v11) ; v13 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + v12 ; v14 = recip v13 ; v15 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) - v14 ; v16 = v14 * v15 ; v18 = sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) ; v19 = v14 + v18 ; v20 = sfromVector (fromList [ssum @_ @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v19)]) + tproject2 (tproject2 (tproject1 v1)) ; v21 = exp (negate v20) ; v22 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v21 ; v23 = recip v22 ; v24 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) - v23 ; v25 = v23 * v24 ; v27 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; v28 = v23 + v27 ; v29 = exp (sfromVector (fromList [ssum @_ @4 (tproject1 (tproject1 (tproject2 v1)) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v28)]) + tproject2 (tproject2 v1)) ; x30 = ssum @_ @10 v29 ; v31 = sreplicate @_ @10 (recip x30) ; v33 = v29 * (sreplicate @_ @10 (negate (recip (x30 * x30)) * ssum @_ @10 (v29 * sfromR v32)) + v31 * sfromR v32) ; v34 = sreplicate @_ @4 (v33 !$ [9]) ; v35 = sreplicate @_ @4 (v33 !$ [8]) ; v36 = sreplicate @_ @4 (v33 !$ [7]) ; v37 = sreplicate @_ @4 (v33 !$ [6]) ; v38 = sreplicate @_ @4 (v33 !$ [5]) ; v39 = sreplicate @_ @4 (v33 !$ [4]) ; v40 = sreplicate @_ @4 (v33 !$ [3]) ; v41 = sreplicate @_ @4 (v33 !$ [2]) ; v42 = sreplicate @_ @4 (v33 !$ [1]) ; v43 = sreplicate @_ @4 (v33 !$ [0]) ; v44 = v25 * (tproject1 (tproject1 (tproject2 v1)) * v43 + tproject1 (tproject2 (tproject1 (tproject2 v1))) * v42 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v39 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v38 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v37 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v36 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v35 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v34) ; v45 = sreplicate @_ @3 (v44 !$ [3]) ; v46 = sreplicate @_ @3 (v44 !$ [2]) ; v47 = sreplicate @_ @3 (v44 !$ [1]) ; v48 = sreplicate @_ @3 (v44 !$ [0]) ; v49 = v16 * (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v48 + tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v47 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v46 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v45) in tpair (tpair (tpair (tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [0]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [1]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [2]), Z0))), v49), tpair (tpair (v19 * v48, tpair (v19 * v47, tpair (v19 * v46, tpair (v19 * v45, Z0)))), v44)), tpair (tpair (v28 * v43, tpair (v28 * v42, tpair (v28 * v41, tpair (v28 * v40, tpair (v28 * v39, tpair (v28 * v38, tpair (v28 * v37, tpair (v28 * v36, tpair (v28 * v35, tpair (v28 * v34, Z0)))))))))), v33))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\v1 -> let v11 = sfromVector (fromList [ssum @_ @784 (tproject1 (tproject1 (tproject1 (tproject1 v1))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1)))) * sreplicate @_ @784 (sscalar 7.0)), ssum @_ @784 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) * sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1)) ; v12 = exp (negate v11) ; v13 = sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + v12 ; v14 = recip v13 ; v18 = sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) ; v19 = v14 + v18 ; v20 = sfromVector (fromList [ssum @_ @3 (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v19), ssum @_ @3 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v19)]) + tproject2 (tproject2 (tproject1 v1)) ; v21 = exp (negate v20) ; v22 = sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + v21 ; v23 = recip v22 ; v27 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; v28 = v23 + v27 ; v29 = exp (sfromVector (fromList [ssum @_ @4 (tproject1 (tproject1 (tproject2 v1)) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject1 (tproject2 v1))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v28), ssum @_ @4 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v28)]) + tproject2 (tproject2 v1)) ; x30 = ssum @_ @10 v29 ; v31 = sreplicate @_ @10 (recip x30) in rfromS (v31 * v29)"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v32 v1 -> let v14 = recip (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1))))) ; v19 = sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + v14 ; v23 = recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v19]) + tproject2 (tproject2 (tproject1 v1))))) ; v28 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v23 ; v29 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v28, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v28]) + tproject2 (tproject2 v1)) ; x30 = ssum @_ @10 v29 ; v33 = v29 * (sreplicate @_ @10 (negate (recip (x30 * x30)) * sdot0 v29 (sfromR v32)) + sreplicate @_ @10 (recip x30) * sfromR v32) ; v34 = sreplicate @_ @4 (v33 !$ [9]) ; v35 = sreplicate @_ @4 (v33 !$ [8]) ; v36 = sreplicate @_ @4 (v33 !$ [7]) ; v37 = sreplicate @_ @4 (v33 !$ [6]) ; v38 = sreplicate @_ @4 (v33 !$ [5]) ; v39 = sreplicate @_ @4 (v33 !$ [4]) ; v40 = sreplicate @_ @4 (v33 !$ [3]) ; v41 = sreplicate @_ @4 (v33 !$ [2]) ; v42 = sreplicate @_ @4 (v33 !$ [1]) ; v43 = sreplicate @_ @4 (v33 !$ [0]) ; v44 = (v23 * (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) - v23)) * (tproject1 (tproject1 (tproject2 v1)) * v43 + tproject1 (tproject2 (tproject1 (tproject2 v1))) * v42 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1)))) * v41 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) * v40 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) * v39 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) * v38 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) * v37 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) * v36 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) * v35 + tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) * v34) ; v45 = sreplicate @_ @3 (v44 !$ [3]) ; v46 = sreplicate @_ @3 (v44 !$ [2]) ; v47 = sreplicate @_ @3 (v44 !$ [1]) ; v48 = sreplicate @_ @3 (v44 !$ [0]) ; v49 = (v14 * (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) - v14)) * (tproject1 (tproject1 (tproject2 (tproject1 v1))) * v48 + tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1)))) * v47 + tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) * v46 + tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) * v45) in tpair (tpair (tpair (tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [0]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [1]), tpair (sreplicate @_ @784 (sscalar 7.0) * sreplicate @_ @784 (v49 !$ [2]), Z0))), v49), tpair (tpair (v19 * v48, tpair (v19 * v47, tpair (v19 * v46, tpair (v19 * v45, Z0)))), v44)), tpair (tpair (v28 * v43, tpair (v28 * v42, tpair (v28 * v41, tpair (v28 * v40, tpair (v28 * v39, tpair (v28 * v38, tpair (v28 * v37, tpair (v28 * v36, tpair (v28 * v35, tpair (v28 * v34, Z0)))))))))), v33))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v1 -> rfromS (let v19 = sconcrete (sfromListLinear [3] [0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [3] [1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject1 (tproject1 v1)))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject1 (tproject1 (tproject1 v1))))) (sreplicate @_ @784 (sscalar 7.0)), sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject1 (tproject1 v1)))))) (sreplicate @_ @784 (sscalar 7.0))]) + tproject2 (tproject1 (tproject1 v1))))) ; v28 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sconcrete (sfromListLinear [4] [1.0,1.0,1.0,1.0]) + exp (negate (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 (tproject1 v1)))) v19, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 (tproject1 v1))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1)))))) v19, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 v1))))))) v19]) + tproject2 (tproject2 (tproject1 v1))))) ; v29 = exp (sfromVector (fromList [sdot0 (tproject1 (tproject1 (tproject2 v1))) v28, sdot0 (tproject1 (tproject2 (tproject1 (tproject2 v1)))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject1 (tproject2 v1))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1))))))))))) v28, sdot0 (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 (tproject2 v1)))))))))))) v28]) + tproject2 (tproject2 v1)) in sreplicate @_ @10 (recip (ssum @_ @10 v29)) * v29)"

valsInitVT2OPP :: MnistFcnnRanked2.ADFcnnMnist2Parameters RepN Double
valsInitVT2OPP =
  ( ( RepN $ Nested.rfromListPrimLinear [4, 3]
               (concat $ replicate 4 [1, 2, 3])
    , RepN $ Nested.rfromListPrimLinear [4] [1, 2, 3, 4] )
  , ( RepN $ Nested.rfromListPrimLinear [5, 4]
               (concat $ replicate 5 [1, 2, 3, 4])
    , RepN $ Nested.rfromListPrimLinear [5] [1, 2, 3, 4, 5] )
  , ( RepN $ Nested.rfromListPrimLinear [2, 5]
               (concat $ replicate 2 [1, 2, 3, 4, 5])
    , RepN $ Nested.rfromListPrimLinear [2] [1, 2] ) )

testVT2OPP :: Assertion
testVT2OPP = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      afcnn2T :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                   (AstTensor AstMethodLet FullSpan) Double
              -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2T = MnistFcnnRanked2.afcnnMnist2 id id blackGlyph
      ftk = tftk @RepN (knownSTK @(XParams2 Double))
                       (toTarget @RepN valsInitVT2OPP)
      (artifactRev, _) = revArtifactAdapt True afcnn2T ftk
  printArtifactPretty renames artifactRev
    @?= "\\v5 m1 -> let m2 = str (sreplicate @_ @5 (ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m3 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; m4 = str (sreplicate @_ @2 (ssum @_ @4 (m2 * m3) + sfromR (tproject2 (tproject2 (tproject1 m1))))) ; v6 = ssum @_ @2 (str (str (sfromR (tproject1 (tproject2 m1))) * sreplicate @_ @5 (sfromR v5))) ; m7 = sreplicate @_ @4 v6 ; v8 = ssum @_ @5 (str (m3 * m7)) in tpair (tpair (tpair (rfromS (str (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * sreplicate @_ @3 v8)), rfromS v8), tpair (rfromS (scast (str (m2 * m7))), rfromS v6)), tpair (rfromS (str (m4 * sreplicate @_ @5 (sfromR v5))), rfromS (sfromR v5)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m1 -> let m2 = str (sreplicate @_ @5 (ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m3 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; m4 = str (sreplicate @_ @2 (ssum @_ @4 (m2 * m3) + sfromR (tproject2 (tproject2 (tproject1 m1))))) in rfromS (ssum @_ @5 (m4 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v5 m1 -> tfromS (let m2 = str (sreplicate @_ @5 (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1))))) ; m3 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v6 = smatvecmul (str (sfromR (tproject1 (tproject2 m1)))) (sfromR v5) ; v8 = smatvecmul m3 v6 in tpair (tpair (tpair (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)) * str (sreplicate @_ @3 v8), v8), tpair (str (scast m2) * str (sreplicate @_ @4 (scast v6)), v6)), tpair (sreplicate @_ @2 (ssum @_ @4 (m2 * m3) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @_ @5 (sfromR v5)), v5)))"
  printArtifactSimple renames (simplifyArtifact artifactRev)
    @?= "\\v5 m1 -> tfromS (tlet (str (sreplicate @_ @5 (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) (\\m2 -> tlet (str (scast (sfromR (tproject1 (tproject2 (tproject1 m1)))))) (\\m3 -> tlet (smatvecmul (str (sfromR (tproject1 (tproject2 m1)))) (sfromR v5)) (\\v6 -> tlet (smatvecmul m3 v6) (\\v8 -> tpair (tpair (tpair (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)) * str (sreplicate @_ @3 v8), v8), tpair (str (scast m2) * str (sreplicate @_ @4 (scast v6)), v6)), tpair (sreplicate @_ @2 (ssum @_ @4 (m2 * m3) + sfromR (tproject2 (tproject2 (tproject1 m1)))) * str (sreplicate @_ @5 (sfromR v5)), v5)))))))"

testVT2OPPNonLin :: Assertion
testVT2OPPNonLin = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Float
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Float)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      constant =
        let ((a1, a2), (a3, a4), (a5, a6)) = valsInitVT2OPP
        in ( ( rcast $ fromPrimal $ tconcrete (FTKR [4, 3] FTKScalar) a1
             , rcast $ fromPrimal $ tconcrete (FTKR [4] FTKScalar) a2 )
           , ( fromPrimal $ rcast $ tconcrete (FTKR [5, 4] FTKScalar) a3
             , fromPrimal $ rcast $ tconcrete (FTKR [5] FTKScalar) a4 )
           , ( rcast $ fromPrimal $ tconcrete (FTKR [2, 5] FTKScalar) a5
             , fromPrimal $ rcast $ tconcrete (FTKR [2] FTKScalar) a6 ) )
      (_, ast3) = funToAst (FTKR (0 :$: ZSR) (FTKScalar @Float))
                           (const $ afcnn2TnonLin constant)
  "\\dummy" ++ " -> " ++ printAstSimple renames ast3
    @?= "\\dummy -> rfromS (tlet (exp (ssum @_ @5 (str (sreplicate @_ @2 (tlet (ssum @_ @4 (str (sreplicate @_ @5 (tlet (ssum @_ @3 (tfromPrimal (STKS [3,4] STKScalar) (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)))) * tfromPrimal (STKS [3,4] STKScalar) (tconcrete (FTKS [3,4] FTKScalar) (sfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + tfromPrimal (STKS [4] STKScalar) (tconcrete (FTKS [4] FTKScalar) (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v2 -> tlet (tfromPrimal (STKS [4] STKScalar) (recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (sfromR (tprimalPart (rfromS v2))))))) (\\v3 -> tlet (tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (sfromR (tprimalPart (rfromS v3)) * (sreplicate @_ @4 (sscalar 1.0) - sfromR (tprimalPart (rfromS v3))))) * tdualPart (STKS [4] STKScalar) (sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v2)))))) (\\v4 -> sfromR (tfromPrimal (STKR (SNat @1) STKScalar) (tprimalPart (rfromS v3))) + v4))))) * tfromPrimal (STKS [4,5] STKScalar) (tconcrete (FTKS [4,5] FTKScalar) (sfromListLinear [4,5] [1.0,1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,4.0]))) + tfromPrimal (STKS [5] STKScalar) (tconcrete (FTKS [5] FTKScalar) (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v5 -> tlet (tfromPrimal (STKS [5] STKScalar) (recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (sfromR (tprimalPart (rfromS v5))))))) (\\v6 -> tlet (tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (sfromR (tprimalPart (rfromS v6)) * (sreplicate @_ @5 (sscalar 1.0) - sfromR (tprimalPart (rfromS v6))))) * tdualPart (STKS [5] STKScalar) (sfromR (tfromDual (tdualPart (STKR (SNat @1) STKScalar) (rfromS v5)))))) (\\v7 -> sfromR (tfromPrimal (STKR (SNat @1) STKScalar) (tprimalPart (rfromS v6))) + v7))))) * tfromPrimal (STKS [5,2] STKScalar) (tconcrete (FTKS [5,2] FTKScalar) (sfromListLinear [5,2] [1.0,1.0,2.0,2.0,3.0,3.0,4.0,4.0,5.0,5.0]))) + tfromPrimal (STKS [2] STKScalar) (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [1.0,2.0])))) (\\v8 -> sreplicate @_ @2 (recip (ssum @_ @2 v8)) * v8))"
  "\\dummy" ++ " -> " ++ printAstSimple renames (simplifyInlineContract ast3)
    @?= "\\dummy -> rfromS (tlet (exp (smatvecmul (tfromPrimal (STKS [2,5] STKScalar) (tconcrete (FTKS [2,5] FTKScalar) (sfromListLinear [2,5] [1.0,2.0,3.0,4.0,5.0,1.0,2.0,3.0,4.0,5.0]))) (tlet (smatvecmul (tfromPrimal (STKS [5,4] STKScalar) (tconcrete (FTKS [5,4] FTKScalar) (sfromListLinear [5,4] [1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0,1.0,2.0,3.0,4.0]))) (tlet (ssum @_ @3 (tfromPrimal (STKS [3,4] STKScalar) (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)))) * tfromPrimal (STKS [3,4] STKScalar) (tconcrete (FTKS [3,4] FTKScalar) (sfromListLinear [3,4] [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0]))) + tfromPrimal (STKS [4] STKScalar) (tconcrete (FTKS [4] FTKScalar) (sfromListLinear [4] [1.0,2.0,3.0,4.0]))) (\\v2 -> tlet (tfromPrimal (STKS [4] STKScalar) (recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (tprimalPart v2))))) (\\v3 -> tfromPrimal (STKS [4] STKScalar) (tprimalPart v3) + tfromDual (tdualPart (STKS [4] STKScalar) (tfromPrimal (STKS [4] STKScalar) (tprimalPart v3 * (sreplicate @_ @4 (sscalar 1.0) - tprimalPart v3))) * tdualPart (STKS [4] STKScalar) v2)))) + tfromPrimal (STKS [5] STKScalar) (tconcrete (FTKS [5] FTKScalar) (sfromListLinear [5] [1.0,2.0,3.0,4.0,5.0]))) (\\v5 -> tlet (tfromPrimal (STKS [5] STKScalar) (recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (tprimalPart v5))))) (\\v6 -> tfromPrimal (STKS [5] STKScalar) (tprimalPart v6) + tfromDual (tdualPart (STKS [5] STKScalar) (tfromPrimal (STKS [5] STKScalar) (tprimalPart v6 * (sreplicate @_ @5 (sscalar 1.0) - tprimalPart v6))) * tdualPart (STKS [5] STKScalar) v5)))) + tfromPrimal (STKS [2] STKScalar) (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [1.0,2.0])))) (\\v8 -> sreplicate @_ @2 (recip (ssum @_ @2 v8)) * v8))"

testVT2OPPNonLin2 :: Assertion
testVT2OPPNonLin2 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnist2 logistic softMax1 blackGlyph
      ftk = tftk @RepN (knownSTK @(XParams2 Double))
                       (toTarget @RepN valsInitVT2OPP)
      (artifactRevnonLin, _) = revArtifactAdapt True afcnn2TnonLin ftk
  printArtifactPretty renames artifactRevnonLin
    @?= "\\v31 m1 -> let v9 = ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v10 = exp (negate v9) ; v11 = sreplicate @_ @4 (sscalar 1.0) + v10 ; v12 = recip v11 ; v13 = sreplicate @_ @4 (sscalar 1.0) - v12 ; v14 = v12 * v13 ; v16 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; m17 = str (sreplicate @_ @5 (v12 + v16)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v19 = ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v20 = exp (negate v19) ; v21 = sreplicate @_ @5 (sscalar 1.0) + v20 ; v22 = recip v21 ; v23 = sreplicate @_ @5 (sscalar 1.0) - v22 ; v24 = v22 * v23 ; v26 = sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) ; m27 = str (sreplicate @_ @2 (v22 + v26)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v30 = sreplicate @_ @2 (recip x29) ; v32 = v28 * (sreplicate @_ @2 (negate (recip (x29 * x29)) * ssum @_ @2 (v28 * sfromR v31)) + v30 * sfromR v31) ; m33 = sreplicate @_ @5 v32 ; v34 = ssum @_ @2 (str (str (sfromR (tproject1 (tproject2 m1))) * m33)) ; v35 = v24 * v34 ; m36 = sreplicate @_ @4 v35 ; v37 = ssum @_ @5 (str (m18 * m36)) ; v38 = v14 * v37 in tpair (tpair (tpair (rfromS (str (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * sreplicate @_ @3 v38)), rfromS v38), tpair (rfromS (scast (str (m17 * m36))), rfromS v35)), tpair (rfromS (str (m27 * m33)), rfromS v32))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m1 -> let v9 = ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v10 = exp (negate v9) ; v11 = sreplicate @_ @4 (sscalar 1.0) + v10 ; v12 = recip v11 ; v16 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; m17 = str (sreplicate @_ @5 (v12 + v16)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v19 = ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v20 = exp (negate v19) ; v21 = sreplicate @_ @5 (sscalar 1.0) + v20 ; v22 = recip v21 ; v26 = sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) ; m27 = str (sreplicate @_ @2 (v22 + v26)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v30 = sreplicate @_ @2 (recip x29) in rfromS (v30 * v28)"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\v31 m1 -> tfromS (let v12 = recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m17 = str (sreplicate @_ @5 (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v12)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v22 = recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m27 = str (sreplicate @_ @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v22)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v32 = v28 * (sreplicate @_ @2 (negate (recip (x29 * x29)) * sdot0 v28 (sfromR v31)) + sreplicate @_ @2 (recip x29) * sfromR v31) ; v35 = (v22 * (sreplicate @_ @5 (sscalar 1.0) - v22)) * smatvecmul (str (sfromR (tproject1 (tproject2 m1)))) v32 ; v38 = (v12 * (sreplicate @_ @4 (sscalar 1.0) - v12)) * smatvecmul m18 v35 in tpair (tpair (tpair (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)) * str (sreplicate @_ @3 v38), v38), tpair (str (scast m17) * str (sreplicate @_ @4 (scast v35)), v35)), tpair (str m27 * str (sreplicate @_ @5 v32), v32)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> rfromS (let v28 = exp (smatvecmul (sfromR (tproject1 (tproject2 m1))) (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (smatvecmul (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1))))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))))) + sfromR (tproject2 (tproject2 m1))) in sreplicate @_ @2 (recip (ssum @_ @2 v28)) * v28)"

testVT2OPPNonLin3 :: Assertion
testVT2OPPNonLin3 = do
  resetVarCounter
  let renames = IM.empty
      blackGlyph = treplicate (SNat @3) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 7
      blackLabel = treplicate (SNat @2) knownSTK
                   $ fromPrimal $ tconcrete (FTKR ZSR FTKScalar)
                   $ RepN $ Nested.rscalar 8
      afcnn2TnonLin :: MnistFcnnRanked2.ADFcnnMnist2Parameters
                         (AstTensor AstMethodLet FullSpan) Double
                    -> AstTensor AstMethodLet FullSpan (TKScalar Double)
      afcnn2TnonLin = MnistFcnnRanked2.afcnnMnistLoss2 (blackGlyph,  blackLabel)
      ftk = tftk @RepN (knownSTK @(XParams2 Double))
                       (toTarget @RepN valsInitVT2OPP)
      (artifactRevnonLin, _) = revArtifactAdapt True afcnn2TnonLin ftk
  printArtifactPretty renames artifactRevnonLin
    @?= "\\x33 m1 -> let v9 = ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v10 = exp (negate v9) ; v11 = sreplicate @_ @4 (sscalar 1.0) + v10 ; v12 = recip v11 ; v13 = sreplicate @_ @4 (sscalar 1.0) - v12 ; v14 = v12 * v13 ; v16 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; m17 = str (sreplicate @_ @5 (v12 + v16)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v19 = ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v20 = exp (negate v19) ; v21 = sreplicate @_ @5 (sscalar 1.0) + v20 ; v22 = recip v21 ; v23 = sreplicate @_ @5 (sscalar 1.0) - v22 ; v24 = v22 * v23 ; v26 = sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) ; m27 = str (sreplicate @_ @2 (v22 + v26)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v30 = sreplicate @_ @2 (recip x29) ; v31 = v30 * v28 ; v34 = recip v31 * (sreplicate @_ @2 (sscalar 8.0) * sreplicate @_ @2 (sscalar -1.0 * sfromK x33)) ; v35 = v28 * (sreplicate @_ @2 (negate (recip (x29 * x29)) * ssum @_ @2 (v28 * v34)) + v30 * v34) ; m36 = sreplicate @_ @5 v35 ; v37 = ssum @_ @2 (str (str (sfromR (tproject1 (tproject2 m1))) * m36)) ; v38 = v24 * v37 ; m39 = sreplicate @_ @4 v38 ; v40 = ssum @_ @5 (str (m18 * m39)) ; v41 = v14 * v40 in tpair (tpair (tpair (rfromS (str (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * sreplicate @_ @3 v41)), rfromS v41), tpair (rfromS (scast (str (m17 * m39))), rfromS v38)), tpair (rfromS (str (m27 * m36)), rfromS v35))"
  printArtifactPrimalPretty renames artifactRevnonLin
    @?= "\\m1 -> let v9 = ssum @_ @3 (str (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0))) * str (sfromR (tproject1 (tproject1 (tproject1 m1))))) + sfromR (tproject2 (tproject1 (tproject1 m1))) ; v10 = exp (negate v9) ; v11 = sreplicate @_ @4 (sscalar 1.0) + v10 ; v12 = recip v11 ; v16 = sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) ; m17 = str (sreplicate @_ @5 (v12 + v16)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v19 = ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1))) ; v20 = exp (negate v19) ; v21 = sreplicate @_ @5 (sscalar 1.0) + v20 ; v22 = recip v21 ; v26 = sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) ; m27 = str (sreplicate @_ @2 (v22 + v26)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v30 = sreplicate @_ @2 (recip x29) ; v31 = v30 * v28 ; v32 = log v31 in kfromS (negate (ssum @_ @2 (v32 * sreplicate @_ @2 (sscalar 8.0))))"
  printArtifactPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\x33 m1 -> tfromS (let v12 = recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1)))))) ; m17 = str (sreplicate @_ @5 (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + v12)) ; m18 = str (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) ; v22 = recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (ssum @_ @4 (m17 * m18) + sfromR (tproject2 (tproject2 (tproject1 m1)))))) ; m27 = str (sreplicate @_ @2 (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + v22)) ; v28 = exp (ssum @_ @5 (m27 * str (sfromR (tproject1 (tproject2 m1)))) + sfromR (tproject2 (tproject2 m1))) ; x29 = ssum @_ @2 v28 ; v30 = sreplicate @_ @2 (recip x29) ; v34 = recip (v30 * v28) * (sreplicate @_ @2 (sscalar 8.0) * sreplicate @_ @2 (sscalar -1.0 * sfromK x33)) ; v35 = v28 * (sreplicate @_ @2 (negate (recip (x29 * x29)) * sdot0 v28 v34) + v30 * v34) ; v38 = (v22 * (sreplicate @_ @5 (sscalar 1.0) - v22)) * smatvecmul (str (sfromR (tproject1 (tproject2 m1)))) v35 ; v41 = (v12 * (sreplicate @_ @4 (sscalar 1.0) - v12)) * smatvecmul m18 v38 in tpair (tpair (tpair (sreplicate @_ @4 (sreplicate @_ @3 (sscalar 7.0)) * str (sreplicate @_ @3 v41), v41), tpair (str (scast m17) * str (sreplicate @_ @4 (scast v38)), v38)), tpair (str m27 * str (sreplicate @_ @5 v35), v35)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRevnonLin)
    @?= "\\m1 -> kfromS (let v28 = exp (smatvecmul (sfromR (tproject1 (tproject2 m1))) (sconcrete (sfromListLinear [5] [0.0,0.0,0.0,0.0,0.0]) + recip (sreplicate @_ @5 (sscalar 1.0) + exp (negate (smatvecmul (scast (sfromR (tproject1 (tproject2 (tproject1 m1))))) (sconcrete (sfromListLinear [4] [0.0,0.0,0.0,0.0]) + recip (sreplicate @_ @4 (sscalar 1.0) + exp (negate (smatvecmul (sfromR (tproject1 (tproject1 (tproject1 m1)))) (sreplicate @_ @3 (sscalar 7.0)) + sfromR (tproject2 (tproject1 (tproject1 m1))))))) + sfromR (tproject2 (tproject2 (tproject1 m1))))))) + sfromR (tproject2 (tproject2 m1))) in negate (sdot0 (log (sreplicate @_ @2 (recip (ssum @_ @2 v28)) * v28)) (sreplicate @_ @2 (sscalar 8.0))))"
