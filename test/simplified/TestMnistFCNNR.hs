{-# LANGUAGE OverloadedLists #-}
-- | Tests of "MnistFcnnRanked1" and "MnistFcnnRanked2" dense neural networks
-- using a few different optimization pipelines.
module TestMnistFCNNR
  ( testTrees
  ) where

import Prelude

import Control.Arrow ((***))
import Control.Monad (foldM, unless)
import Data.Bifunctor (first, second)
import Data.Proxy (Proxy (Proxy))
import System.IO (hPutStrLn, stderr)
import System.Random
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.QuickCheck hiding (label, shuffle)
import Text.Printf

import Data.Array.Nested.Ranked.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.Ops (tconcrete)

import CrossTesting
import EqEpsilon

import MnistData
import MnistFcnnRanked1 qualified
import MnistFcnnRanked2 (XParams2)
import MnistFcnnRanked2 qualified

testTrees :: [TestTree]
testTrees = [ testCase "2VTOrev" mnistTestCase2VTOrev
            , tensorADValMnistTests
            , tensorIntermediateMnistTests
            , tensorADOnceMnistTests
            , tensorADValMnistTests2
            , tensorIntermediateMnistTests2
            , tensorADOnceMnistTests2
            ]


-- * Running rev' on the gradient of afcnnMnistLoss2

mnistTestCase2VTOrev :: Assertion
mnistTestCase2VTOrev =
  let (!targetInit, !art) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradientX
          @Double (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) 1500 500
      blackGlyph = rreplicate sizeMnistGlyphInt $ rscalar 7
      ftk = tftk @Concrete (knownSTK @(XParams2 Double Float))
                 targetInit
      f :: forall target r. (ADReady target, r ~ Double)
        => target (TKR 1 r) -> target (TKR 1 r)
      f label =
        let val = tpair (tconcrete ftk targetInit)
                        (tpair (rconcrete $ unConcrete blackGlyph) label)
            env = extendEnv (artVarDomainRev art) val emptyEnv
        in tproject1 $ tproject2
           $ interpretAst @target env (artDerivativeRev art)
  in assertEqualUpToEpsilon' 1e-10
       (ringestData [10] [6.922657834114052e-2,-3.2210167235305924e-5,0.12334696753032606,-4.892729845753193e-3,3.010762414514606e-2,2.0344986964700877e-2,-3.78339785604896e-2,5.77360835535866e-2,0.10761507003315526,-7.909016076299641e-2])
       (rev' f (rreplicate sizeMnistLabelInt $ rscalar 8))


-- * Using lists of vectors, which is rank 1

type XParams widthHidden widthHidden2 r =
  X (MnistFcnnRanked1.ADFcnnMnist1Parameters
       Concrete widthHidden widthHidden2 r)

-- POPL differentiation, straight via the ADVal instance of RankedTensor,
-- which side-steps vectorization.
mnistTestCase1VTA
  :: forall r.
     ( Differentiable r, NumScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTA prefix epochs maxBatches widthHiddenInt widthHidden2Int
                  gamma batchSize expected
                  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ widthSTK
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 Concrete widthHidden widthHidden2 r
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
          -> ADVal Concrete (XParams widthHidden widthHidden2 r)
          -> ADVal Concrete (TKScalar r)
        f (glyph, label) adinputs =
          MnistFcnnRanked1.afcnnMnistLoss1
            widthHiddenSNat widthHidden2SNat
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
    -- Mimic how backprop tests and display it, even though tests
    -- should not print, in principle.
    let runBatch :: Concrete (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                 -> Concrete (XParams widthHidden widthHidden2 r)
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                      (0.2146 :: Double)
  , mnistTestCase1VTA "VTA1 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                      (0.8972 :: Float)
  , mnistTestCase1VTA "VTA1 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                      (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase1VTI
  :: forall r.
     ( Differentiable r, NumScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase1VTI prefix epochs maxBatches widthHiddenInt widthHidden2Int
                  gamma batchSize expected
                  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  withSNat widthHiddenInt $ \(widthHiddenSNat :: SNat widthHidden) ->
  withSNat widthHidden2Int $ \(widthHidden2SNat :: SNat widthHidden2) ->
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[SizeMnistGlyph] r)) (SNat @widthHidden)) $
  withKnownSTK
    (stkOfListR (knownSTK @(TKS '[widthHidden] Float)) (SNat @widthHidden2)) $
  let valsInit :: MnistFcnnRanked1.ADFcnnMnist1Parameters
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
      ftk = tftk @Concrete (knownSTK @(XParams widthHidden widthHidden2 r))
                 targetInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ widthSTK
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 Concrete widthHidden widthHidden2 r
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
        ast = simplifyInline
              $ MnistFcnnRanked1.afcnnMnistLoss1
                  widthHiddenSNat widthHidden2SNat (astGlyph, astLabel)
                  (fromTarget varAst)
        f :: MnistDataLinearR r
          -> ADVal Concrete (XParams widthHidden widthHidden2 r)
          -> ADVal Concrete (TKScalar r)
        f (glyph, label) varInputs =
          let env = extendEnv var varInputs emptyEnv
              envMnist = extendEnv varGlyph (rconcrete glyph)
                         $ extendEnv varLabel (rconcrete label) env
          in interpretAstFull envMnist ast
    let runBatch :: Concrete (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                 -> Concrete (XParams widthHidden widthHidden2 r)
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                      (0.2116 :: Double)
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
     ( Differentiable r, NumScalar r, ADTensorScalar r ~ r
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
                    Concrete widthHidden widthHidden2 r
      valsInit = fst $ randomValue 1 (mkStdGen 44)
      targetInit :: Concrete (XParams widthHidden widthHidden2 r)
      targetInit = toTarget @Concrete valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHiddenInt, show widthHidden2Int
                        , show $ widthSTK
                          $ knownSTK @(XParams widthHidden widthHidden2 r)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
      ftest :: [MnistDataLinearR r]
            -> MnistFcnnRanked1.ADFcnnMnist1Parameters
                 Concrete widthHidden widthHidden2 r
            -> r
      ftest = MnistFcnnRanked1.afcnnMnistTest1 widthHiddenSNat widthHidden2SNat
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let dataInit = case testData of
          d : _ -> (rconcrete *** rconcrete) d
          [] -> error "empty test data"
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
        artRaw = gradArtifact f (valsInit, dataInit)
        art = simplifyArtifactRev artRaw
        go :: [MnistDataLinearR r]
           -> Concrete (XParams widthHidden widthHidden2 r)
           -> Concrete (XParams widthHidden widthHidden2 r)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
    let runBatch :: Concrete (XParams widthHidden widthHidden2 r)
                 -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                 -> Concrete (XParams widthHidden widthHidden2 r)
                 -> IO (Concrete (XParams widthHidden widthHidden2 r))
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
                      (0.2116 :: Double)
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
     ( Differentiable r, NumScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTA prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected
                  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 r Float)))
            1 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ widthSTK $ knownSTK @(XParams2 r Float)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let f :: MnistDataLinearR r -> ADVal Concrete (XParams2 r Float)
          -> ADVal Concrete (TKScalar r)
        f (glyph, label) adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rconcrete glyph, rconcrete label) (fromTarget adinputs)
    let runBatch :: Concrete (XParams2 r Float) -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams2 r Float))
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
    let runEpoch :: Int -> Concrete (XParams2 r Float)
                 -> IO (Concrete (XParams2 r Float))
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
  [ mnistTestCase2VTA "VTA2 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                       (0.21299999999999997 :: Double)
  , mnistTestCase2VTA "VTA2 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                       (0.8972 :: Float)
  , mnistTestCase2VTA "VTA2 artificial 5 4 3 2 1" 5 4 3 2 1 5000
                       (0.6805:: Double)
  , mnistTestCase2VTA "VTA2 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                       (1 :: Float)
  ]

-- POPL differentiation, with Ast term defined and vectorized only once,
-- but differentiated anew in each gradient descent iteration.
mnistTestCase2VTI
  :: forall r.
     ( Differentiable r, NumScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTI prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected
                  | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
  withSNat widthHidden $ \(SNat @widthHidden) ->
  withSNat widthHidden2 $ \(SNat @widthHidden2) ->
  let targetInit =
        forgetShape $ fst
        $ randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 r Float)))
            1 (mkStdGen 44)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ widthSTK $ knownSTK @(XParams2 r Float)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let ftk = tftk @Concrete (knownSTK @(XParams2 r Float)) targetInit
    (_, _, var, varAst) <- funToAstRevIO ftk
    (varGlyph, astGlyph) <-
      funToAstIO (FTKR (sizeMnistGlyphInt :$: ZSR) FTKScalar) id
    (varLabel, astLabel) <-
      funToAstIO (FTKR (sizeMnistLabelInt :$: ZSR) FTKScalar) id
    let ast :: AstTensor AstMethodLet FullSpan (TKScalar r)
        ast = simplifyInline
              $ MnistFcnnRanked2.afcnnMnistLoss2
                  (astGlyph, astLabel)
                  (fromTarget varAst)
        f :: MnistDataLinearR r -> ADVal Concrete (XParams2 r Float)
          -> ADVal Concrete (TKScalar r)
        f (glyph, label) varInputs =
          let env = extendEnv var varInputs emptyEnv
              envMnist = extendEnv varGlyph (rconcrete glyph)
                         $ extendEnv varLabel (rconcrete label) env
          in interpretAstFull envMnist ast
    let runBatch :: Concrete (XParams2 r Float) -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams2 r Float))
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
    let runEpoch :: Int -> Concrete (XParams2 r Float)
                 -> IO (Concrete (XParams2 r Float))
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
  [ mnistTestCase2VTI "VTI2 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                       (0.20779999999999998 :: Double)
  , mnistTestCase2VTI "VTI2 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                       (0.9108 :: Float)
  , mnistTestCase2VTI "VTI2 artificial 5 4 3 2 1" 5 4 3 2 1 5000
                       (0.8129 :: Double)
  , mnistTestCase2VTI "VTI2 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                       (1 :: Float)
  ]

-- JAX differentiation, Ast term built and differentiated only once
-- and the result interpreted with different inputs in each gradient
-- descent iteration.
mnistTestCase2VTO
  :: forall r.
     ( Differentiable r, NumScalar r
     , PrintfArg r, AssertEqualUpToEpsilon r, ADTensorScalar r ~ r )
  => String
  -> Int -> Int -> Int -> Int -> Double -> Int -> r
  -> TestTree
mnistTestCase2VTO prefix epochs maxBatches widthHidden widthHidden2
                  gamma batchSize expected =
  let (!targetInit, !artRaw) =
        MnistFcnnRanked2.mnistTrainBench2VTOGradient
          @r (Proxy @Float) IgnoreIncomingCotangent
          1 (mkStdGen 44) widthHidden widthHidden2
      !art = simplifyArtifactRev artRaw
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show $ widthSTK $ knownSTK @(XParams2 r Float)
                        , show (tsize knownSTK targetInit)
                        , show gamma ]
  in testCase name $ do
    hPutStrLn stderr $
      printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
             prefix epochs maxBatches
    trainData <- loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map mkMnistDataLinearR . take (batchSize * maxBatches)
                <$> loadMnistData testGlyphsPath testLabelsPath
    let go :: [MnistDataLinearR r] -> Concrete (XParams2 r Float)
           -> Concrete (XParams2 r Float)
        go [] parameters = parameters
        go ((glyph, label) : rest) !parameters =
          let parametersAndInput =
                tpair parameters (tpair (rconcrete glyph) (rconcrete label))
              gradient = tproject1 $ snd
                         $ revInterpretArtifact art parametersAndInput Nothing
          in go rest (updateWithGradient gamma knownSTK parameters gradient)
    let runBatch :: Concrete (XParams2 r Float) -> (Int, [MnistDataLinearR r])
                 -> IO (Concrete (XParams2 r Float))
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
    let runEpoch :: Int -> Concrete (XParams2 r Float)
                 -> IO (Concrete (XParams2 r Float))
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
  [ mnistTestCase2VTO "VTO2 1 epoch, 1 batch" 1 1 300 100 0.02 5000
                       (0.20779999999999998 :: Double)
  , mnistTestCase2VTO "VTO2 artificial 1 2 3 4 5" 1 2 3 4 5 5000
                       (0.9108 :: Float)
  , mnistTestCase2VTO "VTO2 artificial 5 4 3 2 1" 5 4 3 2 1 5000
                       (0.8129 :: Double)
  , mnistTestCase2VTO "VTO2 1 epoch, 0 batch" 1 0 300 100 0.02 5000
                       (1 :: Float)
  , testProperty "VTO2 grad vs fwd" $
    \seed0 ->
    forAllShrink (chooseInt (0, 600)) shrinkIntegral $ \width1Hidden ->
    forAllShrink (chooseInt (0, 200)) shrinkIntegral $ \width1Hidden2 ->
    forAllShrink (chooseInt (0, 5)) shrinkIntegral $ \simp ->
    forAll (choose (0.01, 1)) $ \range ->
    forAll (choose (0.01, 1)) $ \range2 ->
    forAll (choose (0.5, 1.5)) $ \dt ->
    forAll (choose (0, 1e-7)) $ \(perturbation :: Double) ->
    withSNat (1 + width1Hidden) $ \(SNat @widthHidden) ->
    withSNat (1 + width1Hidden2) $ \(SNat @widthHidden2) ->
    let (glyph0, seed2) = randomValue @(Concrete (TKS '[SizeMnistGlyph] Double))
                                      0.5 (mkStdGen seed0)
        (label0, seed3) = randomValue @(Concrete (TKS '[SizeMnistLabel] Double))
                                      5 seed2
        (glyph, label) = ( rmap1 (rscalar 0.5 +) $ forgetShape glyph0
                         , rmap1 (rscalar 5 + ) $ forgetShape label0 )
        ds :: Concrete (XParams2 Double Double)
        (ds, seed4) = first forgetShape $
          randomValue
            @(Concrete (X (MnistFcnnRanked2.ADFcnnMnist2ParametersShaped
                             Concrete widthHidden widthHidden2 Double Double)))
            range seed3
        (targetInit, artRaw) =
          MnistFcnnRanked2.mnistTrainBench2VTOGradient
            @Double (Proxy @Double) UseIncomingCotangent
            range2 seed4 (1 + width1Hidden) (1 + width1Hidden2)
        art = iterate simplifyArtifactRev artRaw !! simp
        stk = knownSTK @(XParams2 Double Double)
        ftk = tftk @Concrete stk targetInit
        parametersAndInput = tpair targetInit (tpair glyph label)
        (value0, _gradient0) = second tproject1 $
          revInterpretArtifact art parametersAndInput Nothing
        (value1, gradient1) = second tproject1 $
          revInterpretArtifact art parametersAndInput (Just $ kconcrete dt)
        f :: ADVal Concrete (XParams2 Double Double)
          -> ADVal Concrete (TKScalar Double)
        f adinputs =
          MnistFcnnRanked2.afcnnMnistLoss2
            (rfromPrimal glyph, rfromPrimal label) (fromTarget adinputs)
        (value2, derivative2) = cjvp2 f targetInit ds
--        goodDt :: forall r. GoodScalar r => r
--        goodDt = ifDifferentiable @r (realToFrac dt) 0
--        targetDt :: Concrete (XParams2 Double Double)
--        targetDt = replTarget goodDt ftk
        goodPerturbation :: forall r. NumScalar r => r
        goodPerturbation = ifDifferentiable @r (realToFrac perturbation) 0
        targetPerturbed :: Concrete (XParams2 Double Double)
        targetPerturbed = treplTarget goodPerturbation ftk
        targetInitPerturbed :: Concrete (XParams2 Double Double)
        targetInitPerturbed = taddTarget stk targetInit targetPerturbed
        (value3, derivative3) = cjvp2 f targetInit targetPerturbed
        value4 :: Concrete (TKScalar Double)
        value4 = MnistFcnnRanked2.afcnnMnistLoss2
                   (rfromPrimal glyph, rfromPrimal label)
                   (fromTarget targetInitPerturbed)
    in
      conjoin
        [ counterexample
            ("Objective function value from grad and jvp matches: "
             ++ show (value1, value2, value1 - value2))
            (abs (value1 - value2) < 1e-10)
        , counterexample
            ("Gradient and derivative agrees: "
             ++ show ( dt, derivative2, tdot0Target ftk gradient1 ds
                     , tdot0Target FTKScalar (kconcrete dt) derivative2
                       - tdot0Target ftk gradient1 ds ))
            (abs (tdot0Target FTKScalar (kconcrete dt) derivative2
                  - tdot0Target ftk gradient1 ds) < 1e-10)
--        , counterexample  -- this is implied by the other clauses
--            "Gradient is a linear function"
--            (gradient1 === tmultTarget stk targetDt gradient0)
        , counterexample
            "Objective function value unaffected by incoming cotangent"
            (value0 === value1)
        , counterexample
            "Objective function value unaffected by derivative perturbation"
            (value2 === value3)
        , counterexample
            ("Derivative approximates the perturbation of value: "
             ++ show ( value2, derivative3, value4
                     , (value3 + derivative3) - value4) )
            (abs ((value3 + derivative3) - value4) < 1e-6)
        ]
  ]
