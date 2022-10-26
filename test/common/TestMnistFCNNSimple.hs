{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
module TestMnistFCNNSimple
  ( testTrees, shortTestForCITrees
  ) where

import Prelude

import           Control.Monad (foldM)
import           Data.List.Index (imap)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck hiding (label, shuffle)
import           Text.Printf

import HordeAd
import MnistData
import MnistFcnnScalar
import MnistFcnnVector

import Tool.EqEpsilon
import Tool.Shared

testTrees :: [TestTree]
testTrees = [ dumbMnistTests
            , shortCIMnistTests
            , bigMnistTests
            , vectorMnistTests
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ dumbMnistTests
                      , shortCIMnistTests
                      ]

sgdShow :: HasDelta r
        => r
        -> (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
        -> [a]  -- ^ training data
        -> Domain0 r  -- ^ initial parameters
        -> IO r
sgdShow gamma f trainData params0Init = do
  result <-
    fst <$> sgd gamma f trainData (domainsFrom01 params0Init V.empty)
  snd <$> revIO 1 (f $ head trainData) result

sgdTestCase :: String
            -> IO [a]
            -> (Int
                -> Int
                -> a
                -> ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double)
            -> Double
            -> Double
            -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      widthHidden2 = 50
      nParams0 = fcnnMnistLen0 widthHidden widthHidden2
      vec = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams0, show gamma]
  in testCase name $ do
       trainData <- trainDataIO
       res <- sgdShow gamma (trainWithLoss widthHidden widthHidden2)
                      trainData vec
       res @?~ expected

mnistTestCase2
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2 prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
               gamma expected =
  let nParams0 = fcnnMnistLen0 widthHidden widthHidden2
      params0Init = HM.randomVector 44 HM.Uniform nParams0 - HM.scalar 0.5
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show gamma ]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domain0 Double -> (Int, [MnistData Double])
                    -> IO (Domain0 Double)
           runBatch !params0 (k, chunk) = do
             let f = trainWithLoss widthHidden widthHidden2
             (!res, _) <-
               domainsTo01 . fst
               <$> sgd gamma f chunk (domainsFrom01 params0 V.empty)
             let !trainScore = fcnnMnistTest0 widthHidden widthHidden2 chunk res
                 !testScore =
                   fcnnMnistTest0 widthHidden widthHidden2 testData res
                 !lenChunk = length chunk
             hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
             hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
             hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> Domain0 Double -> IO (Domain0 Double)
           runEpoch n params0 | n > epochs = return params0
           runEpoch n params0 = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params0 chunks
             runEpoch (succ n) res
       res <- runEpoch 1 params0Init
       let testErrorFinal =
             1 - fcnnMnistTest0 widthHidden widthHidden2 testData res
       testErrorFinal @?~ expected

mnistTestCase2V
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2V prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let (nParams0, nParams1, _, _) = fcnnMnistLen1 widthHidden widthHidden2
      params0Init = HM.randomVector 44 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init = V.fromList $
        imap (\i nPV -> HM.randomVector (44 + nPV + i) HM.Uniform nPV
                        - HM.scalar 0.5)
             nParams1
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show (length nParams1)
                        , show (sum nParams1 + nParams0), show gamma ]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domain0 Double, Domain1 Double)
                    -> (Int, [MnistData Double])
                    -> IO (Domain0 Double, Domain1 Double)
           runBatch (!params0, !params1) (k, chunk) = do
             let f = trainWithLoss widthHidden widthHidden2
             (resS, resV) <-
               domainsTo01 . fst
               <$> sgd gamma f chunk (domainsFrom01 params0 params1)
             let res = (resS, resV)
                 !trainScore = fcnnMnistTest1
                                         widthHidden widthHidden2 chunk res
                 !testScore = fcnnMnistTest1
                                        widthHidden widthHidden2 testData res
                 !lenChunk = length chunk
             hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
             hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
             hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domain0 Double, Domain1 Double)
                    -> IO (Domain0 Double, Domain1 Double)
           runEpoch n params2 | n > epochs = return params2
           runEpoch n params2 = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params2 chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (params0Init, params1Init)
       let testErrorFinal =
             1 - fcnnMnistTest1 widthHidden widthHidden2 testData res
       testErrorFinal @?~ expected

fcnnMnistLossTanh ::
                   Int
                -> Int
                -> MnistData Double
                -> ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double
fcnnMnistLossTanh widthHidden widthHidden2 (xs, targ) vec =
  let res = fcnnMnist0 tanh softMax widthHidden widthHidden2 xs vec
  in lossCrossEntropy targ res

fcnnMnistLossRelu ::
                   Int
                -> Int
                -> MnistData Double
                -> ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double
fcnnMnistLossRelu widthHidden widthHidden2 (xs, targ) vec =
  let res = fcnnMnist0 relu softMax widthHidden widthHidden2 xs vec
  in lossCrossEntropy targ res

dumbMnistTests :: TestTree
dumbMnistTests = testGroup "Dumb MNIST tests"
  [ let blackGlyph = V.replicate sizeMnistGlyphInt 0
        blackLabel = V.replicate sizeMnistLabelInt 0
        trainData = replicate 10 (blackGlyph, blackLabel)
    in sgdTestCase "black"
         (return trainData) fcnnMnistLoss0 0.02 (-0.0)
  , let whiteGlyph = V.replicate sizeMnistGlyphInt 1
        whiteLabel = V.replicate sizeMnistLabelInt 1
        trainData = replicate 20 (whiteGlyph, whiteLabel)
    in sgdTestCase "white"
         (return trainData) fcnnMnistLoss0 0.02 23.02585095418536
  , let blackGlyph = V.replicate sizeMnistGlyphInt 0
        whiteLabel = V.replicate sizeMnistLabelInt 1
        trainData = replicate 50 (blackGlyph, whiteLabel)
    in sgdTestCase "black/white"
         (return trainData) fcnnMnistLoss0 0.02 23.025850929940457
  , let glyph = V.unfoldrExactN sizeMnistGlyphInt (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabelInt (uniformR (0, 1))
        trainData = map ((\g -> (glyph g, label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "random 100"
         (return trainData) fcnnMnistLoss0 0.02 11.089140063760212
  , sgdTestCase "first 100 trainset samples only"
      (take 100 <$> loadMnistData trainGlyphsPath trainLabelsPath)
      fcnnMnistLoss0 0.02 3.233123290489956
  , testCase "fcnnMnistTest0 on 0.1 params0 300 100 width 10k testset" $ do
      let nParams0 = fcnnMnistLen0 300 100
          params0 = V.replicate nParams0 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - fcnnMnistTest0 300 100 testData params0)
        @?~ 0.902
  , testCase "fcnnMnistTest2VV on 0.1 params0 300 100 width 10k testset" $ do
      let (nParams0, nParams1, _, _) = fcnnMnistLen1 300 100
          params0 = V.replicate nParams0 0.1
          params1 = V.fromList $ map (`V.replicate` 0.1) nParams1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - fcnnMnistTest1 300 100 testData (params0, params1))
        @?~ 0.902
  , testProperty "Compare two forward derivatives and gradient for Mnist0" $
      \seed seedDs ->
      forAll (choose (1, 300)) $ \widthHidden ->
      forAll (choose (1, 100)) $ \widthHidden2 ->
      forAll (choose (0.01, 10)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = createRandomVector sizeMnistGlyphInt seed
            label = createRandomVector sizeMnistLabelInt seedDs
            mnistData :: MnistData Double
            mnistData = (glyph, label)
            nParams0 = fcnnMnistLen0 widthHidden widthHidden2
            paramShape = (nParams0, [], [], [])
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds) = initializerFixed seedDs rangeDs paramShape
            (_, _, _, parametersPerturbation) =
              initializerFixed (seed + seedDs) 1e-7 paramShape
            f :: forall d r. (ADModeAndNum d r, r ~ Double)
              => ADInputs d r -> ADVal d r
            f = fcnnMnistLoss0 widthHidden widthHidden2 mnistData
        in ioProperty $ qcPropDom f parameters ds parametersPerturbation 1
  , testProperty "Compare two forward derivatives and gradient for Mnist1" $
      \seed seedDs ->
      forAll (choose (1, 2000)) $ \widthHidden ->
      forAll (choose (1, 5000)) $ \widthHidden2 ->
      forAll (choose (0.01, 0.5)) $ \range ->  -- large nn, so NaNs fast
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = createRandomVector sizeMnistGlyphInt seed
            label = createRandomVector sizeMnistLabelInt seedDs
            mnistData :: MnistData Double
            mnistData = (glyph, label)
            paramShape = fcnnMnistLen1 widthHidden widthHidden2
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds) = initializerFixed seedDs rangeDs paramShape
            (_, _, _, parametersPerturbation) =
              initializerFixed (seed + seedDs) 1e-7 paramShape
            f :: forall d r. (ADModeAndNum d r, r ~ Double)
              => ADInputs d r -> ADVal d r
            f = fcnnMnistLoss1 widthHidden widthHidden2 mnistData
        in ioProperty $ qcPropDom f parameters ds parametersPerturbation 1
  ]

bigMnistTests :: TestTree
bigMnistTests = testGroup "MNIST tests with a 2-hidden-layer nn"
  [ mnistTestCase2 "1 epoch, 1 batch" 1 1 fcnnMnistLoss0 300 100 0.02
                   0.1269
  , mnistTestCase2 "tanh: 1 epoch, 1 batch" 1 1 fcnnMnistLossTanh 300 100 0.02
                   0.6406000000000001
  , mnistTestCase2 "relu: 1 epoch, 1 batch" 1 1 fcnnMnistLossRelu 300 100 0.02
                   0.7248
  , mnistTestCase2 "1 epoch, 1 batch, wider" 1 1 fcnnMnistLoss0 500 150 0.02
                   0.1269
  , mnistTestCase2 "2 epochs, but only 1 batch" 2 1 fcnnMnistLoss0 300 100 0.02
                   9.809999999999997e-2
  ]

vectorMnistTests :: TestTree
vectorMnistTests = testGroup "MNIST VV tests with a 2-hidden-layer nn"
  [ mnistTestCase2V "1 epoch, 1 batch, wider" 1 1 fcnnMnistLoss1 500 150 0.02
                    0.13959999999999995
  , mnistTestCase2V "2 epochs, but only 1 batch" 2 1 fcnnMnistLoss1 300 100 0.02
                    0.10019999999999996
  , mnistTestCase2V "1 epoch, all batches" 1 99 fcnnMnistLoss1 300 100 0.02
                    5.389999999999995e-2
  ]

shortCIMnistTests :: TestTree
shortCIMnistTests = testGroup "Short CI MNIST tests"
  [ mnistTestCase2 "2 artificial 1 2 3 4 5" 1 2 fcnnMnistLoss0 3 4 5
                   0.8972
  , mnistTestCase2 "2 artificial 5 4 3 2 1" 5 4 fcnnMnistLoss0 3 2 1
                   0.8991
  , mnistTestCase2V "VV 1 epoch, 1 batch" 1 1 fcnnMnistLoss1 300 100 0.02
                    0.12960000000000005
  , mnistTestCase2V "VV artificial 1 2 3 4 5" 1 2 fcnnMnistLoss1 3 4 5
                    0.8972
  , mnistTestCase2V "VV artificial 5 4 3 2 1" 5 4 fcnnMnistLoss1 3 2 1
                    0.6585
  ]
