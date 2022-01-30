{-# LANGUAGE FlexibleContexts #-}
module TestMnistFC (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable
import           Numeric.LinearAlgebra (Numeric, konst, uniformSample)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.MnistTools

testTrees :: [TestTree]
testTrees = [ dumbMnistTests
            , bigMnistTests
            , vectorMnistTests
            , matrixMnistTests
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ dumbMnistTests
                      , shortCIMnistTests
                      ]

sgdShow :: (Eq r, Numeric r, Num (Data.Vector.Storable.Vector r))
        => r
        -> (a -> VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
        -> [a]  -- ^ training data
        -> Domain r  -- ^ initial parameters
        -> ([r], r)
sgdShow gamma f trainData params0 =
  let (res, _, _) = sgd gamma f trainData (params0, V.empty, V.empty)
      (_, value) = df (f $ head trainData) (res, V.empty, V.empty)
  in (V.toList res, value)

sgdTestCase
  :: String
  -> IO [a]
  -> (Int
      -> Int
      -> a
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Double
  -> Double
  -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      widthHidden2 = 50
      nParams = lenMnist2 widthHidden widthHidden2
      vec = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams, show gamma]
  in testCase name $ do
       trainData <- trainDataIO
       snd (sgdShow gamma (trainWithLoss widthHidden widthHidden2)
                          trainData vec)
          @?= expected

mnistTestCase2
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2 prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
               gamma expected =
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 44
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show gamma ]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domain Double -> (Int, [MnistData Double])
                    -> IO (Domain Double)
           runBatch !params (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss widthHidden widthHidden2
                 (!res, _, _) = sgd gamma f chunk (params, V.empty, V.empty)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist2 widthHidden widthHidden2 chunk res
                 testScore  = testMnist2 widthHidden widthHidden2 testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> Domain Double -> IO (Domain Double)
           runEpoch n params | n > epochs = return params
           runEpoch n params = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 params0
       let testErrorFinal = 1 - testMnist2 widthHidden widthHidden2 testData res
       testErrorFinal @?= expected

mnistTestCase2V
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2V prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let nParams = lenMnist2V widthHidden widthHidden2
      nParamsV = lenVectorsMnist2V widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 44
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.5, 0.5))
                                          (mkStdGen $ 44 + nPV + i))
               nParamsV
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show (V.length nParamsV)
                        , show (V.sum nParamsV + nParams), show gamma ]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domain Double, DomainV Double)
                    -> (Int, [MnistData Double])
                    -> IO (Domain Double, DomainV Double)
           runBatch (!params, !paramsV) (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss widthHidden widthHidden2
                 (resS, resV, _) = sgd gamma f chunk (params, paramsV, V.empty)
                 res = (resS, resV)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist2V widthHidden widthHidden2 chunk res
                 testScore = testMnist2V widthHidden widthHidden2 testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domain Double, DomainV Double)
                    -> IO (Domain Double, DomainV Double)
           runEpoch n params2 | n > epochs = return params2
           runEpoch n params2 = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params2 chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 (params0, paramsV0)
       let testErrorFinal =
             1 - testMnist2V widthHidden widthHidden2 testData res
       testErrorFinal @?= expected

nnMnistLossTanh :: DeltaMonad Double m
                => Int
                -> Int
                -> MnistData Double
                -> VecDualDelta Double
                -> m (DualDelta Double)
nnMnistLossTanh widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist2 tanhAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

nnMnistLossRelu :: DeltaMonad Double m
                => Int
                -> Int
                -> MnistData Double
                -> VecDualDelta Double
                -> m (DualDelta Double)
nnMnistLossRelu widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist2 reluAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

mnistTestCase2L
  :: String
  -> Int
  -> Int
  -> (MnistData Double
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2L prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let nParams = lenMnist2L widthHidden widthHidden2
      nParamsV = lenVectorsMnist2L widthHidden widthHidden2
      nParamsL = lenMatrixMnist2L widthHidden widthHidden2
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 44
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.5, 0.5))
                                          (mkStdGen $ 44 + nPV + i))
               nParamsV
      paramsL0 = V.imap (\i (rows, cols) ->
                           uniformSample (44 + rows + i) rows
                                         (replicate cols (-0.5, 0.5)))
                        nParamsL
      totalParams = nParams + V.sum nParamsV
                    + V.sum (V.map (uncurry (+)) nParamsL)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show (V.length nParamsV)
                        , show (V.length nParamsL), show totalParams
                        , show gamma ]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domain Double, DomainV Double, DomainL Double)
                    -> (Int, [MnistData Double])
                    -> IO (Domain Double, DomainV Double, DomainL Double)
           runBatch (!params, !paramsV, !paramsL) (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss
                 res = sgd gamma f chunk (params, paramsV, paramsL)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist2L chunk res
                 testScore = testMnist2L testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domain Double, DomainV Double, DomainL Double)
                    -> IO (Domain Double, DomainV Double, DomainL Double)
           runEpoch n params2 | n > epochs = return params2
           runEpoch n params2 = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params2 chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 (params0, paramsV0, paramsL0)
       let testErrorFinal = 1 - testMnist2L testData res
       testErrorFinal @?= expected

dumbMnistTests :: TestTree
dumbMnistTests = testGroup "Dumb MNIST tests"
  [ let blackGlyph = V.replicate sizeMnistGlyph 0
        blackLabel = V.replicate sizeMnistLabel 0
        trainData = replicate 10 (blackGlyph, blackLabel)
    in sgdTestCase "black"
         (return trainData) nnMnistLoss2 0.02 (-0.0)
  , let whiteGlyph = V.replicate sizeMnistGlyph 1
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 20 (whiteGlyph, whiteLabel)
    in sgdTestCase "white"
         (return trainData) nnMnistLoss2 0.02 23.025850929941267
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 50 (blackGlyph, whiteLabel)
    in sgdTestCase "black/white"
         (return trainData) nnMnistLoss2 0.02 23.02585092994046
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        trainData = map ((\g -> (glyph g, label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "random 100"
         (return trainData) nnMnistLoss2 0.02 11.49975974315736
  , sgdTestCase "first 100 trainset samples only"
      (take 100 <$> loadMnistData trainGlyphsPath trainLabelsPath)
      nnMnistLoss2 0.02 2.4789327419863603
  , testCase "testMnist2 on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2 300 100
          params = V.replicate nParams 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2 300 100 testData params) @?= 0.902
  , testCase "testMnist2VV on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2V 300 100
          params = V.replicate nParams 0.1
          nParamsV = lenVectorsMnist2V 300 100
          paramsV = V.map (\nPV -> V.replicate nPV 0.1) nParamsV
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2V 300 100 testData (params, paramsV)) @?= 0.902
  , testCase "testMnist2LL on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2L 300 100
          params = V.replicate nParams 0.1
          nParamsV = lenVectorsMnist2L 300 100
          paramsV = V.map (\nPV -> V.replicate nPV 0.1) nParamsV
          nParamsL = lenMatrixMnist2L 300 100
          paramsL = V.map (\ij -> konst 0.1 ij) nParamsL
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2L testData (params, paramsV, paramsL)) @?= 0.902
 ]

bigMnistTests :: TestTree
bigMnistTests = testGroup "MNIST tests with a 2-hidden-layer nn"
  [ mnistTestCase2 "1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1452
  , mnistTestCase2 "tanh: 1 epoch, 1 batch" 1 1 nnMnistLossTanh 300 100 0.02
                  0.32509999999999994
  , mnistTestCase2 "relu: 1 epoch, 1 batch" 1 1 nnMnistLossRelu 300 100 0.02
                  0.1582
  , mnistTestCase2 "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2 500 150 0.02
                   0.12680000000000002
  , mnistTestCase2 "2 epochs, but only 1 batch" 2 1 nnMnistLoss2 300 100 0.02
                   9.489999999999998e-2
  , mnistTestCase2 "1 epoch, all batches" 1 99 nnMnistLoss2 300 100 0.02
                   5.5300000000000016e-2
                     -- doh, worse than 1-hidden-layer, but twice slower
  , mnistTestCase2 "artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                   0.8972
  , mnistTestCase2 "artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                   0.7132000000000001
  ]

vectorMnistTests :: TestTree
vectorMnistTests = testGroup "MNIST VV tests with a 2-hidden-layer nn"
  [ mnistTestCase2V "1 epoch, 1 batch" 1 1 nnMnistLoss2V 300 100 0.02
                    0.14390000000000003
  , mnistTestCase2V "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2V 500 150 0.02
                    0.1421
  , mnistTestCase2V "2 epochs, but only 1 batch" 2 1 nnMnistLoss2V 300 100 0.02
                    9.619999999999995e-2
  , mnistTestCase2V "1 epoch, all batches" 1 99 nnMnistLoss2V 300 100 0.02
                    5.4200000000000026e-2
                      -- doh, worse than 1-hidden-layer, but twice slower
  , mnistTestCase2V "artificial 1 2 3 4 5" 1 2 nnMnistLoss2V 3 4 5
                    0.8972
  , mnistTestCase2V "artificial 5 4 3 2 1" 5 4 nnMnistLoss2V 3 2 1
                    0.7755
  ]

matrixMnistTests :: TestTree
matrixMnistTests = testGroup "MNIST LL tests with a 2-hidden-layer nn"
  [ mnistTestCase2L "1 epoch, 1 batch" 1 1 nnMnistLoss2L 300 100 0.02
                    0.14390000000000003
  , mnistTestCase2L "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2L 500 150 0.02
                    0.1421
  , mnistTestCase2L "2 epochs, but only 1 batch" 2 1 nnMnistLoss2L 300 100 0.02
                    9.619999999999995e-2
  , mnistTestCase2L "1 epoch, all batches" 1 99 nnMnistLoss2L 300 100 0.02
                    5.4200000000000026e-2
                      -- doh, worse than 1-hidden-layer, but twice slower
  , mnistTestCase2L "artificial 1 2 3 4 5" 1 2 nnMnistLoss2L 3 4 5
                    0.8972
  , mnistTestCase2L "artificial 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.7755
  ]

shortCIMnistTests :: TestTree
shortCIMnistTests = testGroup "Short CI MNIST tests"
  [ mnistTestCase2 "2 - 1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1452
  , mnistTestCase2 "2 artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                   0.8972
  , mnistTestCase2 "2 artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                   0.7132000000000001
  , mnistTestCase2V "VV 1 epoch, 1 batch" 1 1 nnMnistLoss2V 300 100 0.02
                    0.14390000000000003
  , mnistTestCase2V "VV artificial 1 2 3 4 5" 1 2 nnMnistLoss2V 3 4 5
                    0.8972
  , mnistTestCase2V "VV artificial 5 4 3 2 1" 5 4 nnMnistLoss2V 3 2 1
                    0.7755
  , mnistTestCase2L "LL 1 epoch, 1 batch" 1 1 nnMnistLoss2L 300 100 0.02
                    0.14390000000000003
  , mnistTestCase2L "LL artificial 1 2 3 4 5" 1 2 nnMnistLoss2L 3 4 5
                    0.8972
  , mnistTestCase2L "LL artificial 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.7755
  ]
