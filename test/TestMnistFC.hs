{-# LANGUAGE FlexibleContexts #-}
module TestMnistFC (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd.Engine
import HordeAd.MnistTools

testTrees :: [TestTree]
testTrees = [ dumbMnistTests
            , smallMnistTests
            , bigMnistTests
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ dumbMnistTests
                      , shortCIMnistTests
                      ]

sgdShow :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
        => r
        -> (a -> VecDualDelta r -> DeltaMonadGradient r (DualDelta r))
        -> [a]  -- ^ training data
        -> Domain r  -- ^ initial parameters
        -> ([r], r)
sgdShow gamma f trainData params0 =
  let res = sgd gamma f trainData params0
      (_, value) = df (f $ head trainData) res
  in (V.toList res, value)

sgdTestCase
  :: String
  -> IO [a]
  -> (Int
      -> a
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Double
  -> Double
  -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      nParams = lenMnist widthHidden
      vec = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams, show gamma]
  in testCase name $ do
       trainData <- trainDataIO
       snd (sgdShow gamma (trainWithLoss widthHidden) trainData vec)
          @?= expected

mnistTestCase
  :: String
  -> Int
  -> Int
  -> (Int
      -> MnistData Double
      -> VecDualDelta Double
      -> DeltaMonadGradient Double (DualDelta Double))
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase prefix epochs maxBatches trainWithLoss widthHidden gamma
              expected =
  let nParams = lenMnist widthHidden
      params0 = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 44
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches, show widthHidden
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
             let f = trainWithLoss widthHidden
                 !res = sgd gamma f chunk params
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist widthHidden chunk res
                 testScore  = testMnist widthHidden testData res
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
       let testErrorFinal = 1 - testMnist widthHidden testData res
       testErrorFinal @?= expected

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
                 !res = sgd gamma f chunk params
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

chunksOf :: Int -> [e] -> [[e]]
chunksOf n = go where
  go [] = []
  go l = let (chunk, rest) = splitAt n l
         in chunk : go rest

nnMnistLossTanh :: DeltaMonad Double m
                => Int
                -> MnistData Double
                -> VecDualDelta Double
                -> m (DualDelta Double)
nnMnistLossTanh widthHidden (xs, targ) vec = do
  res <- nnMnist tanhAct softMaxAct widthHidden xs vec
  lossCrossEntropy targ res

nnMnistLossRelu :: DeltaMonad Double m
                => Int
                -> MnistData Double
                -> VecDualDelta Double
                -> m (DualDelta Double)
nnMnistLossRelu widthHidden (xs, targ) vec = do
  res <- nnMnist reluAct softMaxAct widthHidden xs vec
  lossCrossEntropy targ res

dumbMnistTests :: TestTree
dumbMnistTests = testGroup "Dumb MNIST tests"
  [ let blackGlyph = V.replicate sizeMnistGlyph 0
        blackLabel = V.replicate sizeMnistLabel 0
        trainData = replicate 10 (blackGlyph, blackLabel)
    in sgdTestCase "black"
         (return trainData) nnMnistLoss 0.02 (-0.0)
  , let whiteGlyph = V.replicate sizeMnistGlyph 1
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 20 (whiteGlyph, whiteLabel)
    in sgdTestCase "white"
         (return trainData) nnMnistLoss 0.02 25.190345811686008
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 50 (blackGlyph, whiteLabel)
    in sgdTestCase "black/white"
         (return trainData) nnMnistLoss 0.02 23.025850929940457
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        trainData = map ((\g -> (glyph g, label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "random 100"
         (return trainData) nnMnistLoss 0.02 12.871539859686832
  , sgdTestCase "first 100 trainset samples only"
      (take 100 <$> loadMnistData trainGlyphsPath trainLabelsPath)
      nnMnistLoss 0.02 4.7615613127819705
  , testCase "testMnist on 0.1 params 250 width 10k testset" $ do
      let nParams = lenMnist 250
          params = V.replicate nParams 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist 250 testData params) @?= 0.902
  , testCase "testMnist on random params 250 width 10k testset" $ do
      let nParams = lenMnist 250
          params = V.unfoldrExactN nParams (uniformR (-0.5, 0.5)) $ mkStdGen 33
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist 250 testData params) @?= 0.8489
  , testCase "testMnist on 0.1 params 2500 width 1k testset" $ do
      let nParams = lenMnist 2500
          params = V.replicate nParams 0.1
      testData <- take 1000 <$> loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist 2500 testData params) @?= 0.915
  , testCase "testMnist2 on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2 300 100
          params = V.replicate nParams 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2 300 100 testData params) @?= 0.902
 ]

smallMnistTests :: TestTree
smallMnistTests = testGroup "MNIST tests with a 1-hidden-layer nn"
  [ mnistTestCase "1 epoch, 2 batches" 1 2 nnMnistLoss 250 0.02
                  9.260000000000002e-2
  , mnistTestCase "tanh: 1 epoch, 2 batches" 1 2 nnMnistLossTanh 250 0.02
                  0.32509999999999994
  , mnistTestCase "relu: 1 epoch, 2 batches" 1 2 nnMnistLossRelu 250 0.02
                  0.1582
  , mnistTestCase "2 epochs, but only 1 batch" 2 1 nnMnistLoss 250 0.02
                  9.819999999999995e-2
  , mnistTestCase "1 epoch, all batches" 1 99 nnMnistLoss 250 0.02
                  5.469999999999997e-2
  , mnistTestCase "artificial 1 2 3 4" 1 2 nnMnistLoss 3 4
                  0.8972
  , mnistTestCase "artificial 4 3 2 1" 4 3 nnMnistLoss 2 1
                  0.7306
  ]

bigMnistTests :: TestTree
bigMnistTests = testGroup "MNIST tests with a 2-hidden-layer nn"
  [ mnistTestCase2 "1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1452
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

shortCIMnistTests :: TestTree
shortCIMnistTests = testGroup "Short CI MNIST tests"
  [ mnistTestCase "artificial 1 2 3 4" 1 2 nnMnistLoss 3 4
                  0.8972
  , mnistTestCase "artificial 4 3 2 1" 4 3 nnMnistLoss 2 1
                  0.7306
  , mnistTestCase2 "1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1452
  , mnistTestCase2 "artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                   0.8972
  , mnistTestCase2 "artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                   0.7132000000000001
  ]
