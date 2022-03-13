{-# LANGUAGE TypeFamilies #-}
module TestMnistFC
  ( testTrees, shortTestForCITrees, mnistTestCase2T, mnistTestCase2D
  ) where

import Prelude

import           Control.DeepSeq
import           Control.Monad (foldM, when)
import           Data.Coerce (coerce)
import           Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hFlush, stdout)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.OutdatedOptimizer
import HordeAd.Tool.MnistTools

testTrees :: [TestTree]
testTrees = [ dumbMnistTests
            , bigMnistTests
            , vectorMnistTests
            , matrixMnistTests
            , fusedMnistTests
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ dumbMnistTests
                      , shortCIMnistTests
                      ]

sgdShow :: HasDelta r
        => r
        -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> [a]  -- ^ training data
        -> Domain r  -- ^ initial parameters
        -> r
sgdShow gamma f trainData params0 =
  let result = fst $ sgd gamma f trainData (params0, V.empty, V.empty, V.empty)
  in snd $ df (f $ head trainData) result

sgdTestCase :: String
            -> IO [a]
            -> (Int
                -> Int
                -> a
                -> DualNumberVariables Double
                -> DeltaMonadGradient Double (DualNumber Double))
            -> Double
            -> Double
            -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      widthHidden2 = 50
      nParams = lenMnist2 widthHidden widthHidden2
      vec = HM.randomVector 33 HM.Uniform nParams - HM.scalar 0.5
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams, show gamma]
  in testCase name $ do
       trainData <- trainDataIO
       sgdShow gamma (trainWithLoss widthHidden widthHidden2)
                     trainData vec
         @?= expected

mnistTestCase2
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2 prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
               gamma expected =
  let nParams = lenMnist2 widthHidden widthHidden2
      params0 = HM.randomVector 44 HM.Uniform nParams - HM.scalar 0.5
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
                 (!res, _, _, _) =
                   fst $ sgd gamma f chunk (params, V.empty, V.empty, V.empty)
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
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2V prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let nParams = lenMnist2V widthHidden widthHidden2
      nParamsV = lenVectorsMnist2V widthHidden widthHidden2
      params0 = HM.randomVector 44 HM.Uniform nParams - HM.scalar 0.5
      paramsV0 =
        V.imap (\i nPV -> HM.randomVector (44 + nPV + i) HM.Uniform nPV
                          - HM.scalar 0.5)
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
                 (resS, resV, _, _) =
                   fst $ sgd gamma f chunk (params, paramsV, V.empty, V.empty)
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
                -> DualNumberVariables Double
                -> m (DualNumber Double)
nnMnistLossTanh widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist2 tanhAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

nnMnistLossRelu :: DeltaMonad Double m
                => Int
                -> Int
                -> MnistData Double
                -> DualNumberVariables Double
                -> m (DualNumber Double)
nnMnistLossRelu widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist2 reluAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

mnistTestCase2L
  :: String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2L prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, parameters0) =
        initializerFixed 44 0.5 (lenMnistFcnn2L widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains Double
                    -> (Int, [MnistData Double])
                    -> IO (Domains Double)
           runBatch (!params, !paramsV, !paramsL, !paramsX) (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss
                 res = fst $ sgd gamma f chunk
                                 (params, paramsV, paramsL, paramsX)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist2L chunk res
                 testScore = testMnist2L testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> Domains Double
                    -> IO (Domains Double)
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
       res <- runEpoch 1 parameters0
       let testErrorFinal = 1 - testMnist2L testData res
       testErrorFinal @?= expected

mnistTestCase2T
  :: Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2T reallyWriteFile
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 (lenMnistFcnn2L widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runBatch ((!params, !paramsV, !paramsL, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 (!paramsNew, !value) =
                   sgd gamma f chunk (params, paramsV, paramsL, paramsX)
             time <- getPOSIXTime
             return (paramsNew, (time, value) : times)
       let runEpoch :: Int
                    -> (Domains Double, [(POSIXTime, Double)])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runEpoch n params2times | n > epochs = return params2times
           runEpoch n (!params2, !times2) = do
             printf "\n[Epoch %d]\n" n
             let !trainDataShuffled =
                   if n > 1
                   then shuffle (mkStdGen $ n + 5) trainData
                   else trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 1 trainDataShuffled
             res <- foldM runBatch (params2, times2) chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d"
              epochs maxBatches
       timeBefore <- getPOSIXTime
       (res, times) <- runEpoch 1 (parameters0, [])
       let ppTime (t, l) = init (show (t - timeBefore)) ++ " " ++ show l
       when reallyWriteFile $
         writeFile "walltimeLoss.txt" $ unlines $ map ppTime times
       let testErrorFinal = 1 - testMnist2L testData res
       testErrorFinal @?= expected

mnistTestCase2D
  :: Bool
  -> Int
  -> Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2D reallyWriteFile miniBatchSize decay
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma0 expected =
  let np = lenMnistFcnn2L widthHidden widthHidden2
      ((nParams, nParamsV, nParamsL), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 np
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show gamma0, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runBatch ((!params, !paramsV, !paramsL, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 gamma = if decay
                         then gamma0 * exp (- fromIntegral k * 1e-4)
                         else gamma0
                 (!paramsNew, !value) =
                   sgdBatchForward (33 + k * 7) miniBatchSize gamma f chunk
                                   (params, paramsV, paramsL, paramsX) np
             time <- getPOSIXTime
             return (paramsNew, (time, value) : times)
       let runEpoch :: Int
                    -> (Domains Double, [(POSIXTime, Double)])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runEpoch n params2times | n > epochs = return params2times
           runEpoch n (!params2, !times2) = do
             printf "\n[Epoch %d]\n" n
             let !trainDataShuffled =
                   if n > 1
                   then shuffle (mkStdGen $ n + 5) trainData
                   else trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf miniBatchSize trainDataShuffled
             res <- foldM runBatch (params2, times2) chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d"
              epochs maxBatches
       timeBefore <- getPOSIXTime
       (res, times) <- runEpoch 1 (parameters0, [])
       let ppTime (t, l) = init (show (t - timeBefore)) ++ " " ++ show l
       when reallyWriteFile $
         writeFile "walltimeLoss.txt" $ unlines $ map ppTime times
       let testErrorFinal = 1 - testMnist2L testData res
       testErrorFinal @?= expected

mnistTestCase2F
  :: Bool
  -> Int
  -> Bool
  -> String
  -> Int
  -> Int
  -> (MnistData (Forward Double)
      -> DualNumberVariables (Forward Double)
      -> DeltaMonadForward (Forward Double) (DualNumber (Forward Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2F reallyWriteFile miniBatchSize decay
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma0 expected =
  let np = lenMnistFcnn2L widthHidden widthHidden2
      ((nParams, nParamsV, nParamsL), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 np
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show gamma0, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = coerce $ force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData (Forward Double)])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runBatch ((!params, !paramsV, !paramsL, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 gamma = if decay
                         then gamma0 * exp (- fromIntegral k * 1e-4)
                         else gamma0
                 (!paramsNew, !value) =
                   sgdBatchFastForward (33 + k * 7) miniBatchSize gamma f chunk
                                       (params, paramsV, paramsL, paramsX) np
             time <- getPOSIXTime
             return (paramsNew, (time, value) : times)
       let runEpoch :: Int
                    -> (Domains Double, [(POSIXTime, Double)])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runEpoch n params2times | n > epochs = return params2times
           runEpoch n (!params2, !times2) = do
             printf "\n[Epoch %d]\n" n
             let !trainDataShuffled =
                   if n > 1
                   then shuffle (mkStdGen $ n + 5) trainData
                   else trainData
                 chunks = take maxBatches
                          $ zip [1 ..]
                          $ chunksOf miniBatchSize trainDataShuffled
             res <- foldM runBatch (params2, times2) chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d"
              epochs maxBatches
       timeBefore <- getPOSIXTime
       (res, times) <- runEpoch 1 (parameters0, [])
       let ppTime (t, l) = init (show (t - timeBefore)) ++ " " ++ show l
       when reallyWriteFile $
         writeFile "walltimeLoss.txt" $ unlines $ map ppTime times
       let testErrorFinal = 1 - testMnist2L testData res
       testErrorFinal @?= expected

dumbMnistTests :: TestTree
dumbMnistTests = testGroup "Dumb MNIST tests"
  [ testCase "1pretty-print in grey 3 2" $ do
      let (nParams, lParamsV, lParamsL) = lenMnistFcnn2L 4 3
          vParamsV = V.fromList lParamsV
          vParamsL = V.fromList lParamsL
          params = V.replicate nParams (1 :: Float)
          paramsV = V.map (`V.replicate` 2) vParamsV
          paramsL = V.map (HM.konst 3) vParamsL
          blackGlyph = V.replicate sizeMnistGlyph 4
          blackLabel = V.replicate sizeMnistLabel 5
          trainData = (blackGlyph, blackLabel)
          output = prettyPrintDf False (nnMnistLoss2L trainData)
                                 (params, paramsV, paramsL, V.empty)
      -- printf "%s" output
      length output @?= 13348
  , testCase "2pretty-print in grey 3 2 fused" $ do
      let (nParams, lParamsV, lParamsL) = lenMnistFcnn2L 4 3
          vParamsV = V.fromList lParamsV
          vParamsL = V.fromList lParamsL
          params = V.replicate nParams (1 :: Float)
          paramsV = V.map (`V.replicate` 2) vParamsV
          paramsL = V.map (HM.konst 3) vParamsL
          blackGlyph = V.replicate sizeMnistGlyph 4
          blackLabel = V.replicate sizeMnistLabel 5
          trainData = (blackGlyph, blackLabel)
          output = prettyPrintDf True (nnMnistLossFused2L trainData)
                                 (params, paramsV, paramsL, V.empty)
      --- printf "%s" output
      length output @?= 12431
  , testCase "3pretty-print on testset 3 2" $ do
      let (_, _, _, parameters0) = initializerFixed 44 0.5 (lenMnistFcnn2L 4 3)
      testData <- loadMnistData testGlyphsPath testLabelsPath
      let trainDataItem = head testData
          output = prettyPrintDf True (nnMnistLoss2L trainDataItem) parameters0
      -- printf "%s" output
      length output @?= 16449
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        blackLabel = V.replicate sizeMnistLabel 0
        trainData = replicate 10 (blackGlyph, blackLabel)
    in sgdTestCase "black"
         (return trainData) nnMnistLoss2 0.02 (-0.0)
  , let whiteGlyph = V.replicate sizeMnistGlyph 1
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 20 (whiteGlyph, whiteLabel)
    in sgdTestCase "white"
         (return trainData) nnMnistLoss2 0.02 23.02585095418536
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 50 (blackGlyph, whiteLabel)
    in sgdTestCase "black/white"
         (return trainData) nnMnistLoss2 0.02 23.025850929940457
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        trainData = map ((\g -> (glyph g, label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "random 100"
         (return trainData) nnMnistLoss2 0.02 11.089140063760212
  , sgdTestCase "first 100 trainset samples only"
      (take 100 <$> loadMnistData trainGlyphsPath trainLabelsPath)
      nnMnistLoss2 0.02 3.233123290489956
  , testCase "testMnist2 on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2 300 100
          params = V.replicate nParams 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2 300 100 testData params) @?= 0.902
  , testCase "testMnist2VV on 0.1 params 300 100 width 10k testset" $ do
      let nParams = lenMnist2V 300 100
          params = V.replicate nParams 0.1
          nParamsV = lenVectorsMnist2V 300 100
          paramsV = V.map (`V.replicate` 0.1) nParamsV
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2V 300 100 testData (params, paramsV)) @?= 0.902
  , testCase "testMnist2LL on 0.1 params 300 100 width 10k testset" $ do
      let (nParams, lParamsV, lParamsL) = lenMnistFcnn2L 300 100
          vParamsV = V.fromList lParamsV
          vParamsL = V.fromList lParamsL
          params = V.replicate nParams 0.1
          paramsV = V.map (`V.replicate` 0.1) vParamsV
          paramsL = V.map (HM.konst 0.1) vParamsL
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2L testData (params, paramsV, paramsL, V.empty)) @?= 0.902
 ]

bigMnistTests :: TestTree
bigMnistTests = testGroup "MNIST tests with a 2-hidden-layer nn"
  [ mnistTestCase2 "1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1269
  , mnistTestCase2 "tanh: 1 epoch, 1 batch" 1 1 nnMnistLossTanh 300 100 0.02
                   0.6406000000000001
  , mnistTestCase2 "relu: 1 epoch, 1 batch" 1 1 nnMnistLossRelu 300 100 0.02
                   0.7248
  , mnistTestCase2 "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2 500 150 0.02
                   0.1269
  , mnistTestCase2 "2 epochs, but only 1 batch" 2 1 nnMnistLoss2 300 100 0.02
                   9.809999999999997e-2
  , mnistTestCase2 "artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                   0.8972
  , mnistTestCase2 "artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                   0.8991
  ]

vectorMnistTests :: TestTree
vectorMnistTests = testGroup "MNIST VV tests with a 2-hidden-layer nn"
  [ mnistTestCase2V "1 epoch, 1 batch" 1 1 nnMnistLoss2V 300 100 0.02
                    0.12960000000000005
  , mnistTestCase2V "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2V 500 150 0.02
                    0.13959999999999995
  , mnistTestCase2V "2 epochs, but only 1 batch" 2 1 nnMnistLoss2V 300 100 0.02
                    0.10019999999999996
  , mnistTestCase2V "1 epoch, all batches" 1 99 nnMnistLoss2V 300 100 0.02
                    5.389999999999995e-2
  , mnistTestCase2V "artificial 1 2 3 4 5" 1 2 nnMnistLoss2V 3 4 5
                    0.8972
  , mnistTestCase2V "artificial 5 4 3 2 1" 5 4 nnMnistLoss2V 3 2 1
                    0.7756000000000001
  ]

matrixMnistTests :: TestTree
matrixMnistTests = testGroup "MNIST LL tests with a 2-hidden-layer nn"
  [ mnistTestCase2L "1 epoch, 1 batch" 1 1 nnMnistLoss2L 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2L 500 150 0.02
                    0.15039999999999998
  , mnistTestCase2L "2 epochs, but only 1 batch" 2 1 nnMnistLoss2L 300 100 0.02
                    8.879999999999999e-2
  , mnistTestCase2L "1 epoch, all batches" 1 99 nnMnistLoss2L 300 100 0.02
                    5.6599999999999984e-2
  , mnistTestCase2L "artificial 1 2 3 4 5" 1 2 nnMnistLoss2L 3 4 5
                    5.1100000000000034e-2
  , mnistTestCase2T False
                    "artificial TL 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.8865
  , mnistTestCase2D False 1 False
                    "artificial DL 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.8991
  , mnistTestCase2F False 1 False
                    "artificial FDL 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.8991
--  , mnistTestCase2T True False
--                    "2 epochs, all batches, TL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 0.02
--                    4.290000000000005e-2
--  , mnistTestCase2D True 1 False
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 0.02
--                    0.9079
--  , mnistTestCase2D True 64 False
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 0.02
--                    0.9261
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 0.02
--                    0.8993
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 2e-5
--                    0.9423
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 2e-4
--                    0.8714
--  , mnistTestCase2F True 64 True
--                    "2 epochs, all batches, FDL, wider, to file"
--                    2 60000 nnMnistLoss2L 500 150 2e-4
--                    0.8714
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLossFusedRelu2L 1024 1024 2e-4
--                    0.902
--  , mnistTestCase2D False 64 True
--                    "2 epochs, all batches, DL"
--                    2 60000 nnMnistLoss2L 1024 1024 2e-4
--                    0.7465999999999999
--  , mnistTestCase2F False 64 True
--                    "2 epochs, all batches, FDL"
--                    2 60000 nnMnistLoss2L 1024 1024 2e-4
--                    0.7465999999999999
  ]

fusedMnistTests :: TestTree
fusedMnistTests = testGroup "MNIST fused LL tests with a 2-hidden-layer nn"
  [ mnistTestCase2L "1 epoch, 1 batch" 1 1 nnMnistLossFused2L 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "1 epoch, 1 batch, wider" 1 1
                    nnMnistLossFused2L 500 150 0.02
                    0.15039999999999998
  , mnistTestCase2L "2 epochs, but only 1 batch" 2 1
                    nnMnistLossFused2L 300 100 0.02
                    8.879999999999999e-2
  , mnistTestCase2L "1 epoch, all batches" 1 99 nnMnistLossFused2L 300 100 0.02
                    5.1100000000000034e-2
  , mnistTestCase2L "artificial 1 2 3 4 5" 1 2 nnMnistLossFused2L 3 4 5
                    0.8972
  , mnistTestCase2L "artificial 5 4 3 2 1" 5 4 nnMnistLossFused2L 3 2 1
                    0.8207
  ]

shortCIMnistTests :: TestTree
shortCIMnistTests = testGroup "Short CI MNIST tests"
  [ mnistTestCase2 "2 - 1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                   0.1269
  , mnistTestCase2 "2 artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                   0.8972
  , mnistTestCase2 "2 artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                   0.8991
  , mnistTestCase2V "VV 1 epoch, 1 batch" 1 1 nnMnistLoss2V 300 100 0.02
                    0.12960000000000005
  , mnistTestCase2V "VV artificial 1 2 3 4 5" 1 2 nnMnistLoss2V 3 4 5
                    0.8972
  , mnistTestCase2V "VV artificial 5 4 3 2 1" 5 4 nnMnistLoss2V 3 2 1
                    0.7756000000000001
  , mnistTestCase2L "LL 1 epoch, 1 batch" 1 1 nnMnistLoss2L 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "LL artificial 1 2 3 4 5" 1 2 nnMnistLoss2L 3 4 5
                    0.8972
  , mnistTestCase2L "LL artificial 5 4 3 2 1" 5 4 nnMnistLoss2L 3 2 1
                    0.8085
  , mnistTestCase2L "fused LL 1/1 batch" 1 1 nnMnistLossFused2L 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "fused LL artificial 1 2 3 4 5" 1 2 nnMnistLossFused2L 3 4 5
                    0.8972
  , mnistTestCase2T False
                    "fused TL artificial 5 4 3 2 1" 5 4 nnMnistLossFused2L 3 2 1
                    0.8865
  , mnistTestCase2D False 1 False
                    "fused DL artificial 5 4 3 2 1" 5 4 nnMnistLossFused2L 3 2 1
                    0.8991
  ]
