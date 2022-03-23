{-# LANGUAGE TypeFamilies #-}
module TestMnistFC
  ( testTrees, shortTestForCITrees, mnistTestCase2T, mnistTestCase2D
  ) where

import Prelude

import           Control.DeepSeq
import           Control.Monad (foldM, when)
import           Data.Coerce (coerce)
import           Data.Proxy (Proxy (Proxy))
import           Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hFlush, stdout)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf
import           Test.Tasty.QuickCheck hiding (shuffle, label)
import qualified Data.Array.DynamicS as OT

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
        => Primal r
        -> (a -> DualNumberVariables r -> DualMonadGradient r (DualNumber r))
        -> [a]  -- ^ training data
        -> Domain0 r  -- ^ initial parameters
        -> Primal r
sgdShow gamma f trainData params0Init =
  let result =
        fst $ sgd gamma f trainData (params0Init, V.empty, V.empty, V.empty)
  in snd $ df (f $ head trainData) result

sgdTestCase :: String
            -> IO [a]
            -> (Int
                -> Int
                -> a
                -> DualNumberVariables (Delta0 Double)
                -> DualMonadGradient (Delta0 Double)
                                     (DualNumber (Delta0 Double)))
            -> Double
            -> Double
            -> TestTree
sgdTestCase prefix trainDataIO trainWithLoss gamma expected =
  let widthHidden = 250
      widthHidden2 = 50
      nParams0 = lenMnist0 widthHidden widthHidden2
      vec = HM.randomVector 33 HM.Uniform nParams0 - HM.scalar 0.5
      name = prefix ++ " "
             ++ unwords [show widthHidden, show nParams0, show gamma]
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
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2 prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
               gamma expected =
  let nParams0 = lenMnist0 widthHidden widthHidden2
      params0Init = HM.randomVector 44 HM.Uniform nParams0 - HM.scalar 0.5
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show gamma ]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domain0 Double -> (Int, [MnistData Double])
                    -> IO (Domain0 Double)
           runBatch !params0 (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss widthHidden widthHidden2
                 (!res, _, _, _) =
                   fst $ sgd gamma f chunk (params0, V.empty, V.empty, V.empty)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist0 (Proxy @(Delta0 Double))
                                         widthHidden widthHidden2 chunk res
                 testScore  = testMnist0 (Proxy @(Delta0 Double))
                                         widthHidden widthHidden2 testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> Domain0 Double -> IO (Domain0 Double)
           runEpoch n params0 | n > epochs = return params0
           runEpoch n params0 = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params0 chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 params0Init
       let testErrorFinal = 1 - testMnist0 (Proxy @(Delta0 Double)) widthHidden widthHidden2 testData res
       testErrorFinal @?= expected

mnistTestCase2V
  :: String
  -> Int
  -> Int
  -> (Int
      -> Int
      -> MnistData Double
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2V prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let nParams0 = lenMnist1 widthHidden widthHidden2
      nParams1 = lenVectorsMnist1 widthHidden widthHidden2
      params0Init = HM.randomVector 44 HM.Uniform nParams0 - HM.scalar 0.5
      params1Init =
        V.imap (\i nPV -> HM.randomVector (44 + nPV + i) HM.Uniform nPV
                          - HM.scalar 0.5)
               nParams1
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show (V.length nParams1)
                        , show (V.sum nParams1 + nParams0), show gamma ]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domain0 Double, Domain1 Double)
                    -> (Int, [MnistData Double])
                    -> IO (Domain0 Double, Domain1 Double)
           runBatch (!params0, !params1) (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss widthHidden widthHidden2
                 (resS, resV, _, _) =
                   fst $ sgd gamma f chunk (params0, params1, V.empty, V.empty)
                 res = (resS, resV)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist1 @(Delta0 Double)
                                         widthHidden widthHidden2 chunk res
                 testScore = testMnist1 @(Delta0 Double)
                                        widthHidden widthHidden2 testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int -> (Domain0 Double, Domain1 Double)
                    -> IO (Domain0 Double, Domain1 Double)
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
       res <- runEpoch 1 (params0Init, params1Init)
       let testErrorFinal =
             1 - testMnist1 @(Delta0 Double) widthHidden widthHidden2 testData
                            res
       testErrorFinal @?= expected

nnMnistLossTanh :: DualMonad (Delta0 Double) m
                => Int
                -> Int
                -> MnistData Double
                -> DualNumberVariables (Delta0 Double)
                -> m (DualNumber (Delta0 Double))
nnMnistLossTanh widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist0 tanhAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

nnMnistLossRelu :: DualMonad (Delta0 Double) m
                => Int
                -> Int
                -> MnistData Double
                -> DualNumberVariables (Delta0 Double)
                -> m (DualNumber (Delta0 Double))
nnMnistLossRelu widthHidden widthHidden2 (xs, targ) vec = do
  res <- nnMnist0 reluAct softMaxAct widthHidden widthHidden2 xs vec
  lossCrossEntropy targ res

mnistTestCase2L
  :: String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2L prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let ((nParams0, nParams1, nParams2), totalParams, range, parameters0) =
        initializerFixed 44 0.5 (lenMnistFcnn2 widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       trainData <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains (Delta0 Double)
                    -> (Int, [MnistData Double])
                    -> IO (Domains (Delta0 Double))
           runBatch (!params0, !params1, !params2, !paramsX) (k, chunk) = do
             printf "(Batch %d)\n" k
             let f = trainWithLoss
                 res = fst $ sgd gamma f chunk
                                 (params0, params1, params2, paramsX)
             printf "Trained on %d points.\n" (length chunk)
             let trainScore = testMnist2 @(Delta0 Double) chunk res
                 testScore = testMnist2 @(Delta0 Double) testData res
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> Domains (Delta0 Double)
                    -> IO (Domains (Delta0 Double))
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
       let testErrorFinal = 1 - testMnist2 @(Delta0 Double) testData res
       testErrorFinal @?= expected

mnistTestCase2T
  :: Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2T reallyWriteFile
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma expected =
  let ((nParams0, nParams1, nParams2), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 (lenMnistFcnn2 widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains (Delta0 Double), [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (Domains (Delta0 Double), [(POSIXTime, Double)])
           runBatch ((!params0, !params1, !params2, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 (!params0New, !value) =
                   sgd gamma f chunk (params0, params1, params2, paramsX)
             time <- getPOSIXTime
             return (params0New, (time, value) : times)
       let runEpoch :: Int
                    -> (Domains (Delta0 Double), [(POSIXTime, Double)])
                    -> IO (Domains (Delta0 Double), [(POSIXTime, Double)])
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
       let testErrorFinal = 1 - testMnist2 @(Delta0 Double) testData res
       testErrorFinal @?= expected

mnistTestCase2D
  :: Bool
  -> Int
  -> Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2D reallyWriteFile miniBatchSize decay
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma0 expected =
  let np = lenMnistFcnn2 widthHidden widthHidden2
      ((nParams0, nParams1, nParams2), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 np
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma0, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains (Delta0 Double), [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (Domains (Delta0 Double), [(POSIXTime, Double)])
           runBatch ((!params0, !params1, !params2, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 gamma = if decay
                         then gamma0 * exp (- fromIntegral k * 1e-4)
                         else gamma0
                 (!params0New, !value) =
                   sgdBatchForward (33 + k * 7) miniBatchSize gamma f chunk
                                   (params0, params1, params2, paramsX) np
             time <- getPOSIXTime
             return (params0New, (time, value) : times)
       let runEpoch :: Int
                    -> (Domains (Delta0 Double), [(POSIXTime, Double)])
                    -> IO (Domains (Delta0 Double), [(POSIXTime, Double)])
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
       let testErrorFinal = 1 - testMnist2 @(Delta0 Double) testData res
       testErrorFinal @?= expected

mnistTestCase2F
  :: Bool
  -> Int
  -> Bool
  -> String
  -> Int
  -> Int
  -> (MnistData Double
      -> DualNumberVariables Double
      -> DualMonadForward Double (DualNumber Double))
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
mnistTestCase2F reallyWriteFile miniBatchSize decay
                prefix epochs maxBatches trainWithLoss widthHidden widthHidden2
                gamma0 expected =
  let np = lenMnistFcnn2 widthHidden widthHidden2
      ((nParams0, nParams1, nParams2), totalParams, range, !parameters0) =
        initializerFixed 44 0.5 np
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma0, show range]
  in testCase name $ do
       trainData0 <- loadMnistData trainGlyphsPath trainLabelsPath
       testData <- loadMnistData testGlyphsPath testLabelsPath
       let !trainData = coerce $ force $ shuffle (mkStdGen 6) trainData0
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: (Domains Double, [(POSIXTime, Double)])
                    -> (Int, [MnistData Double])
                    -> IO (Domains Double, [(POSIXTime, Double)])
           runBatch ((!params0, !params1, !params2, !paramsX), !times)
                    (k, chunk) = do
             when (k `mod` 100 == 0) $ do
               printf "%d " k
               hFlush stdout
             let f = trainWithLoss
                 gamma = if decay
                         then gamma0 * exp (- fromIntegral k * 1e-4)
                         else gamma0
                 (!params0New, !value) =
                   sgdBatchFastForward (33 + k * 7) miniBatchSize gamma f chunk
                                       (params0, params1, params2, paramsX) np
             time <- getPOSIXTime
             return (params0New, (time, value) : times)
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
       let testErrorFinal = 1 - testMnist2 @(Delta0 Double) testData res
       testErrorFinal @?= expected

dumbMnistTests :: TestTree
dumbMnistTests = testGroup "Dumb MNIST tests"
  [ testCase "1pretty-print in grey 3 2" $ do
      let (nParams0, lParams1, lParams2) = lenMnistFcnn2 4 3
          vParams1 = V.fromList lParams1
          vParams2 = V.fromList lParams2
          params0 = V.replicate nParams0 (1 :: Float)
          params1 = V.map (`V.replicate` 2) vParams1
          params2 = V.map (HM.konst 3) vParams2
          blackGlyph = V.replicate sizeMnistGlyph 4
          blackLabel = V.replicate sizeMnistLabel 5
          trainData = (blackGlyph, blackLabel)
          output = prettyPrintDf False (nnMnistLoss2 trainData)
                                 (params0, params1, params2, V.empty)
      -- printf "%s" output
      length output @?= 13348
  , testCase "2pretty-print in grey 3 2 fused" $ do
      let (nParams0, lParams1, lParams2) = lenMnistFcnn2 4 3
          vParams1 = V.fromList lParams1
          vParams2 = V.fromList lParams2
          params0 = V.replicate nParams0 (1 :: Float)
          params1 = V.map (`V.replicate` 2) vParams1
          params2 = V.map (HM.konst 3) vParams2
          blackGlyph = V.replicate sizeMnistGlyph 4
          blackLabel = V.replicate sizeMnistLabel 5
          trainData = (blackGlyph, blackLabel)
          output = prettyPrintDf True (nnMnistLossFused2 trainData)
                                 (params0, params1, params2, V.empty)
      --- printf "%s" output
      length output @?= 12431
  , testCase "3pretty-print on testset 3 2" $ do
      let (_, _, _, parameters0) = initializerFixed 44 0.5 (lenMnistFcnn2 4 3)
      testData <- loadMnistData testGlyphsPath testLabelsPath
      let trainDataItem = head testData
          output = prettyPrintDf True (nnMnistLoss2 trainDataItem) parameters0
      -- printf "%s" output
      length output @?= 16449
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        blackLabel = V.replicate sizeMnistLabel 0
        trainData = replicate 10 (blackGlyph, blackLabel)
    in sgdTestCase "black"
         (return trainData) nnMnistLoss0 0.02 (-0.0)
  , let whiteGlyph = V.replicate sizeMnistGlyph 1
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 20 (whiteGlyph, whiteLabel)
    in sgdTestCase "white"
         (return trainData) nnMnistLoss0 0.02 23.02585095418536
  , let blackGlyph = V.replicate sizeMnistGlyph 0
        whiteLabel = V.replicate sizeMnistLabel 1
        trainData = replicate 50 (blackGlyph, whiteLabel)
    in sgdTestCase "black/white"
         (return trainData) nnMnistLoss0 0.02 23.025850929940457
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        trainData = map ((\g -> (glyph g, label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "random 100"
         (return trainData) nnMnistLoss0 0.02 11.089140063760212
  , sgdTestCase "first 100 trainset samples only"
      (take 100 <$> loadMnistData trainGlyphsPath trainLabelsPath)
      nnMnistLoss0 0.02 3.233123290489956
  , testCase "testMnist0 on 0.1 params0 300 100 width 10k testset" $ do
      let nParams0 = lenMnist0 300 100
          params0 = V.replicate nParams0 0.1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist0 (Proxy @(Delta0 Double)) 300 100 testData params0)
        @?= 0.902
  , testCase "testMnist2VV on 0.1 params0 300 100 width 10k testset" $ do
      let nParams0 = lenMnist1 300 100
          params0 = V.replicate nParams0 0.1
          nParams1 = lenVectorsMnist1 300 100
          params1 = V.map (`V.replicate` 0.1) nParams1
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist1 @(Delta0 Double) 300 100 testData (params0, params1))
        @?= 0.902
  , testCase "testMnist2LL on 0.1 params0 300 100 width 10k testset" $ do
      let (nParams0, lParams1, lParams2) = lenMnistFcnn2 300 100
          vParams1 = V.fromList lParams1
          vParams2 = V.fromList lParams2
          params0 = V.replicate nParams0 0.1
          params1 = V.map (`V.replicate` 0.1) vParams1
          params2 = V.map (HM.konst 0.1) vParams2
      testData <- loadMnistData testGlyphsPath testLabelsPath
      (1 - testMnist2 @(Delta0 Double) testData
                      (params0, params1, params2, V.empty))
        @?= 0.902
  , testProperty "Compare two forward derivatives and gradient for Mnist0" $
      \seed -> \seedDs ->
      forAll (choose (1, 300)) $ \widthHidden ->
      forAll (choose (1, 100)) $ \widthHidden2 ->
      forAll (choose (0.01, 10)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = createRandomVector sizeMnistGlyph seed
            label = createRandomVector sizeMnistLabel seedDs
            mnistData :: MnistData Double
            mnistData = (glyph, label)
            nParams0 = lenMnist0 widthHidden widthHidden2
            paramShape = (nParams0, [], [])
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds@(ds0, ds1, ds2, dsX)) =
              initializerFixed seedDs rangeDs paramShape
            f :: forall r m. (DualMonad r m, Primal r ~ Double)
              => DualNumberVariables r -> m (DualNumber r)
            f = nnMnistLoss0 widthHidden widthHidden2 mnistData
            ff = dfastForward f parameters ds
            close a b = abs (a - b) <= 0.000001
            close1 (a1, b1) (a2, b2) = close a1 a2 .&&. b1 === b2
            dfDot fDot psDot =
              let ((res0, res1, res2, resX), value) = df fDot psDot
              in ( res0 HM.<.> ds0
                   + V.sum (V.zipWith (HM.<.>) res1 ds1)
                   + V.sum (V.zipWith (HM.<.>) (V.map HM.flatten res2)
                                               (V.map HM.flatten ds2))
                   + V.sum (V.zipWith (HM.<.>) (V.map OT.toVector resX)
                                               (V.map OT.toVector dsX))
                 , value )
        -- The formula for comparing derivative and gradient is due to @awf at
        -- https://github.com/Mikolaj/horde-ad/issues/15#issuecomment-1063251319
        in dforward f parameters ds === ff
           .&&. close1 (dfDot f parameters) ff
  , testProperty "Compare two forward derivatives and gradient for Mnist1" $
      \seed -> \seedDs ->
      forAll (choose (1, 2000)) $ \widthHidden ->
      forAll (choose (1, 5000)) $ \widthHidden2 ->
      forAll (choose (0.01, 0.5)) $ \range ->  -- large nn, so NaNs fast
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = createRandomVector sizeMnistGlyph seed
            label = createRandomVector sizeMnistLabel seedDs
            mnistData :: MnistData Double
            mnistData = (glyph, label)
            nParams0 = lenMnist1 widthHidden widthHidden2
            nParams1 = lenVectorsMnist1 widthHidden widthHidden2
            paramShape = (nParams0, V.toList nParams1, [])
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds@(ds0, ds1, ds2, dsX)) =
              initializerFixed seedDs rangeDs paramShape
            f :: forall r m. (DualMonad r m, Primal r ~ Double)
              => DualNumberVariables r -> m (DualNumber r)
            f = nnMnistLoss1 widthHidden widthHidden2 mnistData
            ff = dfastForward f parameters ds
            close a b = abs (a - b) <= 0.000001
            close1 (a1, b1) (a2, b2) = close a1 a2 .&&. b1 === b2
            dfDot fDot psDot =
              let ((res0, res1, res2, resX), value) = df fDot psDot
              in ( res0 HM.<.> ds0
                   + V.sum (V.zipWith (HM.<.>) res1 ds1)
                   + V.sum (V.zipWith (HM.<.>) (V.map HM.flatten res2)
                                               (V.map HM.flatten ds2))
                   + V.sum (V.zipWith (HM.<.>) (V.map OT.toVector resX)
                                               (V.map OT.toVector dsX))
                 , value )
        in dforward f parameters ds === ff
           .&&. close1 (dfDot f parameters) ff
  , testProperty "Compare two forward derivatives and gradient for Mnist2" $
      \seed ->
      forAll (choose (0, sizeMnistLabel - 1)) $ \seedDs ->
      forAll (choose (1, 5000)) $ \widthHidden ->
      forAll (choose (1, 1000)) $ \widthHidden2 ->
      forAll (choose (0.01, 1)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = createRandomVector sizeMnistGlyph seed
            label = createRandomVector sizeMnistLabel seedDs
            labelOneHot = HM.konst 0 sizeMnistLabel V.// [(seedDs, 1)]
            mnistData, mnistDataOneHot :: MnistData Double
            mnistData = (glyph, label)
            mnistDataOneHot = (glyph, labelOneHot)
            paramShape = lenMnistFcnn2 widthHidden widthHidden2
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds@(ds0, ds1, ds2, dsX)) =
              initializerFixed seedDs rangeDs paramShape
            f, fOneHot, fFused
              :: forall r m. (DualMonad r m, Primal r ~ Double)
                 => DualNumberVariables r -> m (DualNumber r)
            f = nnMnistLoss2 mnistData
            fOneHot = nnMnistLoss2 mnistDataOneHot
            fFused = nnMnistLossFused2 mnistDataOneHot
            ff = dfastForward f parameters ds
            ffOneHot = dfastForward fOneHot parameters ds
            ffFused = dfastForward fFused parameters ds
            close a b = abs (a - b) <= 0.000001
            close1 (a1, b1) (a2, b2) = close a1 a2 .&&. b1 === b2
            dfDot fDot psDot =
              let ((res0, res1, res2, resX), value) = df fDot psDot
              in ( res0 HM.<.> ds0
                   + V.sum (V.zipWith (HM.<.>) res1 ds1)
                   + V.sum (V.zipWith (HM.<.>) (V.map HM.flatten res2)
                                               (V.map HM.flatten ds2))
                   + V.sum (V.zipWith (HM.<.>) (V.map OT.toVector resX)
                                               (V.map OT.toVector dsX))
                 , value )
        in dforward f parameters ds === ff
           .&&. close1 (dfDot f parameters) ff
           .&&. dforward fOneHot parameters ds === ffOneHot
           .&&. close1 (dfDot fOneHot parameters) ffOneHot
           .&&. close1 ffOneHot ffFused
           .&&. dforward fFused parameters ds === ffFused
           .&&. close1 (dfDot fFused parameters) ffFused ]

bigMnistTests :: TestTree
bigMnistTests = testGroup "MNIST tests with a 2-hidden-layer nn"
  [ mnistTestCase2 "1 epoch, 1 batch" 1 1 nnMnistLoss0 300 100 0.02
                   0.1269
  , mnistTestCase2 "tanh: 1 epoch, 1 batch" 1 1 nnMnistLossTanh 300 100 0.02
                   0.6406000000000001
  , mnistTestCase2 "relu: 1 epoch, 1 batch" 1 1 nnMnistLossRelu 300 100 0.02
                   0.7248
  , mnistTestCase2 "1 epoch, 1 batch, wider" 1 1 nnMnistLoss0 500 150 0.02
                   0.1269
  , mnistTestCase2 "2 epochs, but only 1 batch" 2 1 nnMnistLoss0 300 100 0.02
                   9.809999999999997e-2
  , mnistTestCase2 "artificial 1 2 3 4 5" 1 2 nnMnistLoss0 3 4 5
                   0.8972
  , mnistTestCase2 "artificial 5 4 3 2 1" 5 4 nnMnistLoss0 3 2 1
                   0.8991
  ]

vectorMnistTests :: TestTree
vectorMnistTests = testGroup "MNIST VV tests with a 2-hidden-layer nn"
  [ mnistTestCase2V "1 epoch, 1 batch" 1 1 nnMnistLoss1 300 100 0.02
                    0.12960000000000005
  , mnistTestCase2V "1 epoch, 1 batch, wider" 1 1 nnMnistLoss1 500 150 0.02
                    0.13959999999999995
  , mnistTestCase2V "2 epochs, but only 1 batch" 2 1 nnMnistLoss1 300 100 0.02
                    0.10019999999999996
  , mnistTestCase2V "1 epoch, all batches" 1 99 nnMnistLoss1 300 100 0.02
                    5.389999999999995e-2
  , mnistTestCase2V "artificial 1 2 3 4 5" 1 2 nnMnistLoss1 3 4 5
                    0.8972
  , mnistTestCase2V "artificial 5 4 3 2 1" 5 4 nnMnistLoss1 3 2 1
                    0.7756000000000001
  ]

matrixMnistTests :: TestTree
matrixMnistTests = testGroup "MNIST LL tests with a 2-hidden-layer nn"
  [ mnistTestCase2L "1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "1 epoch, 1 batch, wider" 1 1 nnMnistLoss2 500 150 0.02
                    0.15039999999999998
  , mnistTestCase2L "2 epochs, but only 1 batch" 2 1 nnMnistLoss2 300 100 0.02
                    8.879999999999999e-2
  , mnistTestCase2L "1 epoch, all batches" 1 99 nnMnistLoss2 300 100 0.02
                    5.1100000000000034e-2
  , mnistTestCase2L "artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                    0.8972
  , mnistTestCase2T False
                    "artificial TL 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                    0.8865
  , mnistTestCase2D False 1 False
                    "artificial DL 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                    0.8991
  , mnistTestCase2F False 1 False
                    "artificial FL 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                    0.8991
--  , mnistTestCase2T True False
--                    "2 epochs, all batches, TL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 0.02
--                    4.290000000000005e-2
--  , mnistTestCase2D True 1 False
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 0.02
--                    0.9079
--  , mnistTestCase2D True 64 False
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 0.02
--                    0.9261
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 0.02
--                    0.8993
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 2e-5
--                    0.9423
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 2e-4
--                    0.8714
--  , mnistTestCase2F True 64 True
--                    "2 epochs, all batches, FL, wider, to file"
--                    2 60000 nnMnistLoss2 500 150 2e-4
--                    0.8714
--  , mnistTestCase2D True 64 True
--                    "2 epochs, all batches, DL, wider, to file"
--                    2 60000 nnMnistLossFusedRelu2 1024 1024 2e-4
--                    0.902
--  , mnistTestCase2D False 64 True
--                    "2 epochs, all batches, 1024DL"
--                    2 60000 nnMnistLoss2 1024 1024 2e-4
--                    0.7465999999999999
--  , mnistTestCase2F False 64 True
--                    "2 epochs, all batches, 1024FL"
--                    2 60000 nnMnistLoss2 1024 1024 2e-4
--                    0.7465999999999999
  ]

fusedMnistTests :: TestTree
fusedMnistTests = testGroup "MNIST fused LL tests with a 2-hidden-layer nn"
  [ mnistTestCase2L "1 epoch, 1 batch" 1 1 nnMnistLossFused2 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "1 epoch, 1 batch, wider" 1 1
                    nnMnistLossFused2 500 150 0.02
                    0.15039999999999998
  , mnistTestCase2L "2 epochs, but only 1 batch" 2 1
                    nnMnistLossFused2 300 100 0.02
                    8.879999999999999e-2
  , mnistTestCase2L "1 epoch, all batches" 1 99 nnMnistLossFused2 300 100 0.02
                    5.1100000000000034e-2
  , mnistTestCase2L "artificial 1 2 3 4 5" 1 2 nnMnistLossFused2 3 4 5
                    0.8972
  , mnistTestCase2L "artificial 5 4 3 2 1" 5 4 nnMnistLossFused2 3 2 1
                    0.8207
  ]

shortCIMnistTests :: TestTree
shortCIMnistTests = testGroup "Short CI MNIST tests"
  [ mnistTestCase2 "2 - 1 epoch, 1 batch" 1 1 nnMnistLoss0 300 100 0.02
                   0.1269
  , mnistTestCase2 "2 artificial 1 2 3 4 5" 1 2 nnMnistLoss0 3 4 5
                   0.8972
  , mnistTestCase2 "2 artificial 5 4 3 2 1" 5 4 nnMnistLoss0 3 2 1
                   0.8991
  , mnistTestCase2V "VV 1 epoch, 1 batch" 1 1 nnMnistLoss1 300 100 0.02
                    0.12960000000000005
  , mnistTestCase2V "VV artificial 1 2 3 4 5" 1 2 nnMnistLoss1 3 4 5
                    0.8972
  , mnistTestCase2V "VV artificial 5 4 3 2 1" 5 4 nnMnistLoss1 3 2 1
                    0.7756000000000001
  , mnistTestCase2L "LL 1 epoch, 1 batch" 1 1 nnMnistLoss2 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "LL artificial 1 2 3 4 5" 1 2 nnMnistLoss2 3 4 5
                    0.8972
  , mnistTestCase2L "LL artificial 5 4 3 2 1" 5 4 nnMnistLoss2 3 2 1
                    0.8085
  , mnistTestCase2L "fused LL 1/1 batch" 1 1 nnMnistLossFused2 300 100 0.02
                    0.12339999999999995
  , mnistTestCase2L "fused LL artificial 1 2 3 4 5" 1 2 nnMnistLossFused2 3 4 5
                    0.8972
  , mnistTestCase2T False
                    "fused TL artificial 5 4 3 2 1" 5 4 nnMnistLossFused2 3 2 1
                    0.8865
  , mnistTestCase2D False 1 False
                    "fused DL artificial 5 4 3 2 1" 5 4 nnMnistLossFused2 3 2 1
                    0.8991
  ]
