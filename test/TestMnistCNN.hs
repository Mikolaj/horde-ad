{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-unused-imports #-}
module TestMnistCNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import qualified Numeric.LinearAlgebra as HM
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck hiding (label, shuffle)
import           Text.Printf

import HordeAd
import HordeAd.Tool.MnistTools

testTrees :: [TestTree]
testTrees = [ mnistCNNTestsShort
            , mnistCNNTestsLong
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ mnistCNNTestsShort
                      ]

-- * The simplest possible convolutional net, based on
-- https://www.ritchieng.com/machine-learning/deep-learning/tensorflow/convnets/#Problem-1
-- but with different initialization and no batches and the picture size
-- evolves differently (@conv2@ used instead of @convSame2@). Theirs is not
-- real convolution but, most likely, correlation, and their padding
-- only preserves size, while ours in @conv2@ increases it,
-- not to put less weigth onto information from the outer rows and columns.

patch_size, _batch_size, depth0, num_hidden0, final_image_size:: Int
patch_size = 5
_batch_size = 16
depth0 = 16
num_hidden0 = 64
final_image_size = 10  -- if size was not increased: 7, see below

lenMnistCNN :: Int -> Int -> Int -> (Int, [Int], [(Int, Int)])
lenMnistCNN final_image_sz depth num_hidden =
  ( depth + depth
  , [num_hidden, sizeMnistLabel]
  , replicate (depth + depth * depth) (patch_size, patch_size)
    ++ [(num_hidden, final_image_sz * final_image_sz * depth)]
    ++ [(sizeMnistLabel, num_hidden)]
  )

-- This is simple convolution with depth 1.
convDataMnistCNN :: DualMonad r m
                 => DualNumberVariables r -> Primal (Tensor2 r) -> Int
                 -> m (DualNumber (Tensor2 r))
convDataMnistCNN variables x offset = do
  let ker = var2 variables offset
      bias = var0 variables offset
  yConv@(D u _) <- conv2 ker (D x (dKonst2 dZero (HM.size x)))  -- == (scalar x)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNN :: DualMonad r m
                   => Int -> DualNumberVariables r
                   -> [DualNumber (Tensor2 r)] -> Int
                   -> m (DualNumber (Tensor2 r))
convMiddleMnistCNN depth variables ms1 k = do
  let conv (m, n) = do
        let ker = var2 variables ((1 + k) * depth + n)
        conv2 ker m
  ms2 <- mapM conv $ zip ms1 [0 ..]
  yConv@(D u _) <- returnLet $ sum ms2
  let bias = var0 variables (depth + k)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

convMnistCNN :: DualMonad r m
             => Int -> Primal (Tensor2 r)  -- 28x28
             -> DualNumberVariables r
             -> m (DualNumber (Tensor1 r))
convMnistCNN depth x variables = do
  ms1 <- mapM (convDataMnistCNN variables x) [0 .. depth - 1]
  ms3 <- mapM (convMiddleMnistCNN depth variables ms1) [0 .. depth - 1]
  let flattenAppend m acc = append1 (flatten1 m) acc
  v <- returnLet $ foldr flattenAppend (seq1 V.empty) ms3
  let weigthsDense = var2 variables (depth + depth * depth)
      biasesDense = var1 variables 0
      denseLayer = weigthsDense #>! v + biasesDense
  denseRelu <- reluAct1 denseLayer
  let weigthsReadout = var2 variables (depth + depth * depth + 1)
      biasesReadout = var1 variables 1
  returnLet $ weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNN :: (DualMonad r m, Floating (Primal (Tensor1 r)))
                 => Int -> MnistData2 (Primal r)
                 -> DualNumberVariables r
                 -> m (DualNumber r)
convMnistLossCNN depth (x, target) variables = do
  result <- convMnistCNN depth x variables
  lossSoftMaxCrossEntropyV target result

convMnistTestCNN
  :: forall r. IsScalar r
  => Proxy r -> Int -> [MnistData2 (Primal r)] -> Domains r -> Primal r
convMnistTestCNN _ depth inputs parameters =
  let matchesLabels :: MnistData2 (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = convMnistCNN depth glyph
            value = primalValue @r nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNN :: Proxy (Delta0 Double) -> Int -> [MnistData2 Double] -> Domains (Delta0 Double) -> Double #-}

-- Here, unlike in
-- https://www.ritchieng.com/machine-learning/deep-learning/tensorflow/convnets/#Problem-1
-- we don't batch yet.
convMnistTestCaseCNN
  :: String
  -> Int
  -> Int
  -> (Int
      -> MnistData2 Double
      -> DualNumberVariables (Delta0 Double)
      -> DualMonadGradient (Delta0 Double) (DualNumber (Delta0 Double)))
  -> (Proxy (Delta0 Double) -> Int -> [MnistData2 Double]
      -> Domains (Delta0 Double) -> Double)
  -> Int
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
convMnistTestCaseCNN prefix epochs maxBatches trainWithLoss testLoss
                     final_image_sz widthHidden widthHidden2 gamma expected =
  let ((nParams0, nParams1, nParams2), totalParams, range, parameters0) =
        initializerFixed 44 0.5
        (lenMnistCNN final_image_sz widthHidden widthHidden2)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       trainData <- loadMnistData2 trainGlyphsPath trainLabelsPath
       testData <- loadMnistData2 testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains (Delta0 Double)
                    -> (Int, [MnistData2 Double])
                    -> IO (Domains (Delta0 Double))
           runBatch (!params0, !params1, !params2, !paramsX) (k, chunk) = do
             printf "(Batch %d with %d points)\n" k (length chunk)
             let f = trainWithLoss widthHidden
                 res = fst $ sgd gamma f chunk
                                 (params0, params1, params2, paramsX)
                 trainScore = testLoss (Proxy @(Delta0 Double))
                                       widthHidden chunk res
                 testScore = testLoss (Proxy @(Delta0 Double))
                                      widthHidden testData res
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
       let testErrorFinal = 1 - testLoss (Proxy @(Delta0 Double))
                                         widthHidden testData res
       testErrorFinal @?= expected

-- * Another flavour of the simplest possible convolutional net, based on
-- https://www.ritchieng.com/machine-learning/deep-learning/tensorflow/convnets/#Problem-1
-- but with different initialization and no batches.
-- Also, if @conv2@ was used instead of @convSame2@,
-- the picture size would evolve differently. Theirs is not
-- real convolution but, most likely, correlation, and their padding
-- only preserves size, while ours in @conv2@ increases it,
-- not to put less weigth onto information from the outer rows and columns.

final_image_sizeS :: Int
final_image_sizeS = 7

-- This is simple convolution with depth 1.
convDataMnistCNNS :: DualMonad r m
                  => DualNumberVariables r -> Primal (Tensor2 r) -> Int
                  -> m (DualNumber (Tensor2 r))
convDataMnistCNNS variables x offset = do
  let ker = var2 variables offset
      bias = var0 variables offset
  yConv@(D u _) <- convSame2 ker (scalar x)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNS :: DualMonad r m
                    => Int -> DualNumberVariables r
                    -> [DualNumber (Tensor2 r)] -> Int
                    -> m (DualNumber (Tensor2 r))
convMiddleMnistCNNS depth variables ms1 k = do
  let conv (m, n) = do
        let ker = var2 variables ((1 + k) * depth + n)
        convSame2 ker m
  ms2 <- mapM conv $ zip ms1 [0 ..]
  yConv@(D u _) <- returnLet $ sum ms2
  let bias = var0 variables (depth + k)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

convMnistCNNS :: DualMonad r m
              => Int -> Primal (Tensor2 r)  -- 28x28
              -> DualNumberVariables r
              -> m (DualNumber (Tensor1 r))
convMnistCNNS depth x variables = do
  ms1 <- mapM (convDataMnistCNNS variables x) [0 .. depth - 1]
  ms3 <- mapM (convMiddleMnistCNNS depth variables ms1) [0 .. depth - 1]
  let flattenAppend m acc = append1 (flatten1 m) acc
  v <- returnLet $ foldr flattenAppend (seq1 V.empty) ms3
  let weigthsDense = var2 variables (depth + depth * depth)
      biasesDense = var1 variables 0
      denseLayer = weigthsDense #>! v + biasesDense
  denseRelu <- reluAct1 denseLayer
  let weigthsReadout = var2 variables (depth + depth * depth + 1)
      biasesReadout = var1 variables 1
  returnLet $ weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNS :: (DualMonad r m, Floating (Primal (Tensor1 r)))
                  => Int -> MnistData2 (Primal r)
                  -> DualNumberVariables r
                  -> m (DualNumber r)
convMnistLossCNNS depth (x, target) variables = do
  result <- convMnistCNNS depth x variables
  lossSoftMaxCrossEntropyV target result

convMnistTestCNNS
  :: forall r. IsScalar r
  => Proxy r -> Int -> [MnistData2 (Primal r)] -> Domains r -> Primal r
convMnistTestCNNS _ depth inputs parameters =
  let matchesLabels :: MnistData2 (Primal r) -> Bool
      matchesLabels (glyph, label) =
        let nn = convMnistCNNS depth glyph
            value = primalValue @r nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNNS :: Proxy (Delta0 Double) -> Int -> [MnistData2 Double] -> Domains (Delta0 Double) -> Double #-}

-- * A variant of @convMnistCNN@ with @conv2'@.

-- This is simple convolution with depth 1.
convDataMnistCNNP :: DualMonad r m
                  => DualNumberVariables r -> Primal (Tensor2 r) -> Int
                  -> m (DualNumber (Tensor2 r))
convDataMnistCNNP variables x offset = do
  let ker = var2 variables offset
      bias = var0 variables offset
  yConv@(D u _) <-
    returnLet $ conv2' ker (D x (dKonst2 dZero (HM.size x)))  -- == (scalar x)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNP :: DualMonad r m
                    => Int -> DualNumberVariables r
                    -> [DualNumber (Tensor2 r)] -> Int
                    -> m (DualNumber (Tensor2 r))
convMiddleMnistCNNP depth variables ms1 k = do
  let conv (m, n) = do
        let ker = var2 variables ((1 + k) * depth + n)
        returnLet $ conv2' ker m
  ms2 <- mapM conv $ zip ms1 [0 ..]
  yConv@(D u _) <- returnLet $ sum ms2
  let bias = var0 variables (depth + k)
  yRelu <- reluAct2 $ yConv + konst2 bias (HM.size u)
  maxPool2 2 2 yRelu

convMnistCNNP :: DualMonad r m
              => Int -> Primal (Tensor2 r)  -- 28x28
              -> DualNumberVariables r
              -> m (DualNumber (Tensor1 r))
convMnistCNNP depth x variables = do
  ms1 <- mapM (convDataMnistCNNP variables x) [0 .. depth - 1]
  ms3 <- mapM (convMiddleMnistCNNP depth variables ms1) [0 .. depth - 1]
  let flattenAppend m acc = append1 (flatten1 m) acc
  v <- returnLet $ foldr flattenAppend (seq1 V.empty) ms3
  let weigthsDense = var2 variables (depth + depth * depth)
      biasesDense = var1 variables 0
      denseLayer = weigthsDense #>! v + biasesDense
  denseRelu <- reluAct1 denseLayer
  let weigthsReadout = var2 variables (depth + depth * depth + 1)
      biasesReadout = var1 variables 1
  returnLet $ weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNP :: (DualMonad r m, Floating (Primal (Tensor1 r)))
                  => Int -> MnistData2 (Primal r)
                  -> DualNumberVariables r
                  -> m (DualNumber r)
convMnistLossCNNP depth (x, target) variables = do
  result <- convMnistCNNP depth x variables
  lossSoftMaxCrossEntropyV target result

mnistCNNTestsLong :: TestTree
mnistCNNTestsLong = testGroup "MNIST CNN long tests"
  [ {-
    convMnistTestCaseCNN "artificial 5 4 3 2 1" 5 4
                         convMnistLossCNN convMnistTestCNN final_image_size
                         3 2 1 0.8991
  , convMnistTestCaseCNN "S artificial 5 4 3 2 1" 5 4
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         3 2 1 0.8991
  , convMnistTestCaseCNN "1 epoch, 1 batch" 1 1
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 0.12339999999999995  -- dummy results everywhere
  , convMnistTestCaseCNN "2 epochs, but only 1 batch" 2 1
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 8.879999999999999e-2
  , convMnistTestCaseCNN "1 epoch, all batches" 1 99
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 5.1100000000000034e-2
  , convMnistTestCaseCNN "S1 epoch, 1 batch" 1 1
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 0.12339999999999995
  , convMnistTestCaseCNN "S2 epochs, but only 1 batch" 2 1
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 8.879999999999999e-2
  , convMnistTestCaseCNN "S1 epoch, all batches" 1 99
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 5.1100000000000034e-2
  , testProperty "Compare two forward derivatives and gradient for convMnistTestCNN and convMnistTestCNNP" $
      \seed ->
      forAll (choose (0, sizeMnistLabel - 1)) $ \seedDs ->
      forAll (choose (1, 15)) $ \widthHidden ->
      forAll (choose (1, 20)) $ \widthHidden2 ->
      forAll (choose (0.01, 0.5)) $ \range ->
      forAll (choose (0.01, 2)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = HM.reshape 28 $ createRandomVector (28 * 28) seed
            label = HM.konst 0 sizeMnistLabel V.// [(seedDs, 1)]
            mnistData :: MnistData2 Double
            mnistData = (glyph, label)
            paramShape = lenMnistCNN final_image_size widthHidden widthHidden2
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds@(ds0, ds1, ds2, dsX)) =
              initializerFixed seedDs rangeDs paramShape
            f, fP :: forall r m. (DualMonad r m, Primal r ~ Double)
                  => DualNumberVariables r -> m (DualNumber r)
            f = convMnistLossCNN widthHidden mnistData
            fP = convMnistLossCNNP widthHidden mnistData
            ff = dfastForward f parameters ds
            ffP = dfastForward fP parameters ds
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
        in close1 ff ffP
           .&&. dforward f parameters ds === ff
           .&&. close1 (dfDot f parameters) ff
           .&&. dforward fP parameters ds === ffP
-- gradient of fP doesn't have a good definition yet (TODO in Delta.hs)
-- so this fails with "different dimensions 3481 and 25 in dot product":
--         .&&. close1 (dfDot fP parameters) ffP
-}
  ]

mnistCNNTestsShort :: TestTree
mnistCNNTestsShort = testGroup "MNIST CNN short tests"
  [ convMnistTestCaseCNN "artificial 1 1 1 1 1" 1 1
                         convMnistLossCNN convMnistTestCNN final_image_size
                         1 1 1 0.9026
  , convMnistTestCaseCNN "S artificial 1 1 1 1 1" 1 1
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         1 1 1 0.9026
{-
  , convMnistTestCaseCNN "artificial 1 2 3 4 5" 1 2
                         convMnistLossCNN convMnistTestCNN final_image_size
                         3 4 5 0.902
  , convMnistTestCaseCNN "S artificial 1 2 3 4 5" 1 2
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         3 4 5 0.902
-}
  ]
