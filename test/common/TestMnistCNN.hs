{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestMnistCNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Arrow (first)
import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal, type (<=))
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck hiding (label, scale, shuffle)
import           Text.Printf

import HordeAd
import HordeAd.Core.DualClass (HasRanks (dKonst2), IsPrimal (dZero))
import HordeAd.Tool.MnistCnnShaped
import HordeAd.Tool.MnistData

import TestCommon
import TestCommonEqEpsilon

testTrees :: [TestTree]
testTrees = [ mnistCNNTestsShort
            , mnistCNNTestsLong
            ] ++ comparisonTests 30


shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ mnistCNNTestsShort
                      ] ++ comparisonTests 7

-- * The simplest possible convolutional net, based on
-- https://www.ritchieng.com/machine-learning/deep-learning/tensorflow/convnets/#Problem-1
-- but with different initialization and no batches and the picture size
-- evolves differently (@conv2@ used instead of @convSame2@). Theirs is not
-- real convolution but, most likely, correlation, and their padding
-- only preserves size, while ours in @conv2@ increases it,
-- not to put less weigth onto information from the outer rows and columns.

patch_size, depth0, num_hidden0, final_image_size :: Int
patch_size = 5
depth0 = 16
num_hidden0 = 64
final_image_size = 10  -- if size was not increased: 7, see below

lenMnistCNN :: Int -> Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
lenMnistCNN final_image_sz depth num_hidden =
  ( depth + depth
  , [num_hidden, sizeMnistLabel]
  , replicate (depth + depth * depth) (patch_size, patch_size)
    ++ [(num_hidden, final_image_sz * final_image_sz * depth)]
    ++ [(sizeMnistLabel, num_hidden)]
  , []
  )

-- This is simple convolution with depth 1.
convDataMnistCNN :: IsScalar d r
                 => DualNumberInputs d r -> Matrix r -> Int
                 -> DualNumber d (Matrix r)
convDataMnistCNN inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) = conv2 ker (D x (dKonst2 dZero (HM.size x)))  -- == (scalar x)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNN :: IsScalar d r
                   => Int -> DualNumberInputs d r
                   -> [DualNumber d (Matrix r)] -> Int
                   -> DualNumber d (Matrix r)
convMiddleMnistCNN depth inputs ms1 k =
  let conv (m, n) =
        let ker = at2 inputs ((1 + k) * depth + n)
        in conv2 ker m
      ms2 = map conv $ zip ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

convMnistCNN :: IsScalar d r
             => Int -> Matrix r  -- 28x28
             -> DualNumberInputs d r
             -> DualNumber d (Vector r)
convMnistCNN depth x inputs =
  let ms1 = map (convDataMnistCNN inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNN depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (seq1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNN :: IsScalar d r
                 => Int -> MnistData2 r
                 -> DualNumberInputs d r
                 -> DualNumber d r
convMnistLossCNN depth (x, target) inputs =
  let result = convMnistCNN depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNN
  :: forall r. IsScalar 'DModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNN depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNN depth glyph xs
              in softMaxV m
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNN :: Int -> [MnistData2 Double] -> Domains Double -> Double #-}

-- Here, unlike in
-- https://www.ritchieng.com/machine-learning/deep-learning/tensorflow/convnets/#Problem-1
-- we don't batch yet.
convMnistTestCaseCNN
  :: String
  -> Int
  -> Int
  -> (Int
      -> MnistData2 Double
      -> DualNumberInputs 'DModeGradient Double
      -> DualNumber 'DModeGradient Double)
  -> (Int -> [MnistData2 Double]-> Domains Double -> Double)
  -> Int
  -> Int
  -> Int
  -> Double
  -> Double
  -> TestTree
convMnistTestCaseCNN prefix epochs maxBatches trainWithLoss testLoss
                     final_image_sz widthHidden widthHidden2 gamma expected =
  let ( (nParams0, nParams1, nParams2, nParamsX)
       , totalParams, range, parameters0 ) =
        initializerFixed 44 0.05
        (lenMnistCNN final_image_sz widthHidden widthHidden2)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show widthHidden, show widthHidden2
                        , show nParams0, show nParams1, show nParams2
                        , show nParamsX
                        , show totalParams, show gamma, show range]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       trainData <- loadMnistData2 trainGlyphsPath trainLabelsPath
       testData <- loadMnistData2 testGlyphsPath testLabelsPath
       -- Mimic how backprop tests and display it, even though tests
       -- should not print, in principle.
       let runBatch :: Domains Double
                    -> (Int, [MnistData2 Double])
                    -> IO (Domains Double)
           runBatch (!params0, !params1, !params2, !paramsX) (k, chunk) = do
             let f = trainWithLoss widthHidden
             res <- fst <$> sgd gamma f chunk
                                (params0, params1, params2, paramsX)
             let !trainScore = testLoss widthHidden chunk res
                 !testScore = testLoss widthHidden testData res
                 !lenChunk = length chunk
             hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
             hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
             hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
       let runEpoch :: Int
                    -> Domains Double
                    -> IO (Domains Double)
           runEpoch n params2 | n > epochs = return params2
           runEpoch n params2 = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch params2 chunks
             runEpoch (succ n) res
       res <- runEpoch 1 parameters0
       let testErrorFinal = 1 - testLoss widthHidden testData res
       testErrorFinal @?~ expected


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
convDataMnistCNNS :: IsScalar d r
                  => DualNumberInputs d r -> Matrix r -> Int
                  -> DualNumber d (Matrix r)
convDataMnistCNNS inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) = convSame2 ker (constant x)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNS :: IsScalar d r
                    => Int -> DualNumberInputs d r
                    -> [DualNumber d (Matrix r)] -> Int
                    -> DualNumber d (Matrix r)
convMiddleMnistCNNS depth inputs ms1 k =
  let conv (m, n) =
        let ker = at2 inputs ((1 + k) * depth + n)
        in convSame2 ker m
      ms2 = map conv $ zip ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

convMnistCNNS :: IsScalar d r
              => Int -> Matrix r  -- 28x28
              -> DualNumberInputs d r
              -> DualNumber d (Vector r)
convMnistCNNS depth x inputs =
  let ms1 = map (convDataMnistCNNS inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNNS depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (seq1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNS :: IsScalar d r
                  => Int -> MnistData2 r
                  -> DualNumberInputs d r
                  -> DualNumber d r
convMnistLossCNNS depth (x, target) inputs =
  let result = convMnistCNNS depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNNS
  :: forall r. IsScalar 'DModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNNS depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNNS depth glyph xs
              in softMaxV m
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNNS :: Int -> [MnistData2 Double] -> Domains Double -> Double #-}


-- * A variant of @convMnistCNN@ with @conv2'@.

-- This is simple convolution with depth 1.
convDataMnistCNNP :: IsScalar d r
                  => DualNumberInputs d r -> Matrix r -> Int
                  -> DualNumber d (Matrix r)
convDataMnistCNNP inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) =
        conv2' ker (D x (dKonst2 dZero (HM.size x)))  -- == (scalar x)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNP :: IsScalar d r
                    => Int -> DualNumberInputs d r
                    -> [DualNumber d (Matrix r)] -> Int
                    -> DualNumber d (Matrix r)
convMiddleMnistCNNP depth inputs ms1 k =
  let conv (m, n) =
        let ker = at2 inputs ((1 + k) * depth + n)
        in conv2' ker m
      ms2 = map conv $ zip ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (HM.size u)
  in maxPool2 2 2 yRelu

convMnistCNNP :: IsScalar d r
              => Int -> Matrix r  -- 28x28
              -> DualNumberInputs d r
              -> DualNumber d (Vector r)
convMnistCNNP depth x inputs =
  let ms1 = map (convDataMnistCNNP inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNNP depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (seq1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNP :: IsScalar d r
                  => Int -> MnistData2 r
                  -> DualNumberInputs d r
                  -> DualNumber d r
convMnistLossCNNP depth (x, target) inputs =
  let result = convMnistCNNP depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNNP
  :: forall r. IsScalar 'DModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNNP depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNNP depth glyph xs
              in softMaxV m
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNNP :: Int -> [MnistData2 Double] -> Domains Double -> Double #-}


-- * A variant of @convMnistCNN@ with shaped tensors, including mini-batches

convMnistTestCaseCNNT
  :: forall kheight_minus_1 kwidth_minus_1 num_hidden out_channels
            in_height in_width batch_size d r.
     ( KnownNat kheight_minus_1, KnownNat kwidth_minus_1
     , KnownNat num_hidden, KnownNat out_channels
     , KnownNat in_height, KnownNat in_width, KnownNat batch_size
     , 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , r ~ Double, d ~ 'DModeGradient )
  => String
  -> Int
  -> Int
  -> (forall kheight_minus_1' kwidth_minus_1' num_hidden' out_channels'
             in_height' in_width' batch_size'.
      ( KnownNat kheight_minus_1', KnownNat kwidth_minus_1'
      , KnownNat num_hidden', KnownNat out_channels'
      , KnownNat in_height', KnownNat in_width', KnownNat batch_size'
      , 1 <= kheight_minus_1'
      , 1 <= kwidth_minus_1'
      , IsScalar d r )
      => Proxy kheight_minus_1'
      -> Proxy kwidth_minus_1'
      -> Proxy num_hidden'
      -> Proxy out_channels'
      -> ( OS.Array '[batch_size', in_height', in_width'] r
         , OS.Array '[batch_size', SizeMnistLabel] r )
      -> DualNumberInputs d r
      -> DualNumber d r)
  -> (forall kheight_minus_1' kwidth_minus_1' num_hidden' out_channels'
             in_height' in_width'.
      ( KnownNat kheight_minus_1', KnownNat kwidth_minus_1'
      , KnownNat num_hidden', KnownNat out_channels'
      , KnownNat in_height', KnownNat in_width'
      , 1 <= kheight_minus_1'
      , 1 <= kwidth_minus_1'
      , IsScalar d r )
      => Proxy kheight_minus_1'
      -> Proxy kwidth_minus_1'
      -> Proxy num_hidden'
      -> Proxy out_channels'
      -> [( OS.Array '[in_height', in_width'] r
          , OS.Array '[SizeMnistLabel] r )]
      -> Domains r
      -> r)
  -> (forall kheight_minus_1' kwidth_minus_1' num_hidden' out_channels'
             in_height' in_width'.
      ( KnownNat kheight_minus_1', KnownNat kwidth_minus_1'
      , KnownNat num_hidden', KnownNat out_channels'
      , KnownNat in_height', KnownNat in_width' )
      => Proxy kheight_minus_1'
      -> Proxy kwidth_minus_1'
      -> Proxy num_hidden'
      -> Proxy out_channels'
      -> Proxy in_height'
      -> Proxy in_width'
      -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> Double
  -> TestTree
convMnistTestCaseCNNT prefix epochs maxBatches trainWithLoss ftest flen
                      gamma expected =
  let proxy_kheight_minus_1 = Proxy @kheight_minus_1
      proxy_kwidth_minus_1 = Proxy @kwidth_minus_1
      proxy_num_hidden = Proxy @num_hidden
      proxy_out_channels  = Proxy @out_channels
      proxy_in_height = Proxy @in_height
      proxy_in_width = Proxy @in_width
      batch_size = valueOf @batch_size
      ((_, _, _, nParamsX), totalParams, range, parametersInit) =
        initializerFixed 44 0.05
          (flen proxy_kheight_minus_1 proxy_kwidth_minus_1
                proxy_num_hidden proxy_out_channels
                proxy_in_height proxy_in_width)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (valueOf @num_hidden :: Int), show batch_size
                        , show nParamsX, show totalParams
                        , show gamma, show range ]
      packBatchS :: [( OS.Array '[in_height, in_width] r
                    , OS.Array '[SizeMnistLabel] r )]
                -> ( OS.Array '[batch_size, in_height, in_width] r
                   , OS.Array '[batch_size, SizeMnistLabel] r )
      packBatchS l =
        let (inputs, targets) = unzip l
        in (OS.ravel $ OSB.fromList inputs, OS.ravel $ OSB.fromList targets)
      shapeBatchS :: MnistData r
                  -> ( OS.Array '[in_height, in_width] r
                     , OS.Array '[SizeMnistLabel] r )
      shapeBatchS (input, target) = (OS.fromVector input, OS.fromVector target)
  in testCase name $ do
    hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
           prefix epochs maxBatches
    trainData <- map shapeBatchS
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- take 100  -- TODO: reduced for now, because too slow
                . map shapeBatchS
                <$> loadMnistData testGlyphsPath testLabelsPath
     -- There is some visual feedback, because some of these take long.
    let runBatch :: Domains r
                 -> (Int, [( OS.Array '[in_height, in_width] r
                           , OS.Array '[SizeMnistLabel] r )])
                 -> IO (Domains r)
        runBatch parameters@(!_, !_, !_, !_) (k, chunk) = do
          let f = trainWithLoss proxy_kheight_minus_1 proxy_kwidth_minus_1
                                proxy_num_hidden proxy_out_channels
              chunkS = map packBatchS
                       $ filter (\ch -> length ch >= batch_size)
                       $ chunksOf batch_size chunk
          res <- fst <$> sgd gamma f chunkS parameters
          let !trainScore = ftest proxy_kheight_minus_1 proxy_kwidth_minus_1
                                  proxy_num_hidden proxy_out_channels
                                  chunk res
              !testScore = ftest proxy_kheight_minus_1 proxy_kwidth_minus_1
                                 proxy_num_hidden proxy_out_channels
                                 testData res
              !lenChunk = length chunk
          hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
          hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
          hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
          return res
    let runEpoch :: Int -> Domains r -> IO (Domains r)
        runEpoch n params2 | n > epochs = return params2
        runEpoch n params2 = do
          hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..]
                       $ chunksOf (2 * batch_size) trainDataShuffled
                           -- TODO: (10 * batch_size) takes forever
          !res <- foldM runBatch params2 chunks
          runEpoch (succ n) res
    res <- runEpoch 1 parametersInit
    let testErrorFinal = 1 - ftest proxy_kheight_minus_1 proxy_kwidth_minus_1
                                   proxy_num_hidden proxy_out_channels
                                   testData res
    testErrorFinal @?~ expected

mnistCNNTestsLong :: TestTree
mnistCNNTestsLong = testGroup "MNIST CNN long tests"
  [ {-convMnistTestCaseCNN "artificial 5 4 3 2 1" 5 4
                         convMnistLossCNN convMnistTestCNN final_image_size
                         3 2 1 0.8991
  , convMnistTestCaseCNN "S artificial 5 4 3 2 1" 5 4
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         3 2 1 0.8991
  , -}convMnistTestCaseCNN "P artificial 5 4 3 2 1" 5 4
                         convMnistLossCNNP convMnistTestCNNP final_image_size
                         3 2 1 0.8991
  , convMnistTestCaseCNNT @4 @4 @2 @3 @SizeMnistHeight @SizeMnistWidth @1
                          "T artificial 5 4 3 2 1" 5 4
                          convMnistLossFusedS convMnistTestS convMnistLenS
                          0.02 0.98
  , convMnistTestCaseCNN "1 epoch 1 batch" 1 1
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 5.989999999999995e-2
{-
  , convMnistTestCaseCNN "2 epochs but only 1 batch" 2 1
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 8.879999999999999e-2  -- dummy results everywhere
  , convMnistTestCaseCNN "1 epoch all batches" 1 99
                         convMnistLossCNN convMnistTestCNN
                         final_image_size depth0 num_hidden0
                         0.02 5.1100000000000034e-2
-}
  , convMnistTestCaseCNN "S1 epoch 1 batch" 1 1
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 4.800000000000004e-2
{-
  , convMnistTestCaseCNN "S2 epochs but only 1 batch" 2 1
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 8.879999999999999e-2
  , convMnistTestCaseCNN "S1 epoch all batches" 1 99
                         convMnistLossCNNS convMnistTestCNNS
                         final_image_sizeS depth0 num_hidden0
                         0.02 5.1100000000000034e-2
-}
  , convMnistTestCaseCNN "P1 epoch 1 batch" 1 1
                         convMnistLossCNNP convMnistTestCNNP
                         final_image_size depth0 num_hidden0
                         0.02 5.989999999999995e-2
{-
  , convMnistTestCaseCNN "P2 epochs but only 1 batch" 2 1
                         convMnistLossCNNP convMnistTestCNNP
                         final_image_size depth0 num_hidden0
                         0.02 4.94e-2
  , convMnistTestCaseCNN "P1 epoch all batches" 1 99
                         convMnistLossCNNP convMnistTestCNNP
                         final_image_size depth0 num_hidden0
                         0.02 2.7000000000000024e-2
-}
  , convMnistTestCaseCNNT @4 @4 @64 @16 @SizeMnistHeight @SizeMnistWidth @16
                          "T1 epoch 1 batch" 1 1
                          convMnistLossFusedS convMnistTestS convMnistLenS
                          0.02 0.8200000000000001
  ]

mnistCNNTestsShort :: TestTree
mnistCNNTestsShort = testGroup "MNIST CNN short tests"
  [ convMnistTestCaseCNN "artificial 1 1 1 1 1" 1 1
                         convMnistLossCNN convMnistTestCNN final_image_size
                         1 1 1 0.9026
  , convMnistTestCaseCNN "S artificial 1 1 1 1 1" 1 1
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         1 1 1 0.9026
  , convMnistTestCaseCNN "P artificial 1 1 1 1 1" 1 1
                         convMnistLossCNNP convMnistTestCNNP final_image_size
                         1 1 1 0.9026
  , convMnistTestCaseCNNT @4 @4 @1 @1 @SizeMnistHeight @SizeMnistWidth @1
                          "T artificial 1 1 1 1 1" 1 1
                          convMnistLossFusedS convMnistTestS convMnistLenS
                          1 0.85
{-
  , convMnistTestCaseCNN "artificial 1 2 3 4 5" 1 2
                         convMnistLossCNN convMnistTestCNN final_image_size
                         3 4 5 0.902
  , convMnistTestCaseCNN "S artificial 1 2 3 4 5" 1 2
                         convMnistLossCNNS convMnistTestCNNS final_image_sizeS
                         3 4 5 0.902
  , convMnistTestCaseCNN "P artificial 1 2 3 4 5" 1 2
                         convMnistLossCNNP convMnistTestCNNP final_image_size
                         3 4 5 0.8972
-}
  , convMnistTestCaseCNNT @4 @4 @4 @3 @SizeMnistHeight @SizeMnistWidth @5
                          "T artificial 1 2 3 4 5" 1 2
                          convMnistLossFusedS convMnistTestS convMnistLenS
                          6 0.92
  ]

comparisonTests :: Int -> [TestTree]
comparisonTests volume =
 [ testProperty "Compare gradients and two forward derivatives for a single 2d convolution implemented twice" $
      forAll (choose (1, 30)) $ \seed ->
      forAll (choose (1, 50)) $ \seedDs ->
      forAll (choose (1, 5 * volume)) $ \widthHidden ->
      forAll (choose (1, 8 * volume)) $ \widthHidden2 ->
      forAll (choose (0, seed + widthHidden - 2)) $ \ix1 ->
      forAll (choose (0, seedDs + widthHidden2 - 2)) $ \ix2 ->
      forAll (choose (0.01, 10)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let paramShape =
              (0, [], [(seed, widthHidden2), (widthHidden, seedDs)], [])
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds) = initializerFixed seedDs rangeDs paramShape
            (_, _, _, parametersPerturbation) =
              initializerFixed (seed + seedDs) 1e-7 paramShape
            f, fP :: forall d r. (IsScalar d r)
                  => DualNumberInputs d r -> DualNumber d r
            f inputs =
              let ker = at2 inputs 0
                  x = at2 inputs 1
                  c = conv2 ker x
                  cx = from2X c
                  cx1 = indexX cx ix1
                  cx2 = indexX cx1 ix2
              in fromX0 cx2
            fP inputs =
              let ker = at2 inputs 0
                  x = at2 inputs 1
                  c = conv2' ker x
                  cx = from2X c
                  cx1 = indexX cx ix1
                  cx2 = indexX cx1 ix2
              in fromX0 cx2
        in ioProperty (qcPropDom f parameters ds parametersPerturbation 1)
           .&&. ioProperty (qcPropDom fP parameters ds parametersPerturbation 1)
           .&&. cmpTwoSimple f fP parameters ds
  , testProperty "Compare gradients and two forward derivatives for 3 implementations of CNN MNIST" $
      \seed ->
      forAll (choose (0, sizeMnistLabel - 1)) $ \seedDs ->
      forAll (choose (1, volume)) $ \depth ->
      forAll (choose (1, volume)) $ \num_hidden ->
      forAll (choose (0.01, 0.5)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = HM.randomVector seedV HM.Uniform n
            glyph = HM.reshape 28 $ createRandomVector (28 * 28) seed
            label = HM.konst 0 sizeMnistLabel V.// [(seedDs, 1)]
            mnistData :: MnistData2 Double
            mnistData = (glyph, label)
            paramShape = lenMnistCNN final_image_size depth num_hidden
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds) = initializerFixed seedDs rangeDs paramShape
            (_, _, _, parametersPerturbation) =
              initializerFixed (seed + seedDs) 1e-7 paramShape
            f, fP, fT :: forall d r. (IsScalar d r, r ~ Double)
                      => DualNumberInputs d r -> DualNumber d r
            f = convMnistLossCNN depth mnistData
            fP = convMnistLossCNNP depth mnistData
            fT = case ( someNatVal $ toInteger num_hidden
                      , someNatVal $ toInteger depth ) of
              ( Just (SomeNat proxy_num_hidden)
               ,Just (SomeNat proxy_out_channel) ) ->
                convMnistLossFusedS (Proxy @4) (Proxy @4)
                                    proxy_num_hidden proxy_out_channel
                                    (packBatch @1 [shapeBatch
                                                  $ first HM.flatten mnistData])
              _ -> error "fT panic"
            paramsToT (p0, p1, p2, _) =
              let qX = V.fromList
                    [ OT.fromVector [depth, 1, 5, 5]
                      $ V.concat $ map HM.flatten
                      $ take depth $ V.toList p2
                    , OT.fromVector [depth] $ V.take depth p0
                    , OT.fromVector [depth, depth, 5, 5]
                      $ V.concat $ map HM.flatten
                      $ take (depth * depth) (drop depth $ V.toList p2)
                    , OT.fromVector [depth] $ V.drop depth p0
                    , let m = p2 V.! (depth + depth * depth)
                      in OT.fromVector [num_hidden, HM.cols m]
                         $ HM.flatten m
                    , OT.fromVector [num_hidden] $ p1 V.! 0
                    , OT.fromVector [sizeMnistLabel, num_hidden]
                      $ HM.flatten
                      $ p2 V.! (depth + depth * depth + 1)
                    , OT.fromVector [sizeMnistLabel] $ p1 V.! 1
                    ]
              in (V.empty, V.empty, V.empty, qX)
            parametersT = paramsToT parameters
            dsT = paramsToT ds
            parametersPerturbationT = paramsToT parametersPerturbation
        in ioProperty (qcPropDom f parameters ds parametersPerturbation 1)
           .&&. ioProperty
                  (qcPropDom fP parameters ds parametersPerturbation 1)
           .&&. ioProperty
                  (qcPropDom fT parametersT dsT parametersPerturbationT 1)
           .&&. cmpTwoSimple f fP parameters ds
           .&&. cmpTwo f fT parameters parametersT ds dsT
  ]
