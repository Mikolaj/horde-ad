{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestMnistCNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Arrow (first)
import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Test.Tasty.QuickCheck hiding (label, scale, shuffle)
import           Text.Printf

import HordeAd
import HordeAd.Core.DualClass (HasRanks (dKonst2), pattern D)
import MnistCnnShaped
import MnistData
import OldMnistCnnShaped

import Tool.EqEpsilon
import Tool.Shared

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
  , [num_hidden, sizeMnistLabelInt]
  , replicate (depth + depth * depth) (patch_size, patch_size)
    ++ [(num_hidden, final_image_sz * final_image_sz * depth)]
    ++ [(sizeMnistLabelInt, num_hidden)]
  , []
  )

-- This is simple convolution with depth 1.
convDataMnistCNN :: ADModeAndNum d r
                 => ADInputs d r -> Matrix r -> Int
                 -> ADVal d (Matrix r)
convDataMnistCNN inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) = conv2 ker (D x (dKonst2 dZero (LA.size x)))  -- == (scalar x)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNN :: ADModeAndNum d r
                   => Int -> ADInputs d r
                   -> [ADVal d (Matrix r)] -> Int
                   -> ADVal d (Matrix r)
convMiddleMnistCNN depth inputs ms1 k =
  let conv m n =
        let ker = at2 inputs ((1 + k) * depth + n)
        in conv2 ker m
      ms2 = zipWith conv ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

convMnistCNN :: ADModeAndNum d r
             => Int -> Matrix r  -- 28x28
             -> ADInputs d r
             -> ADVal d (Vector r)
convMnistCNN depth x inputs =
  let ms1 = map (convDataMnistCNN inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNN depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (fromVector1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNN :: ADModeAndNum d r
                 => Int -> MnistData2 r
                 -> ADInputs d r
                 -> ADVal d r
convMnistLossCNN depth (x, target) inputs =
  let result = convMnistCNN depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNN
  :: forall r. ADModeAndNum 'ADModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNN depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNN depth glyph xs
              in softMaxV m
            v = valueOnDomains nn parameters
        in V.maxIndex v == V.maxIndex label
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
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
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
           runBatch !domains (k, chunk) = do
             let f = trainWithLoss widthHidden
                 res = fst $ sgd gamma f chunk domains
                 !trainScore = testLoss widthHidden chunk res
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
convDataMnistCNNS :: ADModeAndNum d r
                  => ADInputs d r -> Matrix r -> Int
                  -> ADVal d (Matrix r)
convDataMnistCNNS inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) = convSame2 ker (constant x)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNS :: ADModeAndNum d r
                    => Int -> ADInputs d r
                    -> [ADVal d (Matrix r)] -> Int
                    -> ADVal d (Matrix r)
convMiddleMnistCNNS depth inputs ms1 k =
  let conv m n =
        let ker = at2 inputs ((1 + k) * depth + n)
        in convSame2 ker m
      ms2 = zipWith conv ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

convMnistCNNS :: ADModeAndNum d r
              => Int -> Matrix r  -- 28x28
              -> ADInputs d r
              -> ADVal d (Vector r)
convMnistCNNS depth x inputs =
  let ms1 = map (convDataMnistCNNS inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNNS depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (fromVector1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNS :: ADModeAndNum d r
                  => Int -> MnistData2 r
                  -> ADInputs d r
                  -> ADVal d r
convMnistLossCNNS depth (x, target) inputs =
  let result = convMnistCNNS depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNNS
  :: forall r. ADModeAndNum 'ADModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNNS depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNNS depth glyph xs
              in softMaxV m
            v = valueOnDomains nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNNS :: Int -> [MnistData2 Double] -> Domains Double -> Double #-}


-- * A variant of @convMnistCNN@ with @conv2'@.

-- This is simple convolution with depth 1.
convDataMnistCNNP :: ADModeAndNum d r
                  => ADInputs d r -> Matrix r -> Int
                  -> ADVal d (Matrix r)
convDataMnistCNNP inputs x offset =
  let ker = at2 inputs offset
      bias = at0 inputs offset
      yConv@(D u _) =
        conv2' ker (D x (dKonst2 dZero (LA.size x)))  -- == (scalar x)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

-- This simulates convolution of nontrivial depth, without using tensors.
convMiddleMnistCNNP :: ADModeAndNum d r
                    => Int -> ADInputs d r
                    -> [ADVal d (Matrix r)] -> Int
                    -> ADVal d (Matrix r)
convMiddleMnistCNNP depth inputs ms1 k =
  let conv m n =
        let ker = at2 inputs ((1 + k) * depth + n)
        in conv2' ker m
      ms2 = zipWith conv ms1 [0 ..]
      yConv@(D u _) = sum ms2
      bias = at0 inputs (depth + k)
      yRelu = relu $ yConv + konst2 bias (LA.size u)
  in maxPool2 2 2 yRelu

convMnistCNNP :: ADModeAndNum d r
              => Int -> Matrix r  -- 28x28
              -> ADInputs d r
              -> ADVal d (Vector r)
convMnistCNNP depth x inputs =
  let ms1 = map (convDataMnistCNNP inputs x) [0 .. depth - 1]
      ms3 = map (convMiddleMnistCNNP depth inputs ms1) [0 .. depth - 1]
      flattenAppend m = append1 (flatten1 m)
      v = foldr flattenAppend (fromVector1 V.empty) ms3
      weigthsDense = at2 inputs (depth + depth * depth)
      biasesDense = at1 inputs 0
      denseLayer = weigthsDense #>! v + biasesDense
      denseRelu = relu denseLayer
      weigthsReadout = at2 inputs (depth + depth * depth + 1)
      biasesReadout = at1 inputs 1
  in weigthsReadout #>! denseRelu + biasesReadout

convMnistLossCNNP :: ADModeAndNum d r
                  => Int -> MnistData2 r
                  -> ADInputs d r
                  -> ADVal d r
convMnistLossCNNP depth (x, target) inputs =
  let result = convMnistCNNP depth x inputs
  in lossSoftMaxCrossEntropyV target result

convMnistTestCNNP
  :: forall r. ADModeAndNum 'ADModeValue r
  => Int -> [MnistData2 r] -> Domains r -> r
convMnistTestCNNP depth inputs parameters =
  let matchesLabels :: MnistData2 r -> Bool
      matchesLabels (glyph, label) =
        let nn xs =
              let m = convMnistCNNP depth glyph xs
              in softMaxV m
            v = valueOnDomains nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)
{-# SPECIALIZE convMnistTestCNNP :: Int -> [MnistData2 Double] -> Domains Double -> Double #-}


-- * A variant of @convMnistCNN@ with shaped tensors, including mini-batches

convMnistTestCaseCNNT
  :: forall kheight_minus_1 kwidth_minus_1 n_hidden out_channels batch_size r.
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , HasDelta r, ADModeAndNum 'ADModeValue r
     , Random r, PrintfArg r, AssertEqualUpToEpsilon r r )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat n_hidden
  -> StaticNat out_channels
  -> StaticNat batch_size
  -> String
  -> Int
  -> Int
  -> (forall kh kw c_out n_hidden' batch_size'.
      ( 1 <= kh
      , 1 <= kw )
      => StaticNat kh -> StaticNat kw
      -> StaticNat c_out
      -> StaticNat n_hidden' -> StaticNat batch_size'
      -> ( OS.Array '[batch_size', SizeMnistHeight, SizeMnistWidth] r
         , OS.Array '[batch_size', SizeMnistLabel] r )
      -> ADConvMnistParameters kh kw c_out n_hidden' 'ADModeGradient r
      -> ADVal 'ADModeGradient r)
  -> (forall kh kw c_out n_hidden' batch_size'.
      ( 1 <= kh
      , 1 <= kw )
      => StaticNat kh -> StaticNat kw
      -> StaticNat c_out
      -> StaticNat n_hidden' -> StaticNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> ((ADConvMnistParameters kh kw c_out n_hidden'
                                 'ADModeValue r
           -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel, batch_size'] r))
          -> OS.Array '[SizeMnistLabel, batch_size'] r)
      -> r)
  -> r
  -> r
  -> TestTree
convMnistTestCaseCNNT kheight_minus_1@MkSN kwidth_minus_1@MkSN
                      n_hidden@MkSN
                      out_channels@MkSN
                      batch_size@MkSN
                      prefix epochs maxBatches ftrainWithLoss ftestWithParams
                      gamma expected =
  let batchSize = staticNatValue batch_size :: Int
      seed = mkStdGen 44
      range = 0.05
      valsInit
        :: Value (ADConvMnistParameters kheight_minus_1 kwidth_minus_1
                                        out_channels n_hidden 'ADModeGradient r)
      valsInit = fst $ randomVals range seed
      parametersInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (staticNatValue n_hidden :: Int)
                        , show batchSize
                        , show (nParams valsInit)
                        , show (nScalars valsInit)
                        , show gamma, show range ]
      ftrain :: MnistDataBatchS batch_size r
             -> ADInputs 'ADModeGradient r
             -> ADVal 'ADModeGradient r
      ftrain mnist adinputs =
        ftrainWithLoss kheight_minus_1 kwidth_minus_1
                       out_channels
                       n_hidden batch_size
                       mnist (parseADInputs valsInit adinputs)
      ftest :: StaticNat batch_size'
            -> MnistDataBatchS batch_size' r
            -> Domains r
            -> r
      ftest batch_size' mnist testParams =
        ftestWithParams kheight_minus_1 kwidth_minus_1
                        out_channels
                        n_hidden batch_size'
                        mnist (valueAtDomains valsInit testParams)
  in testCase name $ do
    hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
                              prefix epochs maxBatches
    trainData <- map shapeBatch
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- take 100  -- TODO: reduced for now, because too slow
                . map shapeBatch
                <$> loadMnistData testGlyphsPath testLabelsPath
    let testDataS = packBatch @100 testData  -- TODO: @LengthTestData
        -- There is some visual feedback, because some of these take long.
        runBatch :: Domains r
                 -> (Int, [MnistDataS r])
                 -> IO (Domains r)
        runBatch !parameters (k, chunk) = do
          let chunkS = map (packBatch @batch_size)
                       $ filter (\ch -> length ch >= batchSize)
                       $ chunksOf batchSize chunk
              res = fst $ sgd gamma ftrain chunkS parameters
              !trainScore = ftest (MkSN @(10 * batch_size))
                                  (packBatch @(10 * batch_size) chunk)
                                  res
              !testScore = ftest (MkSN @100) testDataS res
              !lenChunk = length chunk
          hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
          hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
          hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
          return res
        runEpoch :: Int -> Domains r -> IO (Domains r)
        runEpoch n params2 | n > epochs = return params2
        runEpoch n params2 = do
          hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..]
                       $ chunksOf (10 * batchSize) trainDataShuffled
          !res <- foldM runBatch params2 chunks
          runEpoch (succ n) res
    res <- runEpoch 1 parametersInit
    let testErrorFinal = 1 - ftest (MkSN @100) testDataS res
    testErrorFinal @?~ expected


-- * An old version of the variant of @convMnistCNN@ with shaped tensors

-- This one depends on convMnistLenS (flen) for random generation
-- of the initial parameters instead of on randomVals.

convMnistTestCaseCNNO
  :: forall kheight_minus_1 kwidth_minus_1 n_hidden out_channels
            in_height in_width batch_size d r.
     ( 1 <= kheight_minus_1
     , 1 <= kwidth_minus_1
     , r ~ Double, d ~ 'ADModeGradient )
  => StaticNat kheight_minus_1 -> StaticNat kwidth_minus_1
  -> StaticNat n_hidden
  -> StaticNat out_channels
  -> StaticNat in_height -> StaticNat in_width
  -> StaticNat batch_size
  -> String
  -> Int
  -> Int
  -> (forall kh kw h w c_out n_hidden' batch_size'.
      ( 1 <= kh
      , 1 <= kw
      , ADModeAndNum d r )
      => StaticNat kh -> StaticNat kw
      -> StaticNat h -> StaticNat w
      -> StaticNat c_out
      -> StaticNat n_hidden' -> StaticNat batch_size'
      -> ( OS.Array '[batch_size', h, w] r
         , OS.Array '[batch_size', SizeMnistLabel] r )
      -> ADInputs d r
      -> ADVal d r)
  -> (forall kh kw h w c_out n_hidden'.
      ( 1 <= kh
      , 1 <= kw
      , ADModeAndNum d r )
      => StaticNat kh -> StaticNat kw
      -> StaticNat h -> StaticNat w
      -> StaticNat c_out
      -> StaticNat n_hidden'
      -> [( OS.Array '[h, w] r
          , OS.Array '[SizeMnistLabel] r )]
      -> Domains r
      -> r)
  -> (forall kh kw h w c_out n_hidden'.
         StaticNat kh -> StaticNat kw
      -> StaticNat h -> StaticNat w
      -> StaticNat c_out
      -> StaticNat n_hidden'
      -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> Double
  -> TestTree
convMnistTestCaseCNNO kheight_minus_1@MkSN kwidth_minus_1@MkSN
                      n_hidden@MkSN
                      out_channels@MkSN
                      in_height@MkSN in_width@MkSN
                      batch_size@MkSN
                      prefix epochs maxBatches trainWithLoss ftest flen
                      gamma expected =
  let batchSize = staticNatValue batch_size :: Int
      ((_, _, _, nParamsX), totalParams, range, parametersInit) =
        initializerFixed 44 0.05
          (flen kheight_minus_1 kwidth_minus_1
                in_height in_width
                out_channels n_hidden)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (staticNatValue n_hidden :: Int)
                        , show batchSize
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
        runBatch !parameters (k, chunk) = do
          let f = trainWithLoss kheight_minus_1 kwidth_minus_1
                                in_height in_width
                                out_channels
                                n_hidden batch_size
              chunkS = map packBatchS
                       $ filter (\ch -> length ch >= batchSize)
                       $ chunksOf batchSize chunk
              res = fst $ sgd gamma f chunkS parameters
              !trainScore = ftest kheight_minus_1 kwidth_minus_1
                                  in_height in_width
                                  out_channels n_hidden
                                  chunk res
              !testScore = ftest kheight_minus_1 kwidth_minus_1
                                 in_height in_width
                                 out_channels n_hidden
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
                       $ chunksOf (2 * batchSize) trainDataShuffled
                           -- TODO: (10 * batchSize) takes forever
          !res <- foldM runBatch params2 chunks
          runEpoch (succ n) res
    res <- runEpoch 1 parametersInit
    let testErrorFinal = 1 - ftest kheight_minus_1 kwidth_minus_1
                                   in_height in_width
                                   out_channels n_hidden
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
  , convMnistTestCaseCNNT (MkSN @4) (MkSN @4) (MkSN @2) (MkSN @3)
                          (MkSN @1)
                          "CNNT artificial 5 4 3 2 1" 5 4
                          convMnistLossFusedS convMnistTestS
                          0.02 (0.89 :: Float)
  , convMnistTestCaseCNNO (MkSN @4) (MkSN @4) (MkSN @2) (MkSN @3)
                          (MkSN @SizeMnistHeight) (MkSN @SizeMnistWidth)
                          (MkSN @1)
                          "O artificial 5 4 3 2 1" 5 4
                          convMnistLossFusedO convMnistTestO convMnistLenS
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
  , convMnistTestCaseCNNT (MkSN @4) (MkSN @4) (MkSN @64) (MkSN @16)
                          (MkSN @16)
                          "CNNT1 epoch 1 batch" 1 1
                          convMnistLossFusedS convMnistTestS
                          0.02 (0.85 :: Double)
  , convMnistTestCaseCNNO (MkSN @4) (MkSN @4) (MkSN @64) (MkSN @16)
                          (MkSN @SizeMnistHeight) (MkSN @SizeMnistWidth)
                          (MkSN @16)
                          "O1 epoch 1 batch" 1 1
                          convMnistLossFusedO convMnistTestO convMnistLenS
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
  , convMnistTestCaseCNNT (MkSN @4) (MkSN @4) (MkSN @1) (MkSN @1)
                          (MkSN @1)
                          "CNNT artificial 1 1 1 1 1" 1 1
                          convMnistLossFusedS convMnistTestS
                          1 (0.92 :: Double)
  , convMnistTestCaseCNNO (MkSN @4) (MkSN @4) (MkSN @1) (MkSN @1)
                          (MkSN @SizeMnistHeight) (MkSN @SizeMnistWidth)
                          (MkSN @1)
                          "O artificial 1 1 1 1 1" 1 1
                          convMnistLossFusedO convMnistTestO convMnistLenS
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
  , convMnistTestCaseCNNT (MkSN @4) (MkSN @4) (MkSN @4) (MkSN @3)
                          (MkSN @5)
                          "CNNT artificial 1 2 3 4 5" 1 2
                          convMnistLossFusedS convMnistTestS
                          6 (0.86 :: Float)
  , convMnistTestCaseCNNO (MkSN @4) (MkSN @4) (MkSN @4) (MkSN @3)
                          (MkSN @SizeMnistHeight) (MkSN @SizeMnistWidth)
                          (MkSN @5)
                          "O artificial 1 2 3 4 5" 1 2
                          convMnistLossFusedO convMnistTestO convMnistLenS
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
            f, fP :: forall d r. (ADModeAndNum d r)
                  => ADInputs d r -> ADVal d r
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
        in qcPropDom f parameters ds parametersPerturbation 1
           .&&. qcPropDom fP parameters ds parametersPerturbation 1
           .&&. cmpTwoSimple f fP parameters ds
  , testProperty "Compare gradients and two forward derivatives for 4 implementations of CNN MNIST" $
      \seed ->
      forAll (choose (0, sizeMnistLabelInt - 1)) $ \seedDs ->
      forAll (choose (1, volume)) $ \depth ->
      forAll (choose (1, volume)) $ \num_hidden ->
      forAll (choose (0.01, 0.5)) $ \range ->
      forAll (choose (0.01, 10)) $ \rangeDs ->
        let createRandomVector n seedV = LA.randomVector seedV LA.Uniform n
            glyph = LA.reshape 28 $ createRandomVector (28 * 28) seed
            label = LA.konst 0 sizeMnistLabelInt V.// [(seedDs, 1)]
            mnistData :: MnistData2 Double
            mnistData = (glyph, label)
            paramShape = lenMnistCNN final_image_size depth num_hidden
            (_, _, _, parameters) = initializerFixed seed range paramShape
            (_, _, _, ds) = initializerFixed seedDs rangeDs paramShape
            (_, _, _, parametersPerturbation) =
              initializerFixed (seed + seedDs) 1e-7 paramShape
            f, fP, fO, fS :: forall d r. (ADModeAndNum d r, r ~ Double)
                          => ADInputs d r -> ADVal d r
            f = convMnistLossCNN depth mnistData
            fP = convMnistLossCNNP depth mnistData
            fO = (withStaticNat num_hidden  -- reverse order than args taken
                  $ withStaticNat depth
                  $ convMnistLossFusedO (MkSN @4) (MkSN @4)
                                        sizeMnistHeight sizeMnistWidth
                 )
                   (MkSN @1)
                   (packBatch @1 [shapeBatch $ first LA.flatten mnistData])
            fS adinputs =
              withStaticNat num_hidden  -- reverse order than args below
              $ withStaticNat depth
              $ \(c_out :: StaticNat c_out) (n_hidden :: StaticNat n_hidden) ->
                  let valsInit
                        :: Value (ADConvMnistParameters 4 4 c_out n_hidden
                                                        'ADModeGradient r)
                      valsInit = fst $ randomVals (1 :: Double) (mkStdGen 1)
                  in convMnistLossFusedS
                       (MkSN @4) (MkSN @4)
                       c_out n_hidden
                       (MkSN @1)
                       (packBatch @1 [shapeBatch $ first LA.flatten mnistData])
                       (parseADInputs valsInit adinputs)
            paramsToT (Domains p0 p1 p2 _) =
              let qX = V.fromList
                    [ OT.fromVector [depth, 1, 5, 5]
                      $ V.concat $ map LA.flatten
                      $ take depth $ V.toList p2
                    , OT.fromVector [depth] $ V.take depth p0
                    , OT.fromVector [depth, depth, 5, 5]
                      $ V.concat $ map LA.flatten
                      $ take (depth * depth) (drop depth $ V.toList p2)
                    , OT.fromVector [depth] $ V.drop depth p0
                    , let m = p2 V.! (depth + depth * depth)
                      in OT.fromVector [num_hidden, LA.cols m]
                         $ LA.flatten m
                    , OT.fromVector [num_hidden] $ p1 V.! 0
                    , OT.fromVector [sizeMnistLabelInt, num_hidden]
                      $ LA.flatten
                      $ p2 V.! (depth + depth * depth + 1)
                    , OT.fromVector [sizeMnistLabelInt] $ p1 V.! 1
                    ]
              in Domains V.empty V.empty V.empty qX
            parametersT = paramsToT parameters
            dsT = paramsToT ds
            parametersPerturbationT = paramsToT parametersPerturbation
        in qcPropDom f parameters ds parametersPerturbation 1
           .&&. qcPropDom fP parameters ds parametersPerturbation 1
           .&&. qcPropDom fO parametersT dsT parametersPerturbationT 1
           .&&. qcPropDom fS parametersT dsT parametersPerturbationT 1
           .&&. cmpTwoSimple f fP parameters ds
           .&&. cmpTwo f fO parameters parametersT ds dsT
           .&&. cmpTwo f fS parameters parametersT ds dsT
  ]
