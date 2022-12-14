{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestMnistRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl', unfoldr)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.DualClass (pattern D)
import HordeAd.External.OptimizerTools
import MnistData
import MnistRnnShaped
import OldMnistRnnShaped

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees = [ sinRNNTests
            , mnistRNNTestsShort
            , mnistRNNTestsLong
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ sinRNNTests
                      , mnistRNNTestsShort
                      ]


-- * A recurrent net and an autoregressive model for sine, following
-- https://blog.jle.im/entry/purely-functional-typed-models-2.html
-- and obtaining matching results

-- A version written using matrices

hiddenLayerSinRNN :: ADModeAndNum d r
                  => r
                  -> ADVal d (Vector r)
                  -> ADInputs d r
                  -> (ADVal d (Vector r), ADVal d (Vector r))
hiddenLayerSinRNN x s inputs =
  let wX = at2 inputs 0
      wS = at2 inputs 1
      b = at1 inputs 0
      y = wX #>!! V.singleton x + wS #>! s + b
      yLogistic = logistic y
  in (y, yLogistic)

outputLayerSinRNN :: ADModeAndNum d r
                  => ADVal d (Vector r)
                  -> ADInputs d r
                  -> ADVal d r
outputLayerSinRNN vec inputs =
  let w = at1 inputs 1
      b = at0 inputs 0
  in w <.>! vec + b

fcfcrnn :: ADModeAndNum d r
        => r
        -> ADVal d (Vector r)
        -> ADInputs d r
        -> (ADVal d r, ADVal d (Vector r))
fcfcrnn x s inputs =
  let (hiddenLayer, sHiddenLayer) = hiddenLayerSinRNN x s inputs
      outputLayer = outputLayerSinRNN hiddenLayer inputs
  in (outputLayer, sHiddenLayer)

unrollLast' :: forall d r. ADModeAndNum d r
            => (r
                -> ADVal d (Vector r)
                -> ADInputs d r
                -> (ADVal d r, ADVal d (Vector r)))
            -> (Vector r
                -> ADVal d (Vector r)
                -> ADInputs d r
                -> (ADVal d r, ADVal d (Vector r)))
unrollLast' f xs s0 inputs =
  let g :: (ADVal d r, ADVal d (Vector r)) -> r
        -> (ADVal d r, ADVal d (Vector r))
      g (_, s) x = f x s inputs
  in V.foldl' g (undefined, s0) xs

zeroState :: ADModeAndNum d r
          => Int
          -> (a
              -> ADVal d (Vector r)
              -> ADInputs d r
              -> (ADVal d r2, ADVal d (Vector r)))
          -> (a
              -> ADInputs d r
              -> ADVal d r2)
zeroState k f xs inputs =
  fst $ f xs (constant $ LA.konst 0 k) inputs

nnSinRNN :: ADModeAndNum d r
         => Vector r
         -> ADInputs d r
         -> ADVal d r
nnSinRNN = zeroState 30 (unrollLast' fcfcrnn)

nnSinRNNLoss :: ADModeAndNum d r
             => (Vector r, r)
             -> ADInputs d r
             -> ADVal d r
nnSinRNNLoss (xs, target) inputs =
  let result = nnSinRNN xs inputs
  in squaredDifference target result

series :: [Double]
series = [sin (2 * pi * t / 25) | t <- [0 ..]]

samples :: [(Vector Double, Double)]
samples  = [(V.fromList $ init c, last c) | c <- chunksOf 19 series]

sgdShow :: HasDelta r
        => (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
        -> [a]
        -> Domains r
        -> r
sgdShow f trainData parameters =
  let result = fst $ sgd 0.1 f trainData parameters
  in snd $ revOnDomains 1 (f $ head trainData) result

sgdTestCase :: String
            -> (a
                -> ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double)
            -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
            -> IO [a]
            -> Double
            -> TestTree
sgdTestCase prefix f nParameters trainDataIO expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, parameters0) =
        initializerFixed 44 0.05 nParameters
      name = prefix ++ " "
             ++ unwords [ show nParams0, show nParams1, show nParams2
                        , show totalParams, show range ]
  in testCase name $ do
       trainData <- trainDataIO
       let res = sgdShow f trainData parameters0
       res @?~ expected

sgdTestCaseAlt :: String
            -> (a
                -> ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double)
            -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
            -> IO [a]
            -> [Double]
            -> TestTree
sgdTestCaseAlt prefix f nParameters trainDataIO expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, parameters0) =
        initializerFixed 44 0.05 nParameters
      name = prefix ++ " "
             ++ unwords [ show nParams0, show nParams1, show nParams2
                        , show totalParams, show range ]
  in testCase name $ do
       trainData <- trainDataIO
       let res = sgdShow f trainData parameters0
       assertCloseElem "" expected res

prime :: ADModeAndNum 'ADModeValue r
      => (r
          -> ADVal 'ADModeValue (Vector r)
          -> ADInputs 'ADModeValue r
          -> (ADVal 'ADModeValue r, ADVal 'ADModeValue (Vector r)))
      -> Domains r
      -> Vector r
      -> [r]
      -> Vector r
prime f parameters =
  foldl' (\s x -> valueOnDomains (snd . f x (constant s)) parameters)

feedback :: ADModeAndNum 'ADModeValue r
         => (r
             -> ADVal 'ADModeValue (Vector r)
             -> ADInputs 'ADModeValue r
             -> (ADVal 'ADModeValue r, ADVal 'ADModeValue (Vector r)))
         -> Domains r
         -> Vector r
         -> r
         -> [r]
feedback f parameters s0 x0 =
  let go (x, s) =
        let (D y _, sd') = valueGeneral (f x s) parameters
        in Just (x, (y, sd'))
  in unfoldr go (x0, constant s0)

feedbackTestCase :: String
                 -> (Double
                     -> ADVal 'ADModeValue (Vector Double)
                     -> ADInputs 'ADModeValue Double
                     -> ( ADVal 'ADModeValue Double
                        , ADVal 'ADModeValue (Vector Double) ))
                 -> (a
                     -> ADInputs 'ADModeGradient Double
                     -> ADVal 'ADModeGradient Double)
                 -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
                 -> [a]
                 -> [Double]
                 -> TestTree
feedbackTestCase prefix fp f nParameters trainData expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, parameters0) =
        initializerFixed 44 0.05 nParameters
      name = prefix ++ " "
             ++ unwords [ show nParams0, show nParams1, show nParams2
                        , show totalParams, show range ]
  in testCase name $ do
       let trained = fst $ sgd 0.1 f trainData parameters0
           primed = prime fp trained (LA.konst 0 30) (take 19 series)
           output = feedback fp trained primed (series !! 19)
       take 30 output @?~ expected

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)], [])
                (return $ take 30000 samples) 5.060827754123346e-5
  , feedbackTestCase "feedback" fcfcrnn nnSinRNNLoss
                     (1, [30, 30], [(30, 1), (30, 30)], [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9655322144631203,-0.8919588317267176,-0.7773331580548076,-0.6212249872512189,-0.4246885094957385,-0.19280278430361192,6.316924614971235e-2,0.3255160857644734,0.5731149496491759,0.7872840563791541,0.957217059407527,1.0815006200684472,1.1654656874016613,1.2170717188563214,1.2437913143303263,1.251142657837598,1.2423738174804864,1.2186583377053681,1.1794148708577938,1.1226117988569018,1.0450711676413071,0.9428743310020188,0.8120257428038534,0.6495453130357101,0.45507653540664667,0.23281831228915612,-6.935736916677385e-3,-0.24789484923780786,-0.4705527193222155]
  ]

-- * A 1 recurrent layer net with 128 neurons for MNIST, based on
-- https://medium.com/machine-learning-algorithms/mnist-using-recurrent-neural-network-2d070a5915a2
-- *Not* LSTM.
-- Doesn't train without Adam, regardless of whether mini-batch sgd
-- is used and whether a second recurrent layer. It does train with Adam,
-- but only after very carefully tweaking initialization. This is
-- extremely sensitive to initial parameters, more than to anything
-- else. Probably, gradient is vanishing if parameters are initialized
-- with a probability distribution that doesn't have the right variance. See
-- https://stats.stackexchange.com/questions/301285/what-is-vanishing-gradient.

hiddenLayerMnistRNNL :: ADModeAndNum d r
                     => Vector r
                     -> ADVal d (Vector r)
                     -> ADInputs d r
                     -> (ADVal d (Vector r), ADVal d (Vector r))
hiddenLayerMnistRNNL x s inputs =
  let wX = at2 inputs 0  -- 128x28
      wS = at2 inputs 1  -- 128x128
      b = at1 inputs 0  -- 128
      y = wX #>!! x + wS #>! s + b
      yTanh = tanh y
  in (yTanh, yTanh)  -- tanh in both, as per https://github.com/keras-team/keras/blob/v2.8.0/keras/layers/legacy_rnn/rnn_cell_impl.py#L468

middleLayerMnistRNNL :: ADModeAndNum d r
                     => ADVal d (Vector r)
                     -> ADVal d (Vector r)
                     -> ADInputs d r
                     -> (ADVal d (Vector r), ADVal d (Vector r))
middleLayerMnistRNNL vec s inputs =
  let wX = at2 inputs 3  -- 128x128
      wS = at2 inputs 4  -- 128x128
      b = at1 inputs 2  -- 128
      y = wX #>! vec + wS #>! s + b
      yTanh = tanh y
  in (yTanh, yTanh)

outputLayerMnistRNNL :: ADModeAndNum d r
                     => ADVal d (Vector r)
                     -> ADInputs d r
                     -> ADVal d (Vector r)
outputLayerMnistRNNL vec inputs =
  let w = at2 inputs 2  -- 10x128
      b = at1 inputs 1  -- 10
  in w #>! vec + b  -- I assume there is no activations, as per https://www.tensorflow.org/api_docs/python/tf/compat/v1/layers/dense

fcfcrnnMnistL :: ADModeAndNum d r
              => Vector r
              -> ADVal d (Vector r)
              -> ADInputs d r
              -> (ADVal d (Vector r), ADVal d (Vector r))
fcfcrnnMnistL = hiddenLayerMnistRNNL

fcfcrnnMnistL2 :: ADModeAndNum d r
               => Vector r
               -> ADVal d (Vector r)
               -> ADInputs d r
               -> (ADVal d (Vector r), ADVal d (Vector r))
fcfcrnnMnistL2 x s@(D u _) inputs =
  let len = V.length u `div` 2
      s1 = slice1 0 len s
      s2 = slice1 len len s
      (vec1, s1') = hiddenLayerMnistRNNL x s1 inputs
      (vec2, s2') = middleLayerMnistRNNL vec1 s2 inputs
      s3 = append1 s1' s2'
  in (vec2, s3)

unrollLastG :: forall d a b c r.
               (a -> b -> ADInputs d r -> (c, b))
            -> ([a] -> b -> ADInputs d r -> (c, b))
unrollLastG f xs s0 inputs =
  let g :: (c, b) -> a -> (c, b)
      g (_, s) x = f x s inputs
  in foldl' g (undefined, s0) xs

nnMnistRNNL :: forall d r. ADModeAndNum d r
            => Int
            -> [Vector r]
            -> ADInputs d r
            -> ADVal d (Vector r)
nnMnistRNNL width x inputs =
  let rnnLayer = zeroState width (unrollLastG fcfcrnnMnistL) x inputs
  in outputLayerMnistRNNL rnnLayer inputs

nnMnistRNNL2 :: ADModeAndNum d r
             => Int
             -> [Vector r]
             -> ADInputs d r
             -> ADVal d (Vector r)
nnMnistRNNL2 width x inputs =
  let rnnLayer = zeroState (2 * width) (unrollLastG fcfcrnnMnistL2) x inputs
  in outputLayerMnistRNNL rnnLayer inputs

nnMnistRNNLossL :: forall d r. ADModeAndNum d r
                => Int
                -> ([Vector r], Vector r)
                -> ADInputs d r
                -> ADVal d r
nnMnistRNNLossL width (xs, target) inputs =
  let result = nnMnistRNNL width xs inputs
  in lossSoftMaxCrossEntropyV target result

nnMnistRNNLossL2 :: ADModeAndNum d r
                 => Int
                 -> ([Vector r], Vector r)
                 -> ADInputs d r
                 -> ADVal d r
nnMnistRNNLossL2 width (xs, target) inputs =
  let result = nnMnistRNNL2 width xs inputs
  in lossSoftMaxCrossEntropyV target result

testMnistRNNL :: forall r. ADModeAndNum 'ADModeValue r
              => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNL width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNL width glyph
            v = valueOnDomains nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

testMnistRNNL2 :: forall r. ADModeAndNum 'ADModeValue r
               => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNL2 width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNL2 width glyph
            v = valueOnDomains nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

lenMnistRNNL :: Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
lenMnistRNNL width nLayers =
  ( 0
  , [width, 10] ++ replicate (nLayers - 1) width
  , [(width, 28), (width, width), (10, width)]
    ++ concat (replicate (nLayers - 1) [(width, width), (width, width)])
  , []
  )

mnistTestCaseRNN
  :: String
  -> Int
  -> Int
  -> (Int
      -> ([Vector Double], Vector Double)
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> (Int -> [([Vector Double], Vector Double)] -> Domains Double -> Double)
  -> (Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Int
  -> Int
  -> Double
  -> TestTree
mnistTestCaseRNN prefix epochs maxBatches f ftest flen width nLayers
                 expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, parameters0) =
        initializerFixed 44 0.2 (flen width nLayers)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show nLayers
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show range ]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       let rws (input, target) =
             ( map (\k -> V.slice (k * 28) 28 input) [0 .. 27]
             , target )
       trainData <- map rws <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rws <$> loadMnistData testGlyphsPath testLabelsPath
       -- There is some visual feedback, because some of these take long.
       let runBatch :: (Domains Double, StateAdam Double)
                    -> (Int, [([Vector Double], Vector Double)])
                    -> IO (Domains Double, StateAdam Double)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let res@(parameters2, _) =
                   sgdAdamBatch 150 (f width) chunk parameters stateAdam
                 !trainScore = ftest width chunk parameters2
                 !testScore = ftest width testData parameters2
                 !lenChunk = length chunk
             hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
             hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
             hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
           runEpoch :: Int
                    -> (Domains Double, StateAdam Double)
                    -> IO (Domains Double)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parameters0, initialStateAdam parameters0)
       let testErrorFinal = 1 - ftest width testData res
       testErrorFinal @?~ expected

-- For testing, we want to avoid using matrices, so we can't express
-- mini-batches as tensors one dimension larger, so the following variant
-- of the optimizer is necessary.
sgdAdamBatch
  :: forall r a. HasDelta r
  => Int  -- ^ batch size
  -> (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatch = sgdAdamBatchArgs defaultArgsAdam

sgdAdamBatchArgs
  :: forall r a. HasDelta r
  => ArgsAdam r
  -> Int  -- ^ batch size
  -> (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatchArgs argsAdam batchSize f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go l parameters stateAdam =
    let inputs = makeADInputs parameters deltaInputs
        (batch, rest) = splitAt batchSize l
        fAdd :: ADInputs 'ADModeGradient r
             -> ADVal 'ADModeGradient r -> a
             -> ADVal 'ADModeGradient r
        fAdd vars !acc a = acc + f a vars
        fBatch :: ADInputs 'ADModeGradient r
               -> ADVal 'ADModeGradient r
        fBatch vars =
          let resBatch = foldl' (fAdd vars) 0 batch
          in resBatch / fromIntegral (length batch)
        gradients = fst $ revOnADInputs 1 fBatch inputs
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew


-- * A version written using matrices to express mini-batches of data
-- and so using matrix multiplication to run the neural net

hiddenLayerMnistRNNB :: ADModeAndNum d r
                     => Matrix r  -- the mini-batch of data 28x150
                     -> ADVal d (Matrix r)  -- state for mini-batch 128x150
                     -> ADInputs d r
                     -> (ADVal d (Matrix r), ADVal d (Matrix r))
hiddenLayerMnistRNNB x s inputs =
  let wX = at2 inputs 0  -- 128x28
      wS = at2 inputs 1  -- 128x128
      b = at1 inputs 0  -- 128
      batchSize = LA.cols x
      y = wX <>!! x + wS <>! s + asColumn2 b batchSize
      yTanh = tanh y
  in (yTanh, yTanh)

middleLayerMnistRNNB :: ADModeAndNum d r
                     => ADVal d (Matrix r)  -- 128x150
                     -> ADVal d (Matrix r)  -- 128x150
                     -> ADInputs d r
                     -> (ADVal d (Matrix r), ADVal d (Matrix r))
middleLayerMnistRNNB batchOfVec@(D u _) s inputs =
  let wX = at2 inputs 3  -- 128x128
      wS = at2 inputs 4  -- 128x128
      b = at1 inputs 2  -- 128
      batchSize = LA.cols u
      y = wX <>! batchOfVec + wS <>! s + asColumn2 b batchSize
      yTanh = tanh y
  in (yTanh, yTanh)

outputLayerMnistRNNB :: ADModeAndNum d r
                     => ADVal d (Matrix r)  -- 128x150
                     -> ADInputs d r
                     -> ADVal d (Matrix r)
outputLayerMnistRNNB batchOfVec@(D u _) inputs =
  let w = at2 inputs 2  -- 10x128
      b = at1 inputs 1  -- 10
      batchSize = LA.cols u
  in w <>! batchOfVec + asColumn2 b batchSize

fcfcrnnMnistB :: ADModeAndNum d r
              => Matrix r
              -> ADVal d (Matrix r)
              -> ADInputs d r
              -> (ADVal d (Matrix r), ADVal d (Matrix r))
fcfcrnnMnistB = hiddenLayerMnistRNNB

fcfcrnnMnistB2 :: ADModeAndNum d r
               => Matrix r  -- 28x150
               -> ADVal d (Matrix r)  -- 256x150
               -> ADInputs d r
               -> (ADVal d (Matrix r), ADVal d (Matrix r))
fcfcrnnMnistB2 x s@(D u _) inputs =
  let len = LA.rows u `div` 2
      s1 = rowSlice2 0 len s
      s2 = rowSlice2 len len s
      (vec1, s1') = hiddenLayerMnistRNNB x s1 inputs
      (vec2, s2') = middleLayerMnistRNNB vec1 s2 inputs
  in (vec2, rowAppend2 s1' s2')

zeroStateB :: ADModeAndNum d r
           => (Int, Int)
           -> (a
               -> ADVal d (Matrix r)
               -> ADInputs d r
               -> (ADVal d r2, ADVal d (Matrix r)))
           -> (a
               -> ADInputs d r
               -> ADVal d r2)
zeroStateB rowsCols f xs inputs =
  fst $ f xs (constant $ LA.konst 0 rowsCols) inputs

nnMnistRNNB :: ADModeAndNum d r
            => Int
            -> [Matrix r]
            -> ADInputs d r
            -> ADVal d (Matrix r)
nnMnistRNNB width xs inputs =
  let batchSize = LA.cols $ head xs
      rnnLayer = zeroStateB (width, batchSize) (unrollLastG fcfcrnnMnistB)
                            xs inputs
  in outputLayerMnistRNNB rnnLayer inputs

nnMnistRNNB2 :: ADModeAndNum d r
             => Int
             -> [Matrix r]
             -> ADInputs d r
             -> ADVal d (Matrix r)
nnMnistRNNB2 width xs inputs =
  let batchSize = LA.cols $ head xs
      rnnLayer = zeroStateB (2 * width, batchSize) (unrollLastG fcfcrnnMnistB2)
                            xs inputs
  in outputLayerMnistRNNB rnnLayer inputs

nnMnistRNNLossB :: ADModeAndNum d r
                => Int
                -> ([Matrix r], Matrix r)
                -> ADInputs d r
                -> ADVal d r
nnMnistRNNLossB width (xs, target) inputs =
  let result = nnMnistRNNB width xs inputs
      vec@(D u _) = lossSoftMaxCrossEntropyL target result
  in scale (recip $ fromIntegral $ V.length u) $ sumElements10 vec

nnMnistRNNLossB2 :: ADModeAndNum d r
                 => Int
                 -> ([Matrix r], Matrix r)
                 -> ADInputs d r
                 -> ADVal d r
nnMnistRNNLossB2 width (xs, target) inputs =
  let result = nnMnistRNNB2 width xs inputs
      vec@(D u _) = lossSoftMaxCrossEntropyL target result
  in scale (recip $ fromIntegral $ V.length u) $ sumElements10 vec

mnistTestCaseRNNB
  :: String
  -> Int
  -> Int
  -> (Int
      -> ([Matrix Double], Matrix Double)
      -> ADInputs 'ADModeGradient Double
      -> ADVal 'ADModeGradient Double)
  -> (Int -> [([Vector Double], Vector Double)] -> Domains Double -> Double)
  -> (Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Int
  -> Int
  -> Double
  -> TestTree
mnistTestCaseRNNB prefix epochs maxBatches f ftest flen width nLayers
                  expected =
  let ((nParams0, nParams1, nParams2, _), totalParams, range, parameters0) =
        initializerFixed 44 0.2 (flen width nLayers)
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show nLayers
                        , show nParams0, show nParams1, show nParams2
                        , show totalParams, show range ]
  in testCase name $ do
       hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
              prefix epochs maxBatches
       let rws (input, target) =
             ( map (\k -> V.slice (k * 28) 28 input) [0 .. 27]
             , target )
       trainData <- map rws <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rws <$> loadMnistData testGlyphsPath testLabelsPath
       let packChunk :: [([Vector Double], Vector Double)]
                     -> ([Matrix Double], Matrix Double)
           packChunk chunk =
             let (inputs, targets) = unzip chunk
                 behead !acc ([] : _) = reverse acc
                 behead !acc l = behead (LA.fromColumns (map head l) : acc)
                                        (map tail l)
             in (behead [] inputs, LA.fromColumns targets)
           -- There is some visual feedback, because some of these take long.
           runBatch :: (Domains Double, StateAdam Double)
                    -> (Int, [([Vector Double], Vector Double)])
                    -> IO (Domains Double, StateAdam Double)
           runBatch (!parameters, !stateAdam) (k, chunk) = do
             let res@(parameters2, _) =
                   sgdAdam (f width) (map packChunk $ chunksOf 150 chunk)
                           parameters stateAdam
                 !trainScore = ftest width chunk parameters2
                 !testScore = ftest width testData parameters2
                 !lenChunk = length chunk
             hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
             hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
             hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
             return res
           runEpoch :: Int
                    -> (Domains Double, StateAdam Double)
                    -> IO (Domains Double)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       res <- runEpoch 1 (parameters0, initialStateAdam parameters0)
       let testErrorFinal = 1 - ftest width testData res
       testErrorFinal @?~ expected


-- * A version written using shaped tensors

mnistTestCaseRNNS
  :: forall out_width batch_size d r. (r ~ Double, d ~ 'ADModeGradient)
  => SNat out_width -> SNat batch_size
  -> String
  -> Int
  -> Int
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => SNat out_width' -> SNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> ADRnnMnistParameters SizeMnistHeight out_width' d r
      -> ADVal d r)
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => SNat out_width' -> SNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> ((ADRnnMnistParameters SizeMnistHeight out_width' 'ADModeValue r
           -> ADVal 'ADModeValue (OS.Array '[SizeMnistLabel, batch_size'] r))
          -> OS.Array '[SizeMnistLabel, batch_size'] r)
      -> r)
  -> Double
  -> TestTree
mnistTestCaseRNNS out_width@MkSNat batch_size@MkSNat
                  prefix epochs maxBatches trainWithLoss ftestWithParams
                  expected =
  let batchSize = staticNatValue batch_size :: Int
      seed = mkStdGen 44
      range = 0.2
      valsInit
        :: Value (ADRnnMnistParameters SizeMnistHeight out_width
                                       'ADModeGradient r)
      valsInit = fst $ randomVals range seed
      parametersInit = toDomains valsInit
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (staticNatValue out_width :: Int)
                        , show batchSize
                        , show (nParams valsInit)
                        , show (nScalars valsInit)
                        , show range ]
      ftest :: SNat batch_size'
            -> MnistDataBatchS batch_size' r
            -> Domains r
            -> r
      ftest batch_size' mnist testParams =
        ftestWithParams out_width batch_size'
                        mnist (valueAtDomains valsInit testParams)
  in testCase name $ do
    hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
           prefix epochs maxBatches
    trainData <- map shapeBatch
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map shapeBatch
                <$> loadMnistData testGlyphsPath testLabelsPath
    let testDataS = packBatch @LengthTestData testData
        -- There is some visual feedback, because some of these take long.
        runBatch :: (Domains r, StateAdam r)
                 -> (Int, [MnistDataS r])
                 -> IO (Domains r, StateAdam r)
        runBatch (!parameters, !stateAdam) (k, chunk) = do
          let f mnist adinputs =
                trainWithLoss out_width batch_size
                              mnist (parseADInputs valsInit adinputs)
              chunkS = map (packBatch @batch_size)
                       $ filter (\ch -> length ch >= batchSize)
                       $ chunksOf batchSize chunk
              res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
              !trainScore =
                ftest (MkSNat @(10 * batch_size))
                      (packBatch @(10 * batch_size) chunk)
                      parameters2
              !testScore = ftest (MkSNat @LengthTestData)
                                 testDataS parameters2
              !lenChunk = length chunk
          hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
          hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
          hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
          return res
        runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
        runEpoch n (params2, _) | n > epochs = return params2
        runEpoch n paramsStateAdam = do
          hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..]
                       $ chunksOf (10 * batchSize) trainDataShuffled
          !res <- foldM runBatch paramsStateAdam chunks
          runEpoch (succ n) res
    res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
    let testErrorFinal = 1 - ftest (MkSNat @LengthTestData)
                                   testDataS res
    testErrorFinal @?~ expected

mnistTestCaseRNNO
  :: forall out_width batch_size d r. (r ~ Double, d ~ 'ADModeGradient)
  => SNat out_width -> SNat batch_size
  -> String
  -> Int
  -> Int
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => SNat out_width' -> SNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> ADInputs d r
      -> ADVal d r)
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => SNat out_width' -> SNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> Domains r
      -> r)
  -> (forall out_width' sizeMnistWidth'.
         SNat out_width'
      -> SNat sizeMnistWidth'
      -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> TestTree
mnistTestCaseRNNO out_width@MkSNat batch_size@MkSNat
                  prefix epochs maxBatches trainWithLoss ftest flen expected =
  let batchSize = staticNatValue batch_size :: Int
      ((_, _, _, nParamsX), totalParams, range, parametersInit) =
        initializerFixed 44 0.2 (flen out_width (MkSNat @SizeMnistWidth))
      name = prefix ++ ": "
             ++ unwords [ show epochs, show maxBatches
                        , show (staticNatValue out_width :: Int), show batchSize
                        , show nParamsX, show totalParams, show range ]
  in testCase name $ do
    hPutStrLn stderr $ printf "\n%s: Epochs to run/max batches per epoch: %d/%d"
           prefix epochs maxBatches
    trainData <- map shapeBatch
                 <$> loadMnistData trainGlyphsPath trainLabelsPath
    testData <- map shapeBatch
                <$> loadMnistData testGlyphsPath testLabelsPath
    let testDataS = packBatch @LengthTestData testData
        -- There is some visual feedback, because some of these take long.
        runBatch :: (Domains r, StateAdam r)
                 -> (Int, [MnistDataS r])
                 -> IO (Domains r, StateAdam r)
        runBatch (!parameters, !stateAdam) (k, chunk) = do
          let f = trainWithLoss out_width batch_size
              chunkS = map (packBatch @batch_size)
                       $ filter (\ch -> length ch >= batchSize)
                       $ chunksOf batchSize chunk
              res@(parameters2, _) = sgdAdam f chunkS parameters stateAdam
              !trainScore =
                ftest out_width (MkSNat @(10 * batch_size))
                      (packBatch @(10 * batch_size) chunk)
                      parameters2
              !testScore = ftest out_width (MkSNat @LengthTestData)
                                 testDataS parameters2
              !lenChunk = length chunk
          hPutStrLn stderr $ printf "\n%s: (Batch %d with %d points)" prefix k lenChunk
          hPutStrLn stderr $ printf "%s: Training error:   %.2f%%" prefix ((1 - trainScore) * 100)
          hPutStrLn stderr $ printf "%s: Validation error: %.2f%%" prefix ((1 - testScore ) * 100)
          return res
        runEpoch :: Int -> (Domains r, StateAdam r) -> IO (Domains r)
        runEpoch n (params2, _) | n > epochs = return params2
        runEpoch n paramsStateAdam = do
          hPutStrLn stderr $ printf "\n%s: [Epoch %d]" prefix n
          let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
              chunks = take maxBatches
                       $ zip [1 ..]
                       $ chunksOf (10 * batchSize) trainDataShuffled
          !res <- foldM runBatch paramsStateAdam chunks
          runEpoch (succ n) res
    res <- runEpoch 1 (parametersInit, initialStateAdam parametersInit)
    let testErrorFinal = 1 - ftest out_width (MkSNat @LengthTestData)
                                   testDataS res
    testErrorFinal @?~ expected

mnistRNNTestsLong :: TestTree
mnistRNNTestsLong = testGroup "MNIST RNN long tests"
  [ mnistTestCaseRNN "99LL 1 epoch, all batches" 1 99
                     nnMnistRNNLossL testMnistRNNL lenMnistRNNL 128 1
                     8.209999999999995e-2
  , mnistTestCaseRNNB "99BB 1 epoch, all batches" 1 99
                      nnMnistRNNLossB testMnistRNNL lenMnistRNNL 128 1
                      8.209999999999995e-2
  , mnistTestCaseRNN "99LL2 1 epoch, all batches" 1 99
                     nnMnistRNNLossL2 testMnistRNNL2 lenMnistRNNL 128 2
                     6.259999999999999e-2
  , mnistTestCaseRNNB "99BB2 1 epoch, all batches" 1 99
                      nnMnistRNNLossB2 testMnistRNNL2 lenMnistRNNL 128 2
                      6.259999999999999e-2
  , mnistTestCaseRNNS (MkSNat @128) (MkSNat @150)
                      "1S 1 epoch, 1 batch" 1 1
                      arnnMnistLossFusedS arnnMnistTestS
                      0.5448999999999999
  , mnistTestCaseRNNO (MkSNat @128) (MkSNat @150)
                      "1O 1 epoch, 1 batch" 1 1
                      rnnMnistLossFusedS rnnMnistTestS rnnMnistLenS
                      0.4375
  ]

mnistRNNTestsShort :: TestTree
mnistRNNTestsShort = testGroup "MNIST RNN short tests"
  [ let glyph = V.unfoldrExactN sizeMnistGlyphInt (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabelInt (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 140]
    in sgdTestCaseAlt "randomLL 140"
                      (nnMnistRNNLossL 128)
                      (lenMnistRNNL 128 1)
                      (return trainData)
                      [39.26534020336613, 39.26529993277164, 39.26529871965807, 39.26529500592892]
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstLL 100 trainset samples only"
                   (nnMnistRNNLossL 128)
                   (lenMnistRNNL 128 1)
                   (map rws . take 100
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.7790856895965272
  , mnistTestCaseRNN "1LL 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossL testMnistRNNL lenMnistRNNL 128 1
                     0.2845
  , mnistTestCaseRNNB "1BB 1 epoch, 1 batch" 1 1
                      nnMnistRNNLossB testMnistRNNL lenMnistRNNL 128 1
                      0.2845
  , let glyph = V.unfoldrExactN sizeMnistGlyphInt (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabelInt (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 140]
    in sgdTestCaseAlt "randomLL2 140"
                      (nnMnistRNNLossL2 128)
                      (lenMnistRNNL 128 2)
                      (return trainData)
                      [30.061871495723956, 30.06187089990927]
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstLL2 99 trainset samples only"
                   (nnMnistRNNLossL2 128)
                   (lenMnistRNNL 128 2)
                   (map rws . take 99
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.772595855528805
  , mnistTestCaseRNN "1LL2 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossL2 testMnistRNNL2 lenMnistRNNL 64 2
                     0.44210000000000005
  , mnistTestCaseRNNB "1BB2 1 epoch, 1 batch" 1 1
                      nnMnistRNNLossB2 testMnistRNNL2 lenMnistRNNL 128 2
                      0.2945
  , mnistTestCaseRNNS (MkSNat @120) (MkSNat @15)
                      "1S 1 epoch, 1 batch" 1 1
                      arnnMnistLossFusedS arnnMnistTestS
                      0.6793
  , mnistTestCaseRNNO (MkSNat @120) (MkSNat @15)
                      "1O 1 epoch, 1 batch" 1 1
                      rnnMnistLossFusedS rnnMnistTestS rnnMnistLenS
                      0.8418
  ]
