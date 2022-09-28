{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestMnistRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.List (foldl', unfoldr)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.External.OutdatedOptimizer
import MnistData
import MnistFcnnVector
import MnistRnnShaped

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
  fst $ f xs (constant $ HM.konst 0 k) inputs

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
        -> IO r
sgdShow f trainData parameters = do
  result <- fst <$> sgd 0.1 f trainData parameters
  snd <$> revIO 1 (f $ head trainData) result

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
       res <- sgdShow f trainData parameters0
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
       res <- sgdShow f trainData parameters0
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
  foldl' (\s x -> valueFun (snd . f x (constant s)) parameters)

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
       trained <- fst <$> sgd 0.1 f trainData parameters0
       let primed = prime fp trained (HM.konst 0 30) (take 19 series)
           output = feedback fp trained primed (series !! 19)
       take 30 output @?~ expected

-- A version written using vectors

hiddenLayerSinRNNV :: ADModeAndNum d r
                   => r
                   -> ADVal d (Vector r)
                   -> ADInputs d r
                   -> (ADVal d (Vector r), ADVal d (Vector r))
hiddenLayerSinRNNV x s inputs =
  let wX = at1 inputs 0
      b = at1 inputs 31
      y = scale (HM.konst x 30) wX + sumTrainableInputsL s 1 inputs 30 + b
      yLogistic = logistic y
  in (y, yLogistic)

outputLayerSinRNNV :: ADModeAndNum d r
                   => ADVal d (Vector r)
                   -> ADInputs d r
                   -> ADVal d r
outputLayerSinRNNV vec inputs =
  let w = at1 inputs 32
      b = at0 inputs 0
  in w <.>! vec + b

fcfcrnnV :: ADModeAndNum d r
         => r
         -> ADVal d (Vector r)
         -> ADInputs d r
         -> (ADVal d r, ADVal d (Vector r))
fcfcrnnV x s inputs =
  let (hiddenLayer, sHiddenLayer) = hiddenLayerSinRNNV x s inputs
      outputLayer = outputLayerSinRNNV hiddenLayer inputs
  in (outputLayer, sHiddenLayer)

nnSinRNNLossV :: ADModeAndNum d r
              => (Vector r, r)
              -> ADInputs d r
              -> ADVal d r
nnSinRNNLossV (xs, target) inputs =
  let result = zeroState 30 (unrollLast' fcfcrnnV) xs inputs
  in squaredDifference target result

-- Autoregressive model with degree 2

ar2Sin :: ADModeAndNum d r
       => r
       -> ADVal d (Vector r)
       -> ADInputs d r
       -> (ADVal d r, ADVal d (Vector r))
ar2Sin yLast s inputs =
  let c = at0 inputs 0
      phi1 = at0 inputs 1
      phi2 = at0 inputs 2
      yLastLast = index0 s 0  -- dummy vector for compatibility
      y = c + scale yLast phi1 + phi2 * yLastLast
  in (y, constant $ V.singleton yLast)

ar2SinLoss :: ADModeAndNum d r
           => (Vector r, r)
           -> ADInputs d r
           -> ADVal d r
ar2SinLoss (xs, target) inputs =
  let result = zeroState 30 (unrollLast' ar2Sin) xs inputs
  in squaredDifference target result

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)], [])
                (return $ take 30000 samples) 5.060827754123346e-5
  , feedbackTestCase "feedback" fcfcrnn nnSinRNNLoss
                     (1, [30, 30], [(30, 1), (30, 30)], [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9655322144631203,-0.8919588317267176,-0.7773331580548076,-0.6212249872512189,-0.4246885094957385,-0.19280278430361192,6.316924614971235e-2,0.3255160857644734,0.5731149496491759,0.7872840563791541,0.957217059407527,1.0815006200684472,1.1654656874016613,1.2170717188563214,1.2437913143303263,1.251142657837598,1.2423738174804864,1.2186583377053681,1.1794148708577938,1.1226117988569018,1.0450711676413071,0.9428743310020188,0.8120257428038534,0.6495453130357101,0.45507653540664667,0.23281831228915612,-6.935736916677385e-3,-0.24789484923780786,-0.4705527193222155]
  , sgdTestCase "trainVV" nnSinRNNLossV (1, replicate 33 30, [], [])
                (return $ take 30000 samples) 4.6511403967229306e-5
      -- different random initial paramaters produce a worse result;
      -- matrix implementation faster, because the matrices still fit in cache
  , feedbackTestCase "feedbackVV" fcfcrnnV nnSinRNNLossV
                     (1, replicate 33 30, [], [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9660899403337656,-0.8930568599923028,-0.7791304201898077,-0.6245654477568863,-0.4314435277698684,-0.2058673183484546,4.0423225394292085e-2,0.29029630688547203,0.5241984159992963,0.7250013011527577,0.8820730400055012,0.9922277361823716,1.057620382863504,1.08252746840241,1.070784986731554,1.0245016946328942,0.9438848015250431,0.827868146535437,0.6753691437632174,0.48708347071773117,0.26756701680655437,2.6913747557207532e-2,-0.21912614372802072,-0.45154893423928943,-0.6525638736434227,-0.8098403108946983,-0.9180866488182939,-0.9775459850131992,-0.9910399864230198]
  , sgdTestCase "trainAR" ar2SinLoss (3, [], [], [])
                (return $ take 30000 samples) 6.327978161031336e-23
  , feedbackTestCase "feedbackAR" ar2Sin ar2SinLoss
                     (3, [], [], [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9510565162972417,-0.8443279255081759,-0.6845471059406962,-0.48175367412103653,-0.24868988719256901,-3.673766846290505e-11,0.24868988711894977,0.4817536740469978,0.6845471058659982,0.8443279254326351,0.9510565162207472,0.9980267283507953,0.9822872506502898,0.9048270523889208,0.7705132427021685,0.5877852522243431,0.3681245526237731,0.12533323351198067,-0.1253332336071494,-0.36812455271766376,-0.5877852523157643,-0.7705132427900961,-0.9048270524725681,-0.9822872507291605,-0.9980267284247174,-0.9510565162898851,-0.844327925497479,-0.6845471059273313,-0.48175367410584324]
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
            v = valueFun nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

testMnistRNNL2 :: forall r. ADModeAndNum 'ADModeValue r
               => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNL2 width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNL2 width glyph
            v = valueFun nn parameters
        in V.maxIndex v == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

-- A version written using vectors

hiddenLayerMnistRNNV :: ADModeAndNum d r
                     => Int
                     -> Vector r
                     -> ADVal d (Vector r)
                     -> ADInputs d r
                     -> (ADVal d (Vector r), ADVal d (Vector r))
hiddenLayerMnistRNNV width x s inputs =
  let b = at1 inputs (width + width)  -- 128
      y = sumConstantDataL x 0 inputs width
          + sumTrainableInputsL s width inputs width
          + b
      yTanh = tanh y
  in (yTanh, yTanh)

outputLayerMnistRNNV :: ADModeAndNum d r
                     => Int
                     -> ADVal d (Vector r)
                     -> ADInputs d r
                     -> ADVal d (Vector r)
outputLayerMnistRNNV width vec inputs =
  let b = at1 inputs (width + width + 1 + 10)  -- 10
  in sumTrainableInputsL vec (width + width + 1) inputs 10 + b

fcfcrnnMnistV :: ADModeAndNum d r
              => Int
              -> Vector r
              -> ADVal d (Vector r)
              -> ADInputs d r
              -> (ADVal d (Vector r), ADVal d (Vector r))
fcfcrnnMnistV = hiddenLayerMnistRNNV

nnMnistRNNV :: ADModeAndNum d r
            => Int
            -> [Vector r]
            -> ADInputs d r
            -> ADVal d (Vector r)
nnMnistRNNV width x inputs =
  let rnnLayer = zeroState width (unrollLastG $ fcfcrnnMnistV width) x inputs
  in outputLayerMnistRNNV width rnnLayer inputs

nnMnistRNNLossV :: ADModeAndNum d r
                => Int
                -> ([Vector r], Vector r)
                -> ADInputs d r
                -> ADVal d r
nnMnistRNNLossV width (xs, target) inputs =
  let result = nnMnistRNNV width xs inputs
  in lossSoftMaxCrossEntropyV target result

testMnistRNNV :: forall r. ADModeAndNum 'ADModeValue r
              => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNV width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNV width glyph
            v = valueFun nn parameters
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

lenMnistRNNV :: Int -> Int -> (Int, [Int], [(Int, Int)], [OT.ShapeL])
lenMnistRNNV width nLayers =
  ( 0
  , replicate width 28 ++ replicate width width ++ [width]
    ++ replicate 10 width ++ [10]
    ++ concat (replicate (nLayers - 1)
                (replicate width width ++ replicate width width ++ [width]))
  , []
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
           runBatch (parameters@(!_, !_, !_, !_), stateAdam) (k, chunk) = do
             res@(parameters2, _) <-
               sgdAdamBatch 150 (f width) chunk parameters stateAdam
             let !trainScore = ftest width chunk parameters2
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
      batchSize = HM.cols x
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
      batchSize = HM.cols u
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
      batchSize = HM.cols u
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
  let len = HM.rows u `div` 2
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
zeroStateB ij f xs inputs =
  fst $ f xs (constant $ HM.konst 0 ij) inputs

nnMnistRNNB :: ADModeAndNum d r
            => Int
            -> [Matrix r]
            -> ADInputs d r
            -> ADVal d (Matrix r)
nnMnistRNNB width xs inputs =
  let batchSize = HM.cols $ head xs
      rnnLayer = zeroStateB (width, batchSize) (unrollLastG fcfcrnnMnistB)
                            xs inputs
  in outputLayerMnistRNNB rnnLayer inputs

nnMnistRNNB2 :: ADModeAndNum d r
             => Int
             -> [Matrix r]
             -> ADInputs d r
             -> ADVal d (Matrix r)
nnMnistRNNB2 width xs inputs =
  let batchSize = HM.cols $ head xs
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
  in scale (recip $ fromIntegral $ V.length u) $ sumElements0 vec

nnMnistRNNLossB2 :: ADModeAndNum d r
                 => Int
                 -> ([Matrix r], Matrix r)
                 -> ADInputs d r
                 -> ADVal d r
nnMnistRNNLossB2 width (xs, target) inputs =
  let result = nnMnistRNNB2 width xs inputs
      vec@(D u _) = lossSoftMaxCrossEntropyL target result
  in scale (recip $ fromIntegral $ V.length u) $ sumElements0 vec

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
                 behead !acc l = behead (HM.fromColumns (map head l) : acc)
                                        (map tail l)
             in (behead [] inputs, HM.fromColumns targets)
           -- There is some visual feedback, because some of these take long.
           runBatch :: (Domains Double, StateAdam Double)
                    -> (Int, [([Vector Double], Vector Double)])
                    -> IO (Domains Double, StateAdam Double)
           runBatch (parameters@(!_, !_, !_, !_), stateAdam) (k, chunk) = do
             res@(parameters2, _) <-
               sgdAdam (f width) (map packChunk $ chunksOf 150 chunk)
                       parameters stateAdam
             let !trainScore = ftest width chunk parameters2
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
  => StaticNat out_width -> StaticNat batch_size
  -> String
  -> Int
  -> Int
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => StaticNat out_width' -> StaticNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> ADInputs d r
      -> ADVal d r)
  -> (forall out_width' batch_size'. ADModeAndNum d r
      => StaticNat out_width' -> StaticNat batch_size'
      -> MnistDataBatchS batch_size' r
      -> Domains r
      -> r)
  -> (forall out_width' sizeMnistWidth'.
         StaticNat out_width'
      -> StaticNat sizeMnistWidth'
      -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> TestTree
mnistTestCaseRNNS out_width@MkSN batch_size@MkSN
                  prefix epochs maxBatches trainWithLoss ftest flen expected =
  let batchSize = staticNatValue batch_size :: Int
      ((_, _, _, nParamsX), totalParams, range, parametersInit) =
        initializerFixed 44 0.2 (flen out_width (MkSN @SizeMnistWidth))
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
        runBatch (parameters@(!_, !_, !_, !_), stateAdam) (k, chunk) = do
          let f = trainWithLoss out_width batch_size
              chunkS = map (packBatch @batch_size)
                       $ filter (\ch -> length ch >= batchSize)
                       $ chunksOf batchSize chunk
          res@(parameters2, _) <- sgdAdam f chunkS parameters stateAdam
          let !trainScore =
                ftest out_width (MkSN @(10 * batch_size))
                      (packBatch @(10 * batch_size) chunk)
                      parameters2
              !testScore = ftest out_width (MkSN @LengthTestData)
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
    let testErrorFinal = 1 - ftest out_width (MkSN @LengthTestData)
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
  , mnistTestCaseRNN "99VV 1 epoch, all batches" 1 99
                     nnMnistRNNLossV testMnistRNNV lenMnistRNNV 128 1
                     6.740000000000002e-2
  , mnistTestCaseRNNS (MkSN @128) (MkSN @150)
                      "1S 1 epoch, 1 batch" 1 1
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
  , let glyph = V.unfoldrExactN sizeMnistGlyphInt (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabelInt (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "randomVV 100"
                   (nnMnistRNNLossV 128)
                   (lenMnistRNNV 128 1)
                   (return trainData)
                   48.93543453250378
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstVV 100 trainset samples only"
                   (nnMnistRNNLossV 128)
                   (lenMnistRNNV 128 1)
                   (map rws . take 100
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.749410768938081
  , mnistTestCaseRNN "1VV 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossV testMnistRNNV lenMnistRNNV 48 1
                     0.6880999999999999
  , mnistTestCaseRNNS (MkSN @120) (MkSN @15)
                      "1S 1 epoch, 1 batch" 1 1
                      rnnMnistLossFusedS rnnMnistTestS rnnMnistLenS
                      0.8418
  ]
