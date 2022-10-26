{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestMnistRNNSimple (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.List (foldl', unfoldr)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.External.OptimizerTools
import MnistData
import MnistFcnnVector

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

-- A version written using vectors

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

unrollLastG :: forall d a b c r.
               (a -> b -> ADInputs d r -> (c, b))
            -> ([a] -> b -> ADInputs d r -> (c, b))
unrollLastG f xs s0 inputs =
  let g :: (c, b) -> a -> (c, b)
      g (_, s) x = f x s inputs
  in foldl' g (undefined, s0) xs

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
  [ sgdTestCase "trainVV" nnSinRNNLossV (1, replicate 33 30, [], [])
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
  -> IO (Domains r, StateAdam r)
sgdAdamBatch = sgdAdamBatchArgs defaultArgsAdam

sgdAdamBatchArgs
  :: forall r a. HasDelta r
  => ArgsAdam r
  -> Int  -- ^ batch size
  -> (a -> ADInputs 'ADModeGradient r -> ADVal 'ADModeGradient r)
  -> [a]
  -> Domains r
  -> StateAdam r
  -> IO (Domains r, StateAdam r)
sgdAdamBatchArgs argsAdam batchSize f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  deltaInputs = generateDeltaInputs parameters0
  go :: [a] -> Domains r-> StateAdam r -> IO (Domains r, StateAdam r)
  go [] parameters stateAdam = return (parameters, stateAdam)
  go l parameters stateAdam = do
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
    gradients <- fst <$> revGeneral 1 fBatch inputs
    let (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    go rest parametersNew stateAdamNew

mnistRNNTestsLong :: TestTree
mnistRNNTestsLong = testGroup "MNIST RNN long tests"
  [ mnistTestCaseRNN "99VV 1 epoch, all batches" 1 99
                     nnMnistRNNLossV testMnistRNNV lenMnistRNNV 128 1
                     6.740000000000002e-2
  ]

mnistRNNTestsShort :: TestTree
mnistRNNTestsShort = testGroup "MNIST RNN short tests"
  [ let glyph = V.unfoldrExactN sizeMnistGlyphInt (uniformR (0, 1))
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
  ]
