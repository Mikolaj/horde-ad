{-# LANGUAGE TypeFamilies #-}
module TestMnistRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import           Data.List (foldl', unfoldr)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

import HordeAd
import HordeAd.Core.OutdatedOptimizer
import HordeAd.Tool.MnistTools

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

hiddenLayerSinRNN :: (DeltaMonad r m, Floating (Vector r))
                  => r
                  -> DualNumber (Vector r)
                  -> DualNumberVariables r
                  -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerSinRNN x s variables = do
  let wX = varL variables 0
      wS = varL variables 1
      b = varV variables 0
  y <- returnLet $ wX #>!! V.singleton x + wS #>! s + b
  yLogistic <- logisticAct y
  return (y, yLogistic)

outputLayerSinRNN :: DeltaMonad r m
                  => DualNumber (Vector r)
                  -> DualNumberVariables r
                  -> m (DualNumber r)
outputLayerSinRNN vec variables = do
  let w = varV variables 1
      b = var variables 0
  returnLet $ w <.>! vec + b

fcfcrnn :: (DeltaMonad r m, Floating (Vector r))
        => r
        -> DualNumber (Vector r)
        -> DualNumberVariables r
        -> m (DualNumber r, DualNumber (Vector r))
fcfcrnn x s variables = do
  (hiddenLayer, sHiddenLayer) <- hiddenLayerSinRNN x s variables
  outputLayer <- outputLayerSinRNN hiddenLayer variables
  return (outputLayer, sHiddenLayer)

unrollLast' :: forall m r. DeltaMonad r m
            => (r
                -> DualNumber (Vector r)
                -> DualNumberVariables r
                -> m (DualNumber r, DualNumber (Vector r)))
            -> (Vector r
                -> DualNumber (Vector r)
                -> DualNumberVariables r
                -> m (DualNumber r, DualNumber (Vector r)))
unrollLast' f xs s0 variables =
  let g :: (DualNumber r, DualNumber (Vector r)) -> r
        -> m (DualNumber r, DualNumber (Vector r))
      g (_, s) x = f x s variables
  in V.foldM' g (undefined, s0) xs

zeroState :: DeltaMonad r m
          => Int
          -> (a
              -> DualNumber (Vector r)
              -> DualNumberVariables r
              -> m (DualNumber r2, DualNumber (Vector r)))
          -> (a
              -> DualNumberVariables r
              -> m (DualNumber r2))
zeroState k f xs variables =
  fst <$> f xs (scalar $ HM.konst 0 k) variables

nnSinRNN :: (DeltaMonad r m, Floating (Vector r))
         => Vector r
         -> DualNumberVariables r
         -> m (DualNumber r)
nnSinRNN = zeroState 30 (unrollLast' fcfcrnn)

nnSinRNNLoss :: (DeltaMonad r m, Floating (Vector r))
             => (Vector r, r)
             -> DualNumberVariables r
             -> m (DualNumber r)
nnSinRNNLoss (xs, target) variables = do
  result <- nnSinRNN xs variables
  lossSquared target result

series :: [Double]
series = [sin (2 * pi * t / 25) | t <- [0 ..]]

samples :: [(Vector Double, Double)]
samples  = [(V.fromList $ init c, last c) | c <- chunksOf 19 series]

sgdShow :: (Eq r, Fractional r, IsScalar r)
        => (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> [a]
        -> Domains r
        -> r
sgdShow f trainData parameters =
  let result = fst $ sgd 0.1 f trainData parameters
  in snd $ df (f $ head trainData) result

sgdTestCase :: String
            -> (a
                -> DualNumberVariables Double
                -> DeltaMonadGradient Double (DualNumber Double))
            -> (Int, [Int], [(Int, Int)])
            -> IO [a]
            -> Double
            -> TestTree
sgdTestCase prefix f nParameters trainDataIO expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, parameters0) =
        initializerFixed 44 0.05 nParameters
      name = prefix ++ " "
             ++ unwords [ show nParams, show nParamsV, show nParamsL
                        , show totalParams, show range ]
  in testCase name $ do
       trainData <- trainDataIO
       sgdShow f trainData parameters0
         @?= expected

prime :: IsScalar r
      => (r
          -> DualNumber (Vector r)
          -> DualNumberVariables r
          -> DeltaMonadValue r (DualNumber r, DualNumber (Vector r)))
      -> Domains r
      -> Vector r
      -> [r]
      -> Vector r
prime f parameters =
  foldl' (\s x -> primalValue (fmap snd . f x (scalar s)) parameters)

feedback :: IsScalar r
         => (r
             -> DualNumber (Vector r)
             -> DualNumberVariables r
             -> DeltaMonadValue r (DualNumber r, DualNumber (Vector r)))
         -> Domains r
         -> Vector r
         -> r
         -> [r]
feedback f parameters s0 x0 =
  let go (x, s) =
        let (D y _, sd') = primalValueGeneric (f x s) parameters
        in Just (x, (y, sd'))
  in unfoldr go (x0, scalar s0)

feedbackTestCase :: String
                 -> (Double
                     -> DualNumber (Vector Double)
                     -> DualNumberVariables Double
                     -> DeltaMonadValue Double
                                        ( DualNumber Double
                                        , DualNumber (Vector Double) ))
                 -> (a
                     -> DualNumberVariables Double
                     -> DeltaMonadGradient Double (DualNumber Double))
                 -> (Int, [Int], [(Int, Int)])
                 -> [a]
                 -> [Double]
                 -> TestTree
feedbackTestCase prefix fp f nParameters trainData expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, parameters0) =
        initializerFixed 44 0.05 nParameters
      name = prefix ++ " "
             ++ unwords [ show nParams, show nParamsV, show nParamsL
                        , show totalParams, show range ]
      trained = fst $ sgd 0.1 f trainData parameters0
      primed = prime fp trained (HM.konst 0 30) (take 19 series)
      output = feedback fp trained primed (series !! 19)
  in testCase name $
       take 30 output @?= expected

-- A version written using vectors

hiddenLayerSinRNNV :: (DeltaMonad r m, Floating (Vector r))
                   => r
                   -> DualNumber (Vector r)
                   -> DualNumberVariables r
                   -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerSinRNNV x s variables = do
  let wX = varV variables 0
      b = varV variables 31
  y <- returnLet
       $ scale (HM.konst x 30) wX + sumTrainableInputsL s 1 variables 30 + b
  yLogistic <- logisticAct y
  return (y, yLogistic)

outputLayerSinRNNV :: DeltaMonad r m
                   => DualNumber (Vector r)
                   -> DualNumberVariables r
                   -> m (DualNumber r)
outputLayerSinRNNV vec variables = do
  let w = varV variables 32
      b = var variables 0
  returnLet $ w <.>! vec + b

fcfcrnnV :: (DeltaMonad r m, Floating (Vector r))
         => r
         -> DualNumber (Vector r)
         -> DualNumberVariables r
         -> m (DualNumber r, DualNumber (Vector r))
fcfcrnnV x s variables = do
  (hiddenLayer, sHiddenLayer) <- hiddenLayerSinRNNV x s variables
  outputLayer <- outputLayerSinRNNV hiddenLayer variables
  return (outputLayer, sHiddenLayer)

nnSinRNNLossV :: (DeltaMonad r m, Floating (Vector r))
              => (Vector r, r)
              -> DualNumberVariables r
              -> m (DualNumber r)
nnSinRNNLossV (xs, target) variables = do
  result <- zeroState 30 (unrollLast' fcfcrnnV) xs variables
  lossSquared target result

-- Autoregressive model with degree 2

ar2Sin :: DeltaMonad r m
       => r
       -> DualNumber (Vector r)
       -> DualNumberVariables r
       -> m (DualNumber r, DualNumber (Vector r))
ar2Sin yLast s variables = do
  let c = var variables 0
      phi1 = var variables 1
      phi2 = var variables 2
      yLastLast = index0 s 0  -- dummy vector for compatibility
  y <- returnLet $ c + scale yLast phi1 + phi2 * yLastLast
  return (y, scalar $ V.singleton yLast)

ar2SinLoss :: DeltaMonad r m
           => (Vector r, r)
           -> DualNumberVariables r
           -> m (DualNumber r)
ar2SinLoss (xs, target) variables = do
  result <- zeroState 30 (unrollLast' ar2Sin) xs variables
  lossSquared target result

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)])
                (return $ take 30000 samples) 5.060827754123346e-5
  , feedbackTestCase "feedback" fcfcrnn nnSinRNNLoss
                     (1, [30, 30], [(30, 1), (30, 30)])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9655322144631203,-0.8919588317267176,-0.7773331580548076,-0.6212249872512189,-0.4246885094957385,-0.19280278430361192,6.316924614971235e-2,0.3255160857644734,0.5731149496491759,0.7872840563791541,0.957217059407527,1.0815006200684472,1.1654656874016613,1.2170717188563214,1.2437913143303263,1.251142657837598,1.2423738174804864,1.2186583377053681,1.1794148708577938,1.1226117988569018,1.0450711676413071,0.9428743310020188,0.8120257428038534,0.6495453130357101,0.45507653540664667,0.23281831228915612,-6.935736916677385e-3,-0.24789484923780786,-0.4705527193222155]
  , sgdTestCase "trainVV" nnSinRNNLossV (1, replicate 33 30, [])
                (return $ take 30000 samples) 4.6511403967229306e-5
      -- different random initial paramaters produce a worse result;
      -- matrix implementation faster, because the matrices still fit in cache
  , feedbackTestCase "feedbackVV" fcfcrnnV nnSinRNNLossV
                     (1, replicate 33 30, [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9660899403337656,-0.8930568599923028,-0.7791304201898077,-0.6245654477568863,-0.4314435277698684,-0.2058673183484546,4.0423225394292085e-2,0.29029630688547203,0.5241984159992963,0.7250013011527577,0.8820730400055012,0.9922277361823716,1.057620382863504,1.08252746840241,1.070784986731554,1.0245016946328942,0.9438848015250431,0.827868146535437,0.6753691437632174,0.48708347071773117,0.26756701680655437,2.6913747557207532e-2,-0.21912614372802072,-0.45154893423928943,-0.6525638736434227,-0.8098403108946983,-0.9180866488182939,-0.9775459850131992,-0.9910399864230198]
  , sgdTestCase "trainAR" ar2SinLoss (3, [], [])
                (return $ take 30000 samples) 6.327978161031336e-23
  , feedbackTestCase "feedbackAR" ar2Sin ar2SinLoss
                     (3, [], [])
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

hiddenLayerMnistRNNL :: (DeltaMonad r m, Floating (Vector r))
                     => Vector r
                     -> DualNumber (Vector r)
                     -> DualNumberVariables r
                     -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerMnistRNNL x s variables = do
  let wX = varL variables 0  -- 128x28
      wS = varL variables 1  -- 128x128
      b = varV variables 0  -- 128
      y = wX #>!! x + wS #>! s + b
  yTanh <- tanhAct y
  return (yTanh, yTanh)  -- tanh in both, as per https://github.com/keras-team/keras/blob/v2.8.0/keras/layers/legacy_rnn/rnn_cell_impl.py#L468

middleLayerMnistRNNL :: (DeltaMonad r m, Floating (Vector r))
                     => DualNumber (Vector r)
                     -> DualNumber (Vector r)
                     -> DualNumberVariables r
                     -> m (DualNumber (Vector r), DualNumber (Vector r))
middleLayerMnistRNNL vec s variables = do
  let wX = varL variables 3  -- 128x128
      wS = varL variables 4  -- 128x128
      b = varV variables 2  -- 128
      y = wX #>! vec + wS #>! s + b
  yTanh <- tanhAct y
  return (yTanh, yTanh)

outputLayerMnistRNNL :: DeltaMonad r m
                     => DualNumber (Vector r)
                     -> DualNumberVariables r
                     -> m (DualNumber (Vector r))
outputLayerMnistRNNL vec variables = do
  let w = varL variables 2  -- 10x128
      b = varV variables 1  -- 10
  returnLet $ w #>! vec + b  -- I assume there is no activations, as per https://www.tensorflow.org/api_docs/python/tf/compat/v1/layers/dense

fcfcrnnMnistL :: (DeltaMonad r m, Floating (Vector r))
              => Vector r
              -> DualNumber (Vector r)
              -> DualNumberVariables r
              -> m (DualNumber (Vector r), DualNumber (Vector r))
fcfcrnnMnistL = hiddenLayerMnistRNNL

fcfcrnnMnistL2 :: (DeltaMonad r m, Floating (Vector r))
               => Vector r
               -> DualNumber (Vector r)
               -> DualNumberVariables r
               -> m (DualNumber (Vector r), DualNumber (Vector r))
fcfcrnnMnistL2 x s@(D u _) variables = do
  let len = V.length u `div` 2
      s1 = slice1 0 len s
      s2 = slice1 len len s
  (vec1, s1') <- hiddenLayerMnistRNNL x s1 variables
  (vec2, s2') <- middleLayerMnistRNNL vec1 s2 variables
  return (vec2, append1 s1' s2')

unrollLastG :: forall a b c m r. DeltaMonad r m
            => (a -> b -> DualNumberVariables r -> m (c, b))
            -> ([a] -> b -> DualNumberVariables r -> m (c, b))
unrollLastG f xs s0 variables =
  let g :: (c, b) -> a -> m (c, b)
      g (_, s) x = f x s variables
  in foldM g (undefined, s0) xs

nnMnistRNNL :: (DeltaMonad r m, Floating (Vector r))
            => Int
            -> [Vector r]
            -> DualNumberVariables r
            -> m (DualNumber (Vector r))
nnMnistRNNL width x variables = do
  rnnLayer <- zeroState width (unrollLastG fcfcrnnMnistL) x variables
  outputLayerMnistRNNL rnnLayer variables

nnMnistRNNL2 :: (DeltaMonad r m, Floating (Vector r))
             => Int
             -> [Vector r]
             -> DualNumberVariables r
             -> m (DualNumber (Vector r))
nnMnistRNNL2 width x variables = do
  rnnLayer <- zeroState (2 * width) (unrollLastG fcfcrnnMnistL2) x variables
  outputLayerMnistRNNL rnnLayer variables

nnMnistRNNLossL :: (DeltaMonad r m, Fractional r, Floating (Vector r))
                => Int
                -> ([Vector r], Vector r)
                -> DualNumberVariables r
                -> m (DualNumber r)
nnMnistRNNLossL width (xs, target) variables = do
  result <- nnMnistRNNL width xs variables
  lossSoftMaxCrossEntropyV target result

nnMnistRNNLossL2 :: (DeltaMonad r m, Fractional r, Floating (Vector r))
                 => Int
                 -> ([Vector r], Vector r)
                 -> DualNumberVariables r
                 -> m (DualNumber r)
nnMnistRNNLossL2 width (xs, target) variables = do
  result <- nnMnistRNNL2 width xs variables
  lossSoftMaxCrossEntropyV target result

testMnistRNNL :: forall r. (Ord r, Floating r, IsScalar r, Floating (Vector r))
              => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNL width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNL width glyph
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

testMnistRNNL2 :: forall r. (Ord r, Floating r, IsScalar r, Floating (Vector r))
               => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNL2 width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNL2 width glyph
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

-- A version written using vectors

hiddenLayerMnistRNNV :: (DeltaMonad r m, Floating (Vector r))
                     => Int
                     -> Vector r
                     -> DualNumber (Vector r)
                     -> DualNumberVariables r
                     -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerMnistRNNV width x s variables = do
  let b = varV variables (width + width)  -- 128
      y = sumConstantDataL x 0 variables width
          + sumTrainableInputsL s width variables width
          + b
  yTanh <- tanhAct y
  return (yTanh, yTanh)

outputLayerMnistRNNV :: DeltaMonad r m
                     => Int
                     -> DualNumber (Vector r)
                     -> DualNumberVariables r
                     -> m (DualNumber (Vector r))
outputLayerMnistRNNV width vec variables = do
  let b = varV variables (width + width + 1 + 10)  -- 10
  returnLet $ sumTrainableInputsL vec (width + width + 1) variables 10 + b

fcfcrnnMnistV :: (DeltaMonad r m, Floating (Vector r))
              => Int
              -> Vector r
              -> DualNumber (Vector r)
              -> DualNumberVariables r
              -> m (DualNumber (Vector r), DualNumber (Vector r))
fcfcrnnMnistV = hiddenLayerMnistRNNV

nnMnistRNNV :: (DeltaMonad r m, Floating (Vector r))
            => Int
            -> [Vector r]
            -> DualNumberVariables r
            -> m (DualNumber (Vector r))
nnMnistRNNV width x variables = do
  rnnLayer <- zeroState width (unrollLastG $ fcfcrnnMnistV width) x variables
  outputLayerMnistRNNV width rnnLayer variables

nnMnistRNNLossV :: (DeltaMonad r m, Fractional r, Floating (Vector r))
                => Int
                -> ([Vector r], Vector r)
                -> DualNumberVariables r
                -> m (DualNumber r)
nnMnistRNNLossV width (xs, target) variables = do
  result <- nnMnistRNNV width xs variables
  lossSoftMaxCrossEntropyV target result

testMnistRNNV :: forall r. (Ord r, Floating r, IsScalar r, Floating (Vector r))
              => Int -> [([Vector r], Vector r)] -> Domains r -> r
testMnistRNNV width inputs parameters =
  let matchesLabels :: ([Vector r], Vector r) -> Bool
      matchesLabels (glyph, label) =
        let nn = nnMnistRNNV width glyph
            value = primalValue nn parameters
        in V.maxIndex value == V.maxIndex label
  in fromIntegral (length (filter matchesLabels inputs))
     / fromIntegral (length inputs)

lenMnistRNNL :: Int -> Int -> (Int, [Int], [(Int, Int)])
lenMnistRNNL width nLayers =
  ( 0
  , [width, 10] ++ replicate (nLayers - 1) width
  , [(width, 28), (width, width), (10, width)]
    ++ concat (replicate (nLayers - 1) [(width, width), (width, width)])
  )

lenMnistRNNV :: Int -> Int -> (Int, [Int], [(Int, Int)])
lenMnistRNNV width nLayers =
  ( 0
  , replicate width 28 ++ replicate width width ++ [width]
    ++ replicate 10 width ++ [10]
    ++ concat (replicate (nLayers - 1)
                (replicate width width ++ replicate width width ++ [width]))
  , []
  )

mnistTestCaseRNN
  :: String
  -> Int
  -> Int
  -> (Int
      -> ([Vector Double], Vector Double)
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> (Int -> [([Vector Double], Vector Double)] -> Domains Double -> Double)
  -> (Int -> Int -> (Int, [Int], [(Int, Int)]))
  -> Int
  -> Int
  -> Double
  -> TestTree
mnistTestCaseRNN prefix epochs maxBatches f ftest flen width nLayers
                 expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, parameters0) =
        initializerFixed 44 0.2 (flen width nLayers)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show nLayers
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show range ]
  in testCase name $ do
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
             printf "(Batch %d with %d points)\n" k (length chunk)
             let res@(parameters2, _) =
                   sgdAdamBatch 150 (f width) chunk parameters stateAdam
                 trainScore = ftest width chunk parameters2
                 testScore = ftest width testData parameters2
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
           runEpoch :: Int
                    -> (Domains Double, StateAdam Double)
                    -> IO (Domains Double)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 (parameters0, initialStateAdam parameters0)
       let testErrorFinal = 1 - ftest width testData res
       testErrorFinal @?= expected

-- A version written using matrices to express mini-batches of data
-- and so using matrix multiplication to run the neural net.

hiddenLayerMnistRNNB :: (DeltaMonad r m, Floating (Matrix r))
                     => Matrix r  -- the mini-batch of data 28x150
                     -> DualNumber (Matrix r)  -- state for mini-batch 128x150
                     -> DualNumberVariables r
                     -> m (DualNumber (Matrix r), DualNumber (Matrix r))
hiddenLayerMnistRNNB x s variables = do
  let wX = varL variables 0  -- 128x28
      wS = varL variables 1  -- 128x128
      b = varV variables 0  -- 128
      batchSize = HM.cols x
      y = wX <>!! x + wS <>! s + asColumn2 b batchSize
  yTanh <- returnLet $ tanh y
  return (yTanh, yTanh)

middleLayerMnistRNNB :: (DeltaMonad r m, Floating (Matrix r))
                     => DualNumber (Matrix r)  -- 128x150
                     -> DualNumber (Matrix r)  -- 128x150
                     -> DualNumberVariables r
                     -> m (DualNumber (Matrix r), DualNumber (Matrix r))
middleLayerMnistRNNB batchOfVec@(D u _) s variables = do
  let wX = varL variables 3  -- 128x128
      wS = varL variables 4  -- 128x128
      b = varV variables 2  -- 128
      batchSize = HM.cols u
      y = wX <>! batchOfVec + wS <>! s + asColumn2 b batchSize
  yTanh <- returnLet $ tanh y
  return (yTanh, yTanh)

outputLayerMnistRNNB :: DeltaMonad r m
                     => DualNumber (Matrix r)  -- 128x150
                     -> DualNumberVariables r
                     -> m (DualNumber (Matrix r))
outputLayerMnistRNNB batchOfVec@(D u _) variables = do
  let w = varL variables 2  -- 10x128
      b = varV variables 1  -- 10
      batchSize = HM.cols u
  returnLet $ w <>! batchOfVec + asColumn2 b batchSize

fcfcrnnMnistB :: (DeltaMonad r m, Floating (Matrix r))
              => Matrix r
              -> DualNumber (Matrix r)
              -> DualNumberVariables r
              -> m (DualNumber (Matrix r), DualNumber (Matrix r))
fcfcrnnMnistB = hiddenLayerMnistRNNB

fcfcrnnMnistB2 :: (DeltaMonad r m, Floating (Matrix r))
               => Matrix r  -- 28x150
               -> DualNumber (Matrix r)  -- 256x150
               -> DualNumberVariables r
               -> m (DualNumber (Matrix r), DualNumber (Matrix r))
fcfcrnnMnistB2 x s@(D u _) variables = do
  let len = HM.rows u `div` 2
      s1 = rowSlice2 0 len s
      s2 = rowSlice2 len len s
  (vec1, s1') <- hiddenLayerMnistRNNB x s1 variables
  (vec2, s2') <- middleLayerMnistRNNB vec1 s2 variables
  return (vec2, rowAppend2 s1' s2')

zeroStateB :: DeltaMonad r m
           => (Int, Int)
           -> (a
               -> DualNumber (Matrix r)
               -> DualNumberVariables r
               -> m (DualNumber r2, DualNumber (Matrix r)))
           -> (a
               -> DualNumberVariables r
               -> m (DualNumber r2))
zeroStateB ij f xs variables =
  fst <$> f xs (scalar $ HM.konst 0 ij) variables

nnMnistRNNB :: (DeltaMonad r m, Floating (Matrix r))
            => Int
            -> [Matrix r]
            -> DualNumberVariables r
            -> m (DualNumber (Matrix r))
nnMnistRNNB width xs variables = do
  let batchSize = HM.cols $ head xs
  rnnLayer <- zeroStateB (width, batchSize) (unrollLastG fcfcrnnMnistB)
                         xs variables
  outputLayerMnistRNNB rnnLayer variables

nnMnistRNNB2 :: (DeltaMonad r m, Floating (Matrix r))
             => Int
             -> [Matrix r]
             -> DualNumberVariables r
             -> m (DualNumber (Matrix r))
nnMnistRNNB2 width xs variables = do
  let batchSize = HM.cols $ head xs
  rnnLayer <- zeroStateB (2 * width, batchSize) (unrollLastG fcfcrnnMnistB2)
                         xs variables
  outputLayerMnistRNNB rnnLayer variables

nnMnistRNNLossB :: (DeltaMonad r m, Fractional r, Floating (Matrix r))
                => Int
                -> ([Matrix r], Matrix r)
                -> DualNumberVariables r
                -> m (DualNumber r)
nnMnistRNNLossB width (xs, target) variables = do
  result <- nnMnistRNNB width xs variables
  vec@(D u _) <- lossSoftMaxCrossEntropyL target result
    -- this @asRow@ is safe, because it gets multiplied/subtracted right away
  returnLet $ scale (recip $ fromIntegral $ V.length u) $ sumElements0 vec

nnMnistRNNLossB2 :: (DeltaMonad r m, Fractional r, Floating (Matrix r))
                 => Int
                 -> ([Matrix r], Matrix r)
                 -> DualNumberVariables r
                 -> m (DualNumber r)
nnMnistRNNLossB2 width (xs, target) variables = do
  result <- nnMnistRNNB2 width xs variables
  vec@(D u _) <- lossSoftMaxCrossEntropyL target result
  returnLet $ scale (recip $ fromIntegral $ V.length u) $ sumElements0 vec

mnistTestCaseRNNB
  :: String
  -> Int
  -> Int
  -> (Int
      -> ([Matrix Double], Matrix Double)
      -> DualNumberVariables Double
      -> DeltaMonadGradient Double (DualNumber Double))
  -> (Int -> [([Vector Double], Vector Double)] -> Domains Double -> Double)
  -> (Int -> Int -> (Int, [Int], [(Int, Int)]))
  -> Int
  -> Int
  -> Double
  -> TestTree
mnistTestCaseRNNB prefix epochs maxBatches f ftest flen width nLayers
                  expected =
  let ((nParams, nParamsV, nParamsL), totalParams, range, parameters0) =
        initializerFixed 44 0.2 (flen width nLayers)
      name = prefix ++ " "
             ++ unwords [ show epochs, show maxBatches
                        , show width, show nLayers
                        , show nParams, show nParamsV, show nParamsL
                        , show totalParams, show range ]
  in testCase name $ do
       let rws (input, target) =
             ( map (\k -> V.slice (k * 28) 28 input) [0 .. 27]
             , target )
       trainData <- map rws <$> loadMnistData trainGlyphsPath trainLabelsPath
       testData <- map rws <$> loadMnistData testGlyphsPath testLabelsPath
       let packChunk :: [([Vector Double], Vector Double)]
                     -> ([Matrix Double], Matrix Double)
           packChunk chunk =
             let (inputs, outputs) = unzip chunk
                 behead !acc ([] : _) = reverse acc
                 behead !acc l = behead (HM.fromColumns (map head l) : acc)
                                        (map tail l)
             in (behead [] inputs, HM.fromColumns outputs)
           -- There is some visual feedback, because some of these take long.
           runBatch :: (Domains Double, StateAdam Double)
                    -> (Int, [([Vector Double], Vector Double)])
                    -> IO (Domains Double, StateAdam Double)
           runBatch (parameters@(!_, !_, !_, !_), stateAdam) (k, chunk) = do
             printf "(Batch %d with %d points)\n" k (length chunk)
             let res@(parameters2, _) =
                   sgdAdam (f width) (map packChunk $ chunksOf 150 chunk)
                           parameters stateAdam
                 trainScore = ftest width chunk parameters2
                 testScore = ftest width testData parameters2
             printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
             printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)
             return res
           runEpoch :: Int
                    -> (Domains Double, StateAdam Double)
                    -> IO (Domains Double)
           runEpoch n (params2, _) | n > epochs = return params2
           runEpoch n paramsStateAdam = do
             printf "[Epoch %d]\n" n
             let trainDataShuffled = shuffle (mkStdGen $ n + 5) trainData
                 chunks = take maxBatches
                          $ zip [1 ..] $ chunksOf 5000 trainDataShuffled
             !res <- foldM runBatch paramsStateAdam chunks
             runEpoch (succ n) res
       printf "\nEpochs to run/max batches per epoch: %d/%d\n"
              epochs maxBatches
       res <- runEpoch 1 (parameters0, initialStateAdam parameters0)
       let testErrorFinal = 1 - ftest width testData res
       testErrorFinal @?= expected

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
  ]

mnistRNNTestsShort :: TestTree
mnistRNNTestsShort = testGroup "MNIST RNN short tests"
  [ let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 99]
    in sgdTestCase "randomLL 100"
                   (nnMnistRNNLossL 128)
                   (lenMnistRNNL 128 1)
                   (return trainData)
                   49.01483873645264
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstLL 100 trainset samples only"
                   (nnMnistRNNLossL 128)
                   (lenMnistRNNL 128 1)
                   (map rws . take 100
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.779085689596527
  , mnistTestCaseRNN "1LL 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossL testMnistRNNL lenMnistRNNL 128 1
                     0.2845
  , mnistTestCaseRNNB "1BB 1 epoch, 1 batch" 1 1
                      nnMnistRNNLossB testMnistRNNL lenMnistRNNL 128 1
                      0.2845
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 99]
    in sgdTestCase "randomLL2 100"
                   (nnMnistRNNLossL2 128)
                   (lenMnistRNNL 128 2)
                   (return trainData)
                   29.99398928593454
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstLL2 99 trainset samples only"
                   (nnMnistRNNLossL2 128)
                   (lenMnistRNNL 128 2)
                   (map rws . take 99
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.772595855528805
  , mnistTestCaseRNN "1LL2 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossL2 testMnistRNNL2 lenMnistRNNL 128 2
                     0.2945
  , mnistTestCaseRNNB "1BB2 1 epoch, 1 batch" 1 1
                      nnMnistRNNLossB2 testMnistRNNL2 lenMnistRNNL 128 2
                      0.2945
  , let glyph = V.unfoldrExactN sizeMnistGlyph (uniformR (0, 1))
        label = V.unfoldrExactN sizeMnistLabel (uniformR (0, 1))
        rws v = map (\k -> V.slice (k * 28) 28 v) [0 .. 27]
        trainData = map ((\g -> (rws (glyph g), label g)) . mkStdGen) [1 .. 100]
    in sgdTestCase "randomVV 100"
                   (nnMnistRNNLossV 128)
                   (lenMnistRNNV 128 1)
                   (return trainData)
                   48.93543453075899
  , let rws (input, target) =
          (map (\k -> V.slice (k * 28) 28 input) [0 .. 27], target)
    in sgdTestCase "firstVV 100 trainset samples only"
                   (nnMnistRNNLossV 128)
                   (lenMnistRNNV 128 1)
                   (map rws . take 100
                    <$> loadMnistData trainGlyphsPath trainLabelsPath)
                   2.7494107689380805
  , mnistTestCaseRNN "1VV 1 epoch, 1 batch" 1 1
                     nnMnistRNNLossV testMnistRNNV lenMnistRNNV 128 1
                     0.3024
  ]
