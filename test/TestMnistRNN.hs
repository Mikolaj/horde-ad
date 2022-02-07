module TestMnistRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Data.List (foldl', unfoldr)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector, konst, uniformSample)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.MnistTools

testTrees :: [TestTree]
testTrees = [ sinRNNTests
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ sinRNNTests
                      ]


-- * A recurrent net for sine, input 1, state/hidden 30, output 1, following
-- https://blog.jle.im/entry/purely-functional-typed-models-2.html
-- and obtaining matching results

-- A version written using matrices

hiddenLayerSinRNN :: (DeltaMonad r m, Numeric r, Floating (Vector r))
                  => r
                  -> DualNumber (Vector r)
                  -> DualNumberVariables r
                  -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerSinRNN x s variables = do
  let wX = varL variables 0
      wS = varL variables 1
      b = varV variables 0
  y <- returnLetV $ wX #>!! V.singleton x + wS #>! s + b
  yLogistic <- logisticActV y
  return (y, yLogistic)

outputLayerSinRNN :: (DeltaMonad r m, Numeric r)
                  => DualNumber (Vector r)
                  -> DualNumberVariables r
                  -> m (DualNumber r)
outputLayerSinRNN vec variables = do
  let w = varV variables 1
      b = var variables 0
  returnLet $ w <.>! vec + b

fcfcrnn :: (DeltaMonad r m, Numeric r, Floating (Vector r))
        => r
        -> DualNumber (Vector r)
        -> DualNumberVariables r
        -> m (DualNumber r, DualNumber (Vector r))
fcfcrnn x s variables = do
  (hiddenLayer, sHiddenLayer) <- hiddenLayerSinRNN x s variables
  outputLayer <- outputLayerSinRNN hiddenLayer variables
  return (outputLayer, sHiddenLayer)

unrollLast' :: forall m r. (DeltaMonad r m, Numeric r)
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

zeroState :: (DeltaMonad r m, Numeric r)
          => (Vector r
              -> DualNumber (Vector r)
              -> DualNumberVariables r
              -> m (DualNumber r, DualNumber (Vector r)))
          -> (Vector r
              -> DualNumberVariables r
              -> m (DualNumber r))
zeroState f xs variables =
  fst <$> f xs (scalar $ konst 0 30) variables

nnSinRNN :: (DeltaMonad r m, Numeric r, Floating (Vector r))
         => Vector r
         -> DualNumberVariables r
         -> m (DualNumber r)
nnSinRNN = zeroState (unrollLast' fcfcrnn)

nnSinRNNLoss :: (DeltaMonad r m, Numeric r, Floating (Vector r))
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

sgdShow :: (Eq r, Fractional r, Numeric r, Num (Vector r))
        => (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> [a]
        -> Domains r
        -> r
sgdShow f trainData parameters =
  let result = sgd 0.1 f trainData parameters
  in snd $ df (f $ head trainData) result

sgdTestCase :: String
            -> (a
                -> DualNumberVariables Double
                -> DeltaMonadGradient Double (DualNumber Double))
            -> (Int, [Int], [(Int, Int)])
            -> [a]
            -> Double
            -> TestTree
sgdTestCase prefix f (nParams, nParamsV, nParamsL) trainData expected =
  let params0 = V.unfoldrExactN nParams (uniformR (-0.05, 0.05)) $ mkStdGen 44
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.05, 0.05))
                                          (mkStdGen $ 44 + nPV + i))
               (V.fromList nParamsV)
      paramsL0 = V.imap (\i (rows, cols) ->
                           uniformSample (44 + rows + i) rows
                                         (replicate cols (-0.05, 0.05)))
                        (V.fromList nParamsL)
      totalParams = nParams + sum nParamsV
                    + sum (map (uncurry (*)) nParamsL)
      name = prefix ++ " "
             ++ unwords [ show nParams, show (length nParamsV)
                        , show (length nParamsL), show totalParams ]
  in testCase name $
       sgdShow f trainData (params0, paramsV0, paramsL0)
       @?= expected

prime :: Numeric r
      => (r
          -> DualNumber (Vector r)
          -> DualNumberVariables r
          -> DeltaMonadValue Double (DualNumber r, DualNumber (Vector r)))
      -> Domains r
      -> Vector r
      -> [r]
      -> Vector r
prime f parameters s0 as =
  foldl' (\s x ->
            primalValue (\vs -> snd <$> f x (scalar s) vs) parameters) s0 as

feedback :: Numeric r
         => (r
             -> DualNumber (Vector r)
             -> DualNumberVariables r
             -> DeltaMonadValue Double (DualNumber r, DualNumber (Vector r)))
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
feedbackTestCase prefix fp f (nParams, nParamsV, nParamsL) trainData expected =
  let params0 = V.unfoldrExactN nParams (uniformR (-0.05, 0.05)) $ mkStdGen 44
      paramsV0 =
        V.imap (\i nPV -> V.unfoldrExactN nPV (uniformR (-0.05, 0.05))
                                          (mkStdGen $ 44 + nPV + i))
               (V.fromList nParamsV)
      paramsL0 = V.imap (\i (rows, cols) ->
                           uniformSample (44 + rows + i) rows
                                         (replicate cols (-0.05, 0.05)))
                        (V.fromList nParamsL)
      totalParams = nParams + sum nParamsV
                    + sum (map (uncurry (*)) nParamsL)
      name = prefix ++ " "
             ++ unwords [ show nParams, show (length nParamsV)
                        , show (length nParamsL), show totalParams ]
      trained = sgd 0.1 f trainData (params0, paramsV0, paramsL0)
      primed = prime fp trained (konst 0 30) (take 19 series)
      output = feedback fp trained primed (series !! 19)
  in testCase name $
       take 30 output @?= expected

-- A version written using vectors

hiddenLayerSinRNNV :: (DeltaMonad r m, Numeric r, Floating (Vector r))
                   => r
                   -> DualNumber (Vector r)
                   -> DualNumberVariables r
                   -> m (DualNumber (Vector r), DualNumber (Vector r))
hiddenLayerSinRNNV x s variables = do
  let wX = varV variables 0
      b = varV variables 31
  y <- returnLetV
       $ scale (konst x 30) wX + sumTrainableInputsL s 1 variables 30 + b
  yLogistic <- logisticActV y
  return (y, yLogistic)

outputLayerSinRNNV :: (DeltaMonad r m, Numeric r)
                   => DualNumber (Vector r)
                   -> DualNumberVariables r
                   -> m (DualNumber r)
outputLayerSinRNNV vec variables = do
  let w = varV variables 32
      b = var variables 0
  returnLet $ w <.>! vec + b

fcfcrnnV :: (DeltaMonad r m, Numeric r, Floating (Vector r))
         => r
         -> DualNumber (Vector r)
         -> DualNumberVariables r
         -> m (DualNumber r, DualNumber (Vector r))
fcfcrnnV x s variables = do
  (hiddenLayer, sHiddenLayer) <- hiddenLayerSinRNNV x s variables
  outputLayer <- outputLayerSinRNNV hiddenLayer variables
  return (outputLayer, sHiddenLayer)

nnSinRNNLossV :: (DeltaMonad r m, Numeric r, Floating (Vector r))
              => (Vector r, r)
              -> DualNumberVariables r
              -> m (DualNumber r)
nnSinRNNLossV (xs, target) variables = do
  result <- zeroState (unrollLast' fcfcrnnV) xs variables
  lossSquared target result

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)])
                (take 30000 samples) 2.7767078390174838e-5
  , feedbackTestCase "feedback" fcfcrnn nnSinRNNLoss
                     (1, [30, 30], [(30, 1), (30, 30)])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9635969636166014,-0.8852952626226361,-0.7642608678210426,-0.6022770608206665,-0.4033390312094312,-0.17537818420131487,6.879282387447619e-2,0.31226627184414224,0.5368846584179489,0.7271314393668484,0.8730549544002943,0.9707639759459372,1.0207324787951833,1.0253326233680582,0.986900394287602,0.9068894463306796,0.7861024783590012,0.6257839317393192,0.42928109139491266,0.20379685354628732,-3.855688343960128e-2,-0.281343520120466,-0.5064405440888685,-0.6978715569402032,-0.8448912129493893,-0.9427585471613646,-0.9912623762593421,-0.9923429067482449,-0.9481655850002165]
  , sgdTestCase "trainVV" nnSinRNNLossV (1, replicate 33 30, [])
                (take 30000 samples) 3.396124727552674e-5
      -- different random initial paramaters produce a worse result;
      -- matrix implementation faster, because the matrices still fit in cache
  , feedbackTestCase "feedbackVV" fcfcrnnV nnSinRNNLossV
                     (1, replicate 33 30, [])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9634123298992812,-0.8847335504597839,-0.7622853687776576,-0.5962848755420429,-0.38884074710283445,-0.14654599247925756,0.11757603905860295,0.38437938161262064,0.6323324161445587,0.8436159306746334,1.009006310264001,1.1284972482500732,1.2081446932687734,1.2560009904674736,1.2792814156548193,1.2831268046191948,1.2703983550132165,1.2419052564483004,1.1967293095390061,1.1325415817990008,1.0459466765807786,0.9329720084923336,0.789865350066696,0.6143550789522167,0.4073941707753075,0.17505714838370537,-7.029722905472535e-2,-0.31086676131884383,-0.5269348888108187]
  ]
