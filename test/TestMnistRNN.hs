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

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)])
                (take 30000 samples) 2.7767078390174838e-5
  , feedbackTestCase "feedback" fcfcrnn nnSinRNNLoss
                     (1, [30, 30], [(30, 1), (30, 30)])
                     (take 10000 samples)
                     [-0.9980267284282716,-0.9635969636166014,-0.8852952626226361,-0.7642608678210426,-0.6022770608206665,-0.4033390312094312,-0.17537818420131487,6.879282387447619e-2,0.31226627184414224,0.5368846584179489,0.7271314393668484,0.8730549544002943,0.9707639759459372,1.0207324787951833,1.0253326233680582,0.986900394287602,0.9068894463306796,0.7861024783590012,0.6257839317393192,0.42928109139491266,0.20379685354628732,-3.855688343960128e-2,-0.281343520120466,-0.5064405440888685,-0.6978715569402032,-0.8448912129493893,-0.9427585471613646,-0.9912623762593421,-0.9923429067482449,-0.9481655850002165]
  ]









--
