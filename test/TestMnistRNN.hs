{-# LANGUAGE FlexibleContexts #-}
module TestMnistRNN (testTrees, shortTestForCITrees) where

import Prelude

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

sinRNNTests :: TestTree
sinRNNTests = testGroup "Sine RNN tests"
  [ sgdTestCase "train" nnSinRNNLoss (1, [30, 30], [(30, 1), (30, 30)])
                (take 30000 samples) 2.7767078390174838e-5
  ]









--
