module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import qualified TestConditionalSynth
import qualified TestDescentSimple
import qualified TestGradientSimple
import qualified TestMnistFCNNSimple
import qualified TestMnistRNNSimple
import           Tool.EqEpsilon

--import qualified TestDescent
--import qualified TestGradient
--import qualified TestMnistCNN
--import qualified TestMnistFCNN
--import qualified TestMnistRNN

main :: IO ()
main = do
  -- Limit interleaving of characters in parallel tests.
  SIO.hSetBuffering SIO.stdout SIO.LineBuffering
  SIO.hSetBuffering SIO.stderr SIO.LineBuffering
  opts <- parseOptions (ingredients : defaultIngredients) tests
  setEpsilonEq (lookupOption opts :: EqEpsilon)
  defaultMainWithIngredients (ingredients : defaultIngredients) tests
  where
    ingredients = includingOptions [Option (Proxy :: Proxy EqEpsilon)]

tests :: TestTree
tests = testGroup "Tests" $
  TestGradientSimple.testTrees
  ++ TestDescentSimple.testTrees
--  ++ TestGradient.testTrees
--  ++ TestDescent.testTrees
--  ++ TestMnistFCNN.testTrees
--  ++ TestMnistRNN.testTrees
--  ++ TestMnistCNN.testTrees
  ++ TestMnistFCNNSimple.testTrees
  ++ TestMnistRNNSimple.testTrees
  ++ TestConditionalSynth.testTrees
  ++ [TestGradientSimple.finalCounter]
