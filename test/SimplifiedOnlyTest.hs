module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import           EqEpsilon
import qualified TestAdaptorSimplified
import qualified TestConvSimplified
import qualified TestGatherSimplified
import qualified TestHighRankSimplified
import qualified TestMnistCNNR
import qualified TestMnistFCNNR
import qualified TestMnistRNNR

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
tests = testGroup "Only special tests for simplified horde-ad" $
  TestGatherSimplified.testTrees
  ++ TestHighRankSimplified.testTrees
  ++ TestConvSimplified.testTrees
  ++ TestAdaptorSimplified.testTrees
  ++ TestMnistFCNNR.testTrees
  ++ TestMnistRNNR.testTrees
  ++ TestMnistCNNR.testTrees
