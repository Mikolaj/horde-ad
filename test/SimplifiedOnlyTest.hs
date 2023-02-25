module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import qualified TestAdaptorSimplified
import qualified TestBuildSimplified
import qualified TestGatherSimplified
import qualified TestGradientSimple
import qualified TestHighRankSimplified
import qualified TestSimplified
import           Tool.EqEpsilon

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
  ++ TestBuildSimplified.testTrees
  ++ TestAdaptorSimplified.testTrees
  ++ TestSimplified.testTrees
  ++ [TestGradientSimple.finalCounter]
