module Main (main) where

import Prelude

import Data.Proxy
import System.IO qualified as SIO
import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Runners

import EqEpsilon
import TestAdaptorSimplified qualified
import TestConvSimplified qualified
import TestGatherSimplified qualified
import TestHighRankSimplified qualified
import TestMnistCNNR qualified
import TestMnistFCNNR qualified
import TestMnistPP qualified
import TestMnistRNNR qualified
import TestMnistRNNS qualified
import TestRevFwdFold qualified

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
tests =
  testGroup "Full set of tests for simplified horde-ad"
    [ testGroup "Short_tests"
        (TestAdaptorSimplified.testTrees
         ++ TestConvSimplified.testTrees
         ++ TestGatherSimplified.testTrees
         ++ TestHighRankSimplified.testTrees
         ++ TestRevFwdFold.testTrees
         ++ TestMnistPP.testTrees)
    , testGroup "Long_tests"
        (TestMnistCNNR.testTrees
         ++ TestMnistFCNNR.testTrees
         ++ TestMnistRNNR.testTrees
         ++ TestMnistRNNS.testTrees)
    ]
