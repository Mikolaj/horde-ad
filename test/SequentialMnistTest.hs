module Main (main) where

import Prelude

import Data.Proxy
import System.IO qualified as SIO
import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Runners

import EqEpsilon
import TestMnistCNNR qualified
import TestMnistCNNS qualified
import TestMnistFCNNR qualified
import TestMnistRNNR qualified
import TestMnistRNNS qualified

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
  inOrderTestGroup "The set of MNIST tests for horde-ad that can serve as a benchmark when run sequentially"
    [ inOrderTestGroup "Long_tests"
        (TestMnistCNNR.testTrees
         ++ TestMnistCNNS.testTrees
         ++ TestMnistFCNNR.testTrees
         ++ TestMnistRNNR.testTrees
         ++ TestMnistRNNS.testTrees)
    ]
