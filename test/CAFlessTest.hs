module Main (main) where

import Prelude

import Data.Proxy
import System.IO qualified as SIO
import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Runners

import EqEpsilon
import TestAdaptorSimplified qualified
import TestConvQuickCheck qualified
import TestConvSimplified qualified
import TestGatherSimplified qualified
import TestHighRankSimplified qualified
import TestMnistPP qualified
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
  testGroup "Tests for simplified horde-ad that don't create big CAFs"
    [ testGroup "Short_tests"
        (TestAdaptorSimplified.testTrees
         ++ TestConvQuickCheck.testTrees
         ++ TestConvSimplified.testTrees
         ++ TestGatherSimplified.testTrees
         ++ TestHighRankSimplified.testTrees
         ++ TestRevFwdFold.testTrees
         ++ TestMnistPP.testTrees)
    ]
