{-# LANGUAGE CPP #-}
#if defined(VERSION_ghc_typelits_natnormalise)
-- Not really used here, but this squashes a warning caused by a hack
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import qualified TestMnistFCNNSimple
import qualified TestMnistRNNSimple
import           Tool.EqEpsilon

#if defined(VERSION_ghc_typelits_natnormalise)
import qualified TestMnistCNN
import qualified TestMnistFCNN
import qualified TestMnistRNN
import qualified TestSimpleDescent
import qualified TestSingleGradient
#endif

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
tests = testGroup "Short tests for CI" $
  TestMnistFCNNSimple.testTrees
  ++ TestMnistRNNSimple.testTrees
#if defined(VERSION_ghc_typelits_natnormalise)
  ++ TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
  ++ TestMnistFCNN.shortTestForCITrees
  ++ TestMnistRNN.shortTestForCITrees
  ++ TestMnistCNN.shortTestForCITrees
  ++ [TestSingleGradient.finalCounter]
#endif
