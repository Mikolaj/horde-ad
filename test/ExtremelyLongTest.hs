{-# LANGUAGE CPP #-}
module Main (main) where

import Prelude

import qualified System.IO as SIO
import           Test.Tasty

import qualified TestConditionalSynth
import qualified TestOutdated

#if VERSION_ghc_typelits_natnormalise
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
  defaultMain tests

tests :: TestTree
tests = testGroup "Tests" $
  TestOutdated.testTrees
  ++ TestConditionalSynth.testTrees
#if VERSION_ghc_typelits_natnormalise
  ++ TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
  ++ TestMnistFCNN.testTrees
  ++ TestMnistRNN.testTrees
  ++ TestMnistCNN.testTrees
#endif
