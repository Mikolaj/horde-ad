module Main (main) where

import Prelude

import Test.Tasty

import qualified TestConditionalSynth
import qualified TestMnistCNN
import qualified TestMnistFCNN
import qualified TestMnistRNN
import qualified TestOutdated
import qualified TestSimpleDescent
import qualified TestSingleGradient

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" $
  TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
  ++ TestOutdated.testTrees
  ++ TestConditionalSynth.testTrees
  ++ TestMnistFCNN.testTrees
  ++ TestMnistRNN.testTrees
  ++ TestMnistCNN.testTrees
