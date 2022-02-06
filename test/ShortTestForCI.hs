module Main (main) where

import Prelude

import Test.Tasty

import qualified TestMnistFC
import qualified TestMnistRNN
import qualified TestSimpleDescent
import qualified TestSingleGradient

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Short tests for CI" $
  TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
  ++ TestMnistFC.shortTestForCITrees
  ++ TestMnistRNN.testTrees
