module Main (main) where

import Prelude

import Test.Tasty

import qualified ConditionalSynth
import qualified MnistFC
import qualified Outdated
import qualified SimpleDescent
import qualified SingleGradient

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" $
  SingleGradient.testTrees
  ++ SimpleDescent.testTrees
  ++ Outdated.testTrees
--  ++ ConditionalSynth.testTrees
  ++ MnistFC.testTrees
