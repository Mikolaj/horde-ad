module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import qualified TestSimplified


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Only special tests for simplified horde-ad" $
--  TestHighRankSimplified.testTrees
--  ++ TestBuildSimplified.testTrees
--  ++ TestAdaptorSimplified.testTrees
   TestSimplified.testTrees
--  ++ [TestGradientSimple.finalCounter]
