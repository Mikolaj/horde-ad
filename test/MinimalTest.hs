module Main (main) where

import Prelude

import qualified System.IO as SIO
import           Test.Tasty

import qualified TestSimpleDescent
import qualified TestSingleGradient

main :: IO ()
main = do
  -- Limit interleaving of characters in parallel tests.
  SIO.hSetBuffering SIO.stdout SIO.LineBuffering
  SIO.hSetBuffering SIO.stderr SIO.LineBuffering
  defaultMain tests

tests :: TestTree
tests = testGroup "Minimal test that doesn't require any dataset" $
  TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
