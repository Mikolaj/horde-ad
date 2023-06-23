module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import           EqEpsilon
import qualified TestGatherSimplified

main :: IO ()
main = do
  TestGatherSimplified.testGatherNested1
