module Main (main) where

import Prelude

import           Data.Proxy
import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options
import           Test.Tasty.Runners

import           EqEpsilon
import qualified TestGatherSimplified

import GHC.Debug.Stub

main :: IO ()
main = withGhcDebug normalMain

normalMain :: IO ()
normalMain = TestGatherSimplified.testGatherNested1
