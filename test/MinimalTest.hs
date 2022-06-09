{-# LANGUAGE CPP #-}
module Main (main) where

import Prelude

import qualified System.IO as SIO
import           Test.Tasty

#if VERSION_ghc_typelits_natnormalise
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
tests = testGroup "Minimal test that doesn't require any dataset" $
#if VERSION_ghc_typelits_natnormalise
  TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
#else
  []
#endif
