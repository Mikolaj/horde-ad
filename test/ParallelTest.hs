{-# LANGUAGE CPP #-}
-- Kept above any CPP conditional: stylish-haskell honors no LANGUAGE pragma
-- that sits below one, and silently leaves such a file unformatted.
module Main (main) where

import Prelude

import Data.Proxy
import System.IO qualified as SIO
import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Runners

import EqEpsilon
import TestConvQuickCheck qualified
import TestMnistCNNR qualified
import TestMnistCNNS qualified
import TestMnistFCNNR qualified
import TestMnistRNNR qualified
import TestMnistRNNS qualified

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
tests =
#ifdef TEST_SEQ
  -- This, not the RTS half of the test_seq flag, is what makes the suite
  -- sequential. tasty picks its concurrency from NumThreads, which defaults
  -- to getNumProcessors and is independent of -N; it then raises capabilities
  -- to match, and only ever raises, so dropping -N from -with-rtsopts leaves
  -- the tests interleaving exactly as before. At NumThreads 1 nothing
  -- interleaves, and the counter in Core/AstFreshId.hs stops being shared.
  localOption (NumThreads 1) $
#endif
  testGroup "The set of tests for horde-ad that can be run in parallel"
    [ testGroup "Long_tests"
        (TestConvQuickCheck.testTrees
         ++ TestMnistCNNR.testTrees
         ++ TestMnistCNNS.testTrees
         ++ TestConvQuickCheck.testTrees  -- saturates cores to prevent OOM
         ++ TestMnistFCNNR.testTrees
         ++ TestConvQuickCheck.testTrees
         ++ TestMnistRNNR.testTrees
         ++ TestConvQuickCheck.testTrees
         ++ TestMnistRNNS.testTrees)
    ]
