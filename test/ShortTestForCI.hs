{-# LANGUAGE CPP #-}
#if defined(VERSION_ghc_typelits_natnormalise)
-- Not really used here, but this squashes a warning caused by a hack
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
module Main (main) where

import Prelude
import Data.Typeable

import qualified System.IO as SIO
import           Test.Tasty
import           Test.Tasty.Options

#if defined(VERSION_ghc_typelits_natnormalise)
import qualified TestMnistCNN
import qualified TestMnistFCNN
import qualified TestMnistRNN
import qualified TestSimpleDescent
import qualified TestSingleGradient
#endif

newtype EqEpsilon = EqEpsilon Double
  deriving Typeable

instance IsOption EqEpsilon where
  defaultValue = EqEpsilon 1e-4
  parseValue = fmap EqEpsilon . safeRead
  optionName = return "eq-epsilon"
  optionHelp = return "Epsilon to use for floating point comparisons: abs(a-b) < epsilon"

main :: IO ()
main = do
  -- Limit interleaving of characters in parallel tests.
  SIO.hSetBuffering SIO.stdout SIO.LineBuffering
  SIO.hSetBuffering SIO.stderr SIO.LineBuffering
  defaultMainWithIngredients (ingredients : defaultIngredients) $ askOption $ \(EqEpsilon eqEps) -> tests eqEps
  where
    ingredients = includingOptions [Option (Proxy :: Proxy EqEpsilon)]

tests :: Double -> TestTree
tests eqEpsilon = testGroup "Short tests for CI" $
#if defined(VERSION_ghc_typelits_natnormalise)
  TestSingleGradient.testTrees
  ++ TestSimpleDescent.testTrees
  ++ TestMnistFCNN.shortTestForCITrees eqEpsilon
  ++ TestMnistRNN.shortTestForCITrees
  ++ TestMnistCNN.shortTestForCITrees
#else
  []
#endif
