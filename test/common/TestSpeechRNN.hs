{-# LANGUAGE AllowAmbiguousTypes, DataKinds, RankNTypes, TypeFamilies,
             TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestSpeechRNN (testTrees, shortTestForCITrees) where

import Prelude

import           Control.Monad (foldM)
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl', unfoldr)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Matrix, Vector)
import qualified Numeric.LinearAlgebra as HM
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)
import           Text.Printf

-- until stylish-haskell accepts NoStarIsType
import qualified GHC.TypeLits

import HordeAd

testTrees :: [TestTree]
testTrees = [ mnistRNNTestsLong
            , speechRNNTestsShort
            ]

shortTestForCITrees :: [TestTree]
shortTestForCITrees = [ speechRNNTestsShort
                      ]


type SpeechDataBatchS batch_size window_size n_labels r =
  ( OS.Array '[batch_size, window_size] r
  , OS.Array '[batch_size, n_labels] r )

speechTestCaseRNNS
  :: forall out_width batch_size window_size n_labels d r m.
     ( KnownNat out_width, KnownNat batch_size, KnownNat window_size
     , r ~ Double, d ~ 'DModeGradient, m ~ DualMonadGradient Double )
  => String
  -> Int
  -> Int
  -> (forall out_width' batch_size' window_size' n_labels'.
      (DualMonad d r m, KnownNat out_width', KnownNat batch_size')
      => Proxy out_width'
      -> SpeechDataBatchS batch_size' window_size' n_labels' r
      -> DualNumberVariables d r
      -> m (DualNumber d r))
  -> (forall out_width' batch_size' window_size' n_labels'.
      (IsScalar d r, KnownNat out_width', KnownNat batch_size')
      => Proxy out_width'
      -> SpeechDataBatchS batch_size' window_size' n_labels' r
      -> Domains r
      -> r)
  -> (forall out_width'. KnownNat out_width'
      => Proxy out_width' -> (Int, [Int], [(Int, Int)], [OT.ShapeL]))
  -> Double
  -> TestTree
speechTestCaseRNNS prefix epochs maxBatches trainWithLoss ftest flen expected =
  testCase prefix $
    1.0 @?= 1.0

mnistRNNTestsLong :: TestTree
mnistRNNTestsLong = testGroup "Speech RNN long tests"
  []

speechRNNTestsShort :: TestTree
speechRNNTestsShort = testGroup "Speech RNN short tests"
  []
