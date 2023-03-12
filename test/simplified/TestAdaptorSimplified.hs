{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (inputConstant)

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
  ]
