{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             FunctionalDependencies, RankNTypes, TypeFamilies,
             TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import           Control.Arrow (first)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import Tool.EqEpsilon
import Tool.Shared

testTrees :: [TestTree]
testTrees = []
