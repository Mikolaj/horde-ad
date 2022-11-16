{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

{-
import Prelude

import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd hiding (sumElementsVectorOfDual)

import Tool.EqEpsilon
import Tool.Shared
-}

import Prelude ()

import Test.Tasty

testTrees :: [TestTree]
testTrees = []  -- ATM all new tests already ported to non-simplified
