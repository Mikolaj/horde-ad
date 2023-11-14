{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fspecialise-aggressively #-}
-- | Assorted mostly high rank tensor tests.
module TestHighRankSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip

import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import HordeAd

import CrossTesting

testTrees :: [TestTree]
testTrees =
  [ testCase "3concatBuild22" testConcatBuild22
  ]

t48 :: Flip OR.Array Double 15
t48 = Flip $ OR.fromList [3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

concatBuild2 :: forall ranked r. ( ADReady ranked, GoodScalar r )
             => ranked r 15 -> ranked r 17
concatBuild2 r =
  tbuild1 5 (\i ->
    tbuild1 2 (\j -> tmap0N (* tfromIndex0 (maxF j (i `quot` (j + 1)))) r))

testConcatBuild22 :: Assertion
testConcatBuild22 =
  let !_ = revShort @Double concatBuild2 t48
  in return ()
