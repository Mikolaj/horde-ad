{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fspecialise-aggressively #-}
-- | Assorted mostly high rank tensor tests.
module TestHighRankSimplified (testTrees) where

import Prelude

import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import HordeAd

import CrossTesting

testTrees :: [TestTree]
testTrees =
  [ testCase "3concatBuild22" testConcatBuild22
  ]

concatBuild2 :: forall ranked r. ( ADReady ranked, GoodScalar r )
             => ranked r 15 -> ranked r 17
concatBuild2 r =
  tbuild1 5 (\i ->
    tbuild1 2 (\j -> tmap0N (* tfromIndex0 (maxF j (i `quot` (j + 1)))) r))

testConcatBuild22 :: Assertion
testConcatBuild22 =
  let !_ = revShort @Double concatBuild2 t48
  in return ()
