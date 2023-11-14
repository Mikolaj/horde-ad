{-# LANGUAGE OverloadedLists #-}
-- | Assorted mostly high rank tensor tests.
module TestHighRankSimplified (testTrees) where

import Prelude

import GHC.TypeLits (KnownNat, type (+))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Unsafe.Coerce (unsafeCoerce)

import HordeAd

import CrossTesting

testTrees :: [TestTree]
testTrees =
  [ testCase "3concatBuild22" testConcatBuild22
  ]

concatBuild2 :: forall n ranked r.
                ( ADReady ranked, GoodScalar r
                , KnownNat (1 + n), KnownNat (1 + (1 + n)) )
             => ranked r (1 + n) -> ranked r (3 + n)
concatBuild2 r =
  gcastWith (unsafeCoerce Refl :: 1 + (1 + (1 + n)) :~: 3 + n) $
  tbuild1 5 (\i ->
    tbuild1 2 (\j -> tmap0N (* tfromIndex0 (maxF j (i `quot` (j + 1)))) r))

testConcatBuild22 :: Assertion
testConcatBuild22 =
  let !(!_, !_) = revShort @Double @9 concatBuild2 t48
  in return ()
