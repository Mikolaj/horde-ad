{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -dno-typeable-binds -dsuppress-all -dsuppress-uniques -ddump-simpl #-}
-- | Tests of the gather and scatter operations and of operations that expand
-- to gather and of fusion of all of them.
module TestGatherSimplified (testTrees) where

import Prelude

import Data.Int (Int8)
import Data.Vector.Storable qualified as VS
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Ranked.Shape

import HordeAd

import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "detSquare9" testDetSquare9
  ]

detSquare :: forall target. ADReady target
          => target (TKR 2 Double) -> target (TKScalar Double)
detSquare =
  let fact :: Int -> Int
      fact n = factAcc 1 n
        where factAcc acc i | i <= 1 = acc
              factAcc acc i = factAcc (i * acc) (i - 1)

      idx_to_perm :: Int -> Nested.Ranked 2 Int8
      idx_to_perm n = Nested.rfromVector (fact n :$: n :$: ZSR)
                      $ VS.replicate (fact n * n) 0

      productR :: target (TKR 1 Double) -> target (TKScalar Double)
      productR = kfromR . rfold (*) (rscalar 1)

      det :: target (TKR 2 Double) -> target (TKScalar Double)
      det a =
        let ell = rwidth a
            p :: PlainOf target (TKR 2 Int8)
            p = rconcrete $ idx_to_perm ell
            f :: IntOf target -> target (TKScalar Double)
            f i = productR (rgather1 ell a $ \i2 ->
                              [i2, kfromIntegral $ p `rindex0` [i, i2]])
        in withSNat (fact ell) $ \ (SNat @k) ->
             ssum0 $ kbuild1 @k f
  in det

testDetSquare9 :: Assertion
testDetSquare9 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [10,10] [1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.464351690816e14,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])
    (grad detSquare
          (ringestData [10,10]
             [ 7, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432
             , 7, 25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432
             , 7, 40.1,32.1,40.1,89.0,53.99432,97.1,56.8200001,97.1,52.843201
             , 7, 97.1,55.8943200001,97.1,85.894001,97.1,85.801,18.1,29.1,32.1
             , 7, 40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001
             , 7, 97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1
             , 7, 40.1,32.1,40.1,89.0,53.99432,97.1,56.8200001,97.1,52.843201
             , 7, 97.1,55.8943200001, 1, -2, 97.1,58.200001,97.1,55.894320,97.1
             , 7, 29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1
             , 7, 32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6 ]))
