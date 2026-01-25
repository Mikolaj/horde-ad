{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tests of the gather and scatter operations and of operations that expand
-- to gather and of fusion of all of them.
module TestGatherSimplified (testTrees) where

import Prelude

import Control.Monad.ST.Strict (ST, runST)
import Data.Int (Int8)
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested qualified as Nested

import HordeAd

import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "detSquare9" testDetSquare9
  ]

type IntOr8 = Int8
type Int8OrDouble = Int8

detSquare :: forall target. ADReady target
          => target (TKR 2 Double) -> target (TKScalar Double)
detSquare =
  let fact :: Int -> Int
      fact n = factAcc 1 n
        where factAcc acc i | i <= 1 = acc
              factAcc acc i = factAcc (i * acc) (i - 1)

      fused :: forall s.
               Int -> Int -> VSM.MVector s IntOr8 -> VSM.MVector s Bool
            -> ST s ()
      fused !len !idx0 !perm !freeSpots = do
        let nthFreeSpot :: Int -> Int -> ST s Int
            nthFreeSpot !pos !el = do
              free <- VSM.read freeSpots el
              if pos <= 0 && free
              then return el
              else nthFreeSpot (pos - fromEnum free) (el + 1)
            loop :: Int -> Int -> Int -> ST s ()
            loop _ _ 0 = return ()
            loop !idx !fi i2 = do
              let fi2 = fi `quot` i2
                  (idxDigit, idxRest) = idx `quotRem` fi2
              el <- nthFreeSpot idxDigit 0
              VSM.write perm (len - i2) (fromIntegral el)
              VSM.write freeSpots el False
              loop idxRest fi2 (i2 - 1)
        loop idx0 (fact len) len

      mutated :: forall s. Int -> ST s (VS.Vector IntOr8)
      mutated !len = do
        perms <- VSM.unsafeNew (len * fact len)
        freeSpots <- VSM.unsafeNew len
        let loop :: Int -> ST s ()
            loop (-1) = return ()
            loop i = do
              VSM.set freeSpots True
              fused len i (VSM.slice (i * len) len perms) freeSpots
              loop (i - 1)
        loop (fact len - 1)
        VS.unsafeFreeze perms

      idx_to_perm :: Int -> Nested.Ranked 2 IntOr8
      idx_to_perm n = Nested.rfromVector [fact n, n] $ runST $ mutated n

      inversion_number_from_idx :: Int -> Nested.Ranked 1 Int8OrDouble
      inversion_number_from_idx n =
        let loop :: Int -> Int -> Int -> Int -> Int8OrDouble
            loop s _ _ i | i == 1 = fromIntegral s
            loop s idx fi i =
              let fi2 = fi `quot` i
                  (s1, idx2) = idx `quotRem` fi2
                  s2 = s + s1
              in loop s2 idx2 fi2 (i - 1)
            f idx0 = loop 0 idx0 (fact n) n
        in Nested.rfromVector [fact n] $ VS.generate (fact n) f

      productR :: target (TKR 1 Double) -> target (TKScalar Double)
      productR = kfromR . rfold (*) (rscalar 1)

      det :: target (TKR 2 Double) -> target (TKScalar Double)
      det a =
        let ell = rwidth a
            p :: PlainOf target (TKR 2 IntOr8)
            p = rconcrete $ idx_to_perm ell
            q :: PlainOf target (TKR 1 Int8OrDouble)
            q = rconcrete $ inversion_number_from_idx ell
            f :: IntOf target -> target (TKScalar Double)
            f i = (-1) ** kfromIntegral (kfromPlain (q `rindex0` [i]))
                  * productR (rgather1 ell a $ \i2 ->
                                [i2, kfromIntegral $ p `rindex0` [i, i2]])
        in withSNat (fact ell) $ \ (SNat @k) ->
             ssum0 $ kbuild1 @k f
      {-
      gradient :: Input -> GradientOutput
      gradient a =
        let ell = rwidth a
        in if ell /= 5
             let art = gradArtifact det a
                 artSimp = simplifyArtifactRev art
             in traceShow ("gradient", printArtifactSimple art) $
                traceShow ("gradSimp", printArtifactSimple artSimp) $
                 gradInterpretArtifact artSimp (chunk ell a)
      -}
  in det

testDetSquare9 :: Assertion
testDetSquare9 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [10,10] [198.10693359375,-208.391845703125,-74.715576171875,-235.9921875,-56.984375,31.765625,20.578125,-214.5625,-41.9375,-181.75,-158.23355102539063,15.689483642578125,-6.07183837890625,-32.855712890625,-18.2464599609375,-13.33154296875,8.1669921875,9.7578125,36.15625,49.59375,4.102272751895559e15,-7.306139851602269e13,1.6344669707400714e16,-2.0387070048459585e15,1.1609737081775948e14,-5.972802872324755e15,-8.292337523172424e14,6.612381495486813e14,1.3074134839774018e15,-4.551880458211714e15,14.17529296875,-9.8779296875,28.02752685546875,-12.56640625,40.626953125,-29.2734375,4.2890625,41.9375,-2.474609375,-6.21875,-54.611328125,-16.91455078125,-39.5654296875,8.5,-6.6484375,35.75,-9.375e-2,-57.0625,19.8515625,-28.75,32.62109375,16.92626953125,94.29736328125,10.3125,-22.953125,-14.3125,-8.9375,9.625,0.259765625,-17.0,-4.10227275189546e15,7.306139851613288e13,-1.6344669707400854e16,2.0387070048459333e15,-1.1609737081777206e14,5.972802872324765e15,8.292337523172635e14,-6.612381495487908e14,-1.3074134839774085e15,4.551880458211696e15,-44.125,63.90625,24.578125,-34.1015625,-16.609375,-12.015625,0.109375,-7.28125,10.8671875,10.1875,-70.75,-21.0,-31.0625,31.78125,-19.25,77.75,-19.125,43.625,5.875,-32.375,51.25,-17.875,26.5,-10.34375,36.1875,23.4375,1.625,-45.625,-20.59375,-68.25])
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
