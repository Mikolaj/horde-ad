{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestHighRankSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           GHC.TypeLits (KnownNat, type (+), type (-), type (<=))
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import TestAdaptorSimplified (assertEqualUpToEpsilon', rev')
import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "3nestedBuildMap7" testNestedBuildMap7
  , testCase "3concatBuild" testConcatBuild
  ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

fooBuild1 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild1 v =
  let r = tsum v
      tk = tkonst0N (tailShape $ tshape v)
      v' = tk $ tminimum $ tflatten v
  in tbuild1 3 $ \ix ->
       r * foo ( tk 3
               , tk 5 * r
               , r * v')

fooMap1 :: (ADReady r, KnownNat n, RealFloat (TensorOf n r))
        => ShapeInt (1 + n) -> TensorOf 0 r -> TensorOf (1 + n) r
fooMap1 sh r =
  let v = fooBuild1 $ tkonst0N sh (r * r)
  in tmap0N (\x -> x * r + 5) v

nestedBuildMap :: forall n r.
                  (ADReady r, n <= 6, KnownNat n)
               => TensorOf 0 r -> TensorOf (1 + n) r
nestedBuildMap r =
  let v' = tkonst0N (177 :$ ZS) r
      variableLengthBuild iy = tbuild1 7 (\ix ->
        tindex v' (ix + iy :. ZI))
      doublyBuild =
        tbuild1 3 (tkonst0N (takeShape @n @(6 - n)
                             $ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ ZS)
                   . tminimum . variableLengthBuild)
  in tmap0N (\x -> x * tsum0 (fooMap1 (3 :$ ZS) x)
            ) doublyBuild

testNestedBuildMap7 :: Assertion
testNestedBuildMap7 =
  assertEqualUpToEpsilon 1e-8
    2176.628439128524
    (rev @(OR.Array 7 Double) nestedBuildMap 0.6)






concatBuild :: (ADReady r, KnownNat n)
            => TensorOf (1 + n) r -> TensorOf (3 + n) r
concatBuild r =
  tbuild1 1 (\i -> tbuild1 1 (\j -> tmap0N (* tfromIndex0 (j - i)) r))

testConcatBuild :: Assertion
testConcatBuild =
  assertEqualUpToEpsilon' 1e-10
    (rev' @(OR.Array 3 Double) concatBuild (tkonst 7 3.4))
