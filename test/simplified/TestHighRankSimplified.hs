{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestHighRankSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           GHC.TypeLits (KnownNat, type (+), type (-), type (<=))
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (inputConstant)

import Tool.EqEpsilon

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m, HasDelta r, ADReady r
        , a ~ OR.Array m r, ScalarOf r ~ r
        , TensorOf n r ~ OR.Array n r
        , TensorOf n (ADVal 'ADModeGradient r)
          ~ ADVal 'ADModeGradient (OR.Array n r)
        , TensorOf m (ADVal 'ADModeGradient r)
          ~ ADVal 'ADModeGradient (OR.Array m r)
        , ADReady (ADVal 'ADModeGradient r) )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> OR.Array n r
     -> ( TensorOf m r, a )
rev' f vals =
  let value0 = f vals
      dt = inputConstant @a 1
      g inputs = f $ parseADInputs vals inputs
      (_, value1) = revOnDomainsFun dt g (toDomains vals)
  in ( value0, value1 )

assertEqualUpToEpsilon'
    :: ( AssertEqualUpToEpsilon z b
       , HasCallStack )
    => z  -- ^ error margin (i.e., the epsilon)
    -> (b, b)
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin
    ( value0, value1 ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1

testTrees :: [TestTree]
testTrees =
  [ testCase "3nestedBuildMap7" testNestedBuildMap7
  , testCase "3concatBuild" testConcatBuild
  ]

nestedBuildMap :: forall n r.
                  (ADReady r, n <= 77, KnownNat n, KnownNat (1 + n))
               => TensorOf 0 r -> TensorOf (1 + n) r
nestedBuildMap r =
  let v' = tkonst0N (288 :$ ZS) r
      variableLengthBuild iy = tbuild1 7 (\ix ->
        tindex v' (ix + iy :. ZI))
      doublyBuild =
        tbuild1 3 (tkonst0N (takeShape @n @(114 - n)
                             $ 2 :$ 4 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ 2 :$ 4 :$ 2 :$ 1 :$ 3 :$ 2 :$ ZS)
                   . tminimum . variableLengthBuild)
  in tmap0N (\x -> x
            ) doublyBuild

testNestedBuildMap7 :: Assertion
testNestedBuildMap7 =
  assertEqualUpToEpsilon 1e-8
    2176.628439128524
    (rev @(OR.Array 33 Double) nestedBuildMap 0.6)






concatBuild :: (ADReady r, KnownNat (1 + n), KnownNat (2 + n))
            => TensorOf (1 + n) r -> TensorOf (3 + n) r
concatBuild r =
  tbuild1 1 (\i -> tbuild1 1 (\j -> tmap0N (* tfromIndex0 (j - i)) r))

testConcatBuild :: Assertion
testConcatBuild =
  assertEqualUpToEpsilon' 1e-10
    (rev' @(OR.Array 3 Double) concatBuild (tkonst 7 3.4))
