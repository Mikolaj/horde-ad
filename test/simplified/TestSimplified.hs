{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
module TestSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import HordeAd.Internal.SizedList

testTrees :: [TestTree]
testTrees = [ testCase "nestedSumBuild" testNestedSumBuild
            ]


-- * Tensor tests

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooBuild1 :: ADReady r => TensorOf 1 r -> TensorOf 1 r
fooBuild1 v =
  let r = tsum0 v
      v' = tminimum0 v
  in tbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * tminimum0 v * v')
       + bar (r, tindex v [ix + 1])

fooMap1 :: ADReady r => r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] (tscalar r)
  in tmap0N (\x -> x * tscalar r + 5) v

nestedBuildMap :: forall r. ADReady r => r -> TensorOf 1 r
nestedBuildMap r =
  let w = tkonst0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = tkonst0N [177] (tscalar r) :: TensorOf 1 r
      nestedMap x = tmap0N (tscalar x /) (w (tscalar x))
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' [ix + iy])
      doublyBuild = tbuild1 5 (tminimum0 . variableLengthBuild)
  in tmap0N (\x -> x
                  * (tsum0
                      (tbuild1 3 (\ix -> bar (x
                                            , tindex v' [ix]) )
                       + fooBuild1 (nestedMap (tunScalar x))
                       / fooMap1 (tunScalar x)))
           ) doublyBuild

nestedSumBuild :: forall r. ADReady r
               => AstIndex 2 Double -> TensorOf 1 r -> TensorOf 1 r
nestedSumBuild sl v =
 let  !_A1 = takeIndex @2 (1 :. (2 :: AstInt r) :. ZI)
      !_A2 = takeIndex @0 (1 :. (2 :: AstInt r) :. ZI)
      !_A3 = dropIndex @2 (1 :. (2 :: AstInt r) :. ZI)
      !_A4 = dropIndex @0 (1 :. (2 :: AstInt r) :. ZI)
      !_A1v = takeSized @2 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A2v = takeSized @0 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A3v = dropSized @2 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_A4v = dropSized @0 (AstVarName 1 ::: AstVarName 2 ::: Z)
      !_B1 = takeIndex @2 sl
      !_B2 = takeIndex @0 sl
      !_B3 = dropIndex @2 sl
      !_B4 = dropIndex @0 sl
 in -- tfromList0N [13] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
-- {-
  tbuild1 13 (\ix ->
    tsum (tbuild1 4 (\ix2 ->
      flip tindex [ix2]
        (tbuild1 5 (\ _ -> tsum v)
         * tfromList
             [ tfromIntOf0 ix
             , tsum (tbuild1 9 tfromIntOf0)
             , tsum (tbuild1 6 (\_ -> tsum v))
             , tindex v [ix2]
             , tsum (tbuild1 3 (\ix7 ->
                 tsum (tkonst 5 (tfromIntOf0 ix7))))
             ]))))
  + tbuild1 13 (\ix ->
      nestedBuildMap (tunScalar $ tsum0 v) `tindex` [min ix 4])
-- -}

testPoly11
  :: r ~ Double
  => (forall x. ADReady x => TensorOf 1 x -> TensorOf 1 x) -> Int -> [r] -> [r]
  -> Assertion
testPoly11 f outSize input expected = do
  let domainsInput =
        domainsFrom0V V.empty (V.singleton (V.fromList input))
      domainsExpected =
        domainsFrom0V V.empty (V.singleton (V.fromList expected))
      dt = vToVec $ LA.konst 1 outSize
        -- "1" wrong due to fragility of hmatrix and tensor numeric instances
      (astGrad, astValue) =
        revOnDomains dt
          (\adinputs ->
             interpretAst (IM.singleton 0
                             (AstVarR $ from1X $ at1 @1 adinputs 0))
                          (f (AstVar [length input] (AstVarName 0))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains dt
          (\adinputs -> f $ adinputs `at1` 0)
          domainsInput
      val = f (vToVec $ V.fromList input)
  astValue @?~ val
  advalValue @?~ val
  domains1 astGrad @?~ domains1 domainsExpected
  domains1 advalGrad @?~ domains1 domainsExpected

testNestedSumBuild :: Assertion
testNestedSumBuild = do
  let sl = 1 :. (2 :: AstInt Double) :. ZI
  testPoly11 (nestedSumBuild sl) 13
    [1.1, 2.2, 3.3, 4, -5.22]
    [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612]
