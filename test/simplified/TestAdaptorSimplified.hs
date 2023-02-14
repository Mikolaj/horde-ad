{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
module TestAdaptorSimplified (testTrees, rev', assertEqualUpToEpsilon') where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.MonoTraversable (Element)
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (inputConstant)

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2foo" testFoo
  , testCase "2bar" testBar
  , testCase "2barADVal" testBarADVal
  , testCase "2baz old to force fooConstant" testBaz
  , testCase "2baz new to check if mere repetition breaks things" testBaz
  , testCase "2baz again with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuild" testFooBuild
  , testCase "2fooMap" testFooMap
  , testCase "2fooMap1" testFooMap1
  , testCase "2fooNoGoAst" testFooNoGoAst
  , testCase "2fooNoGo" testFooNoGo
  , testCase "2nestedBuildMap" testNestedBuildMap
  , testCase "2nestedBuildMap1" testNestedBuildMap1
  , testCase "2nestedSumBuild" testNestedSumBuild
  , testCase "2nestedBuildIndex" testNestedBuildIndex
  , testCase "2barReluADValDt" testBarReluADValDt
  , testCase "2barReluADVal" testBarReluADVal
  , testCase "2barReluADVal3" testBarReluADVal3
  , testCase "2barReluAst0" testBarReluAst0
  , testCase "2barReluAst1" testBarReluAst1
  , testCase "2konstReluAst" testKonstReluAst
  , -- Tests by TomS:
    testCase "2F1" testF1
  , testCase "2F11" testF11
  , testCase "2F2" testF2
  , testCase "2F21" testF21
--  , testCase "2F3" testF3
  , -- Hairy tests
    testCase "2braidedBuilds" testBraidedBuilds
  , testCase "2braidedBuilds1" testBraidedBuilds1
  , testCase "2recycled" testRecycled
  , testCase "2recycled1" testRecycled1
  , testCase "2concatBuild" testConcatBuild
  , testCase "2concatBuild1" testConcatBuild1
  ]

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m
        , ADModeAndNumTensor 'ADModeGradient r, HasDelta r, ADReady r
        , a ~ OR.Array m r, TensorOf n r ~ OR.Array n r )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x) -> OR.Array n r
     -> (a, TensorOf m r, a, OR.Array n r, OR.Array n r)
rev' f vals =
  let dt = inputConstant @a 1
      g inputs = f $ parseADInputs vals inputs
      (advalGrad, value1) = revOnDomainsFun dt g (toDomains vals)
      gradient1 = parseDomains vals advalGrad
      value2 = f vals
      env inputs = IM.singleton 0 (AstVarR $ from1X $ parseADInputs vals inputs)
      h inputs =
        interpretAst (env inputs) (f (AstVar (tshape vals) (AstVarName 0)))
      (astGrad, value3) = revOnDomainsFun dt h (toDomains vals)
      gradient2 = parseDomains vals astGrad
  in (value1, value2, value3, gradient1, gradient2)

assertEqualUpToEpsilon'
    :: (AssertEqualUpToEpsilon z a, AssertEqualUpToEpsilon z b)
    => z  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> (b, b, b, a, a)   -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon' error_margin expected
                        (value1, value2, value3, gradient1, gradient2) = do
  value1 @?~ value2
  value3 @?~ value2
  assertEqualUpToEpsilon error_margin expected gradient1
  assertEqualUpToEpsilon error_margin expected gradient2


-- * Tensor tests

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo =
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double foo (1.1, 2.2, 3.3))

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (3.1435239435581166,-1.1053869545195814)
    (rev (bar @(ADVal 'ADModeGradient Double)) (1.1, 2.2))

barADVal :: forall r d. ADModeAndNum d r => (ADVal d r, ADVal d r) -> ADVal d r
barADVal = bar @(ADVal d r)

testBarADVal :: Assertion
testBarADVal =
  assertEqualUpToEpsilon 1e-9
    (11.49618087412679,-135.68959896367525)
    (revDt (barADVal @Double @'ADModeGradient) (1.1, 3) 42.2)

barADVal2 :: forall r a. (a ~ ADVal 'ADModeGradient r, r ~ Double)
          => (a, a, a) -> a
barADVal2 (x,y,z) =
  let w = foo (x,y,z) * sin y
  in atan2 z w + z * w

-- A check if gradient computation is re-entrant.
-- This test fails (not on first run, but on repetition) if old terms,
-- from before current iteration of gradient descent, are not soundly
-- handled in new computations (due to naive impurity, TH, plugins,
-- or just following the papers that assume a single isolated run).
-- This example requires monomorphic types and is contrived,
-- but GHC does optimize and factor out some accidentally constant
-- subterms in real examples (presumably after it monomorphizes them)
-- causing exactly the same danger.
-- This example also tests unused parameters (x), another common cause
-- of crashes in naive gradient computing code.
baz :: ( ADVal 'ADModeGradient Double
       , ADVal 'ADModeGradient Double
       , ADVal 'ADModeGradient Double )
    -> ADVal 'ADModeGradient Double
baz (_x,y,z) =
  let w = fooConstant * barADVal2 (y,y,z) * sin y
  in atan2 z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal 'ADModeGradient Double
fooConstant = foo (7, 8, 9)

testBaz :: Assertion
testBaz =
  assertEqualUpToEpsilon 1e-9
    (0, -5219.20995030263, 2782.276274462047)
    (rev baz (1.1, 2.2, 3.3))

-- If terms are numbered and @z@ is, wrongly, decorated with number 0,
-- here @fooConstant@ is likely to clash with @z@, since it was numbered
-- starting from 0, too.
-- The test fails if term numbering is reset to 0 between gradient computation
-- runs (verified) as well as when delta-expression evaluation assumes
-- it can only encounter terms numbered in the current run and,
-- e.g., allocates an array with only that much space (not verified).
-- Actually, with term counter zeroed just before @rev@ application,
-- even a single @testBaz@ execution produces wrong results, but this test
-- is likely to fail in less naive implementations, as well.
testBazRenumbered :: Assertion
testBazRenumbered =
  assertEqualUpToEpsilon 1e-9
    (0, -5219.20995030263, 2783.276274462047)
    (rev (\(x,y,z) -> z + baz (x,y,z)) (1.1, 2.2, 3.3))

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r d. ADModeAndNum d r => [ADVal d r] -> ADVal d r
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [2.4396285219055063, -1.953374825727421, 0.9654825811012627]
    (rev fooD [1.1 :: Double, 2.2, 3.3])

fooBuild1 :: ADReady r => TensorOf 1 r -> TensorOf 1 r
fooBuild1 v =
  let r = tsum0 v
      v' = tminimum0 v
  in tbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * tminimum0 v * v')
       + bar (r, tindex v [ix + 1])

testFooBuildDt :: Assertion
testFooBuildDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [4] [-189890.46351219364,-233886.08744601303,-222532.22669716467,-206108.68889329425])
    (revDt @(OR.Array 1 Double) fooBuild1 (OR.fromList [4] [1.1, 2.2, 3.3, 4]) (OR.constant [3] 42))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @(OR.Array 1 Double) fooBuild1 (OR.fromList [4] [1.1, 2.2, 3.3, 4]))

fooMap1 :: ADReady r => r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] (tscalar r)
  in tmap0N (\x -> x * r + 5) v

testFooMap :: Assertion
testFooMap =
  assertEqualUpToEpsilon 1e-6
    4.438131773948916e7
    (rev @(OR.Array 1 Double) fooMap1 1.1)

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-6
    4.438131773948916e7
    (rev' @(OR.Array 1 Double) (fooMap1 . tunScalar) 1.1)

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r))
       => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. (Show r, Numeric r, RealFloat r, Floating (Vector r))
           => Ast 1 r -> Ast 1 r
fooNoGoAst v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       barAst (3.14, bar (3.14, tindex v [ix]))
       + astCond (AstBoolOp AndOp
                    [ tindex v (ix * 2 :. ZI) `tleq` 0
                        -- @1 not required thanks to :.; see below for @ and []
                    , gtInt @(Ast 0 r) 6 (abs ix) ])
                 r (5 * r))
     / tslice 1 3 (tmap0N (\x -> astCond (x `tgt` r) r x) v)
     * tbuild1 3 (const 1)

testFooNoGoAst :: Assertion
testFooNoGoAst =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 1 r) -> ADVal d (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (fooNoGoAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-6
       (OR.fromList [5] [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])
       (rev @(OR.Array 1 Double) f
             (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

fooNoGo :: forall r. ADReady r
        => TensorOf 1 r -> TensorOf 1 r
fooNoGo v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       bar (3.14, bar (3.14, tindex v [ix]))
       + tcond (andBool @r (tindex @r @1 v [ix * 2] `tleq` 0)
                           (gtInt @r 6 (abs ix)))
               r (5 * r))
     / tslice 1 3 (tmap0N (\x ->
         tunScalar $ tcond (tscalar x `tgt` r) r (tscalar x)) v)
     * tbuild1 3 (const 1)

testFooNoGo :: Assertion
testFooNoGo =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])
   (rev' @(OR.Array 1 Double) fooNoGo
         (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall r. ADReady r => r -> TensorOf 1 r
nestedBuildMap r =
  let w = tkonst0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = tkonst0N [177] (tscalar r) :: TensorOf 1 r
      nestedMap x = tmap0N (x /) (w (tscalar x))
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' [ix + iy])
      doublyBuild = tbuild1 5 (tminimum0 . variableLengthBuild)
  in tmap0N (\x -> x
                  * tunScalar (tsum0
                      (tbuild1 3 (\ix -> bar ( tscalar x
                                            , tindex v' [ix]) )
                       + fooBuild1 (nestedMap x)
                       / fooMap1 x))
           ) doublyBuild

testNestedBuildMap :: Assertion
testNestedBuildMap =
  assertEqualUpToEpsilon 1e-10
    107.25984443006627
    (rev @(OR.Array 1 Double) nestedBuildMap 1.1)

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @(OR.Array 1 Double) (nestedBuildMap . tunScalar) 1.1)

nestedSumBuild :: ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedSumBuild v =
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
-- dynamic shapes:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + 1] (tfromIntOf0 ix7))))
-- irregular array:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + ix7 + 1] 2.4)))
             ]))))
  + tbuild1 13 (\ix ->
      nestedBuildMap (tunScalar $ tsum0 v) `tindex` [min ix 4])

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @(OR.Array 1 Double) nestedSumBuild (OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall r. ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedBuildIndex v =
  tbuild1 2 $ \ix2 -> tindex (tbuild1 3 $ \ix3 -> tindex (tbuild1 4 $ \ix4 -> tindex v (ix4 :. ZI)) [ix3]) (ix2 :. ZI)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @(OR.Array 1 Double) nestedBuildIndex (OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( RealFloat (TensorOf n r), HasPrimal (TensorOf n r)
     , Ord (Element (PrimalOf (TensorOf n r)))
     , Fractional (Element (PrimalOf (TensorOf n r))) )
  => TensorOf n r -> TensorOf n r
barRelu x = relu1 $ bar (x, relu1 x)

testBarReluADValDt :: Assertion
testBarReluADValDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]) 42.2)

testBarReluADVal :: Assertion
testBarReluADVal =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]))

testBarReluADVal3 :: Assertion
testBarReluADVal3 =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev @(OR.Array 3 Double) barRelu (OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluAst
  :: (KnownNat n, Numeric r, RealFloat r, Floating (Vector r))
  => Ast n r -> Ast n r
barReluAst x = reluAst1 $ bar (x, reluAst1 x)
  -- TODO; barRelu @(Ast 0 r) fails
  -- due to relu using conditionals and @>@ instead of
  -- a generalization of those that have Ast instance:

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 0 r) -> ADVal d (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [191.20462646925841])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 1 r) -> ADVal d (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (rev @(OR.Array 1 Double) f (OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. (Show r, Numeric r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ reluAst1 $ tkonst0N (7 :$ ZS) x

testKonstReluAst :: Assertion
testKonstReluAst =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 0 r) -> ADVal d (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (konstReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [295.4])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> tunScalar $ tsum0 (tbuild1 10 (\i -> tscalar arg * tfromIntOf0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    45.0
    (rev @Double f1 1.1)

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    45.0
    (rev' @(OR.Array 0 Double) (tscalar . f1 . tunScalar) 1.1)

f2 :: ADReady a => a -> a
f2 = \arg ->
  let fun1 i = tscalar arg * tfromIntOf0 i
      v1a = tsum0 (tbuild1 10 fun1)
      v1b = tsum0 (tbuild1 20 fun1)
      fun2 y i = tscalar y * tfromIntOf0 i
      v2a = tsum0 (tbuild1 10 (fun2 arg))
      v2b = tsum0 (tbuild1 20 (fun2 (arg + 1)))
  in tunScalar $ v1a + v1b + v2a + v2b

testF2 :: Assertion
testF2 =
  assertEqualUpToEpsilon 1e-10
    470
    (rev @Double f2 1.1)

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    470
    (rev' @(OR.Array 0 Double) (tscalar . f2 . tunScalar) 1.1)

{- TODO: disabled, because the a -> r instances are disabled
f3 :: (ADReady r, Tensor (r -> r), Tensor ((r -> r) -> (r -> r)))
   => TensorOf 0 r -> TensorOf 0 r
f3 arg =
  let arr1 = tbuild [10] (\i -> tscalar $ \x ->
                            x + tunScalar (tfromIntOf0 (headIndex i)))
      arr2 = tbuild [10] (\i -> tscalar $ \f -> (tunScalar $ arr1 ! i) . f)
      arr3 = tbuild [10] (\i -> tscalar $ (tunScalar $ arr2 ! i)
                                            (tunScalar $ arr1 ! i)
                                              (tunScalar arg))
  in tsum arr3

testF3 :: Assertion
testF3 =
  let _ = assertEqualUpToEpsilon' 1e-10
            470
            (rev' @(OR.Array 0 Double) f3 1.1)
  in return ()  -- dummy instance for -> and Ast rewrites don't remove -> yet
-}

-- * Hairy tests (many by TomS as well)

braidedBuilds :: forall r. ADReady r => r -> TensorOf 2 r
braidedBuilds r =
  tbuild1 3 (\ix1 ->
    tbuild1 4 (\ix2 -> tindex (tfromList0N [4]
                                      [tunScalar $ tfromIntOf0 ix2, 7, r, -0.2]) (ix1 :. ZI)))

testBraidedBuilds :: Assertion
testBraidedBuilds =
  assertEqualUpToEpsilon 1e-10
    4.0
    (rev @(OR.Array 2 Double) braidedBuilds 3.4)

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @(OR.Array 2 Double) (braidedBuilds . tunScalar) 3.4)

recycled :: ADReady r
         => r -> TensorOf 5 r
recycled r =
  tbuild1 2 $ \_ -> tbuild1 4 $ \_ -> tbuild1 2 $ \_ -> tbuild1 3 $ \_ ->
    nestedSumBuild (tkonst0N [7] (tscalar r))

testRecycled :: Assertion
testRecycled =
  assertEqualUpToEpsilon 1e-6
    3.983629038066359e7
    (rev @(OR.Array 5 Double) recycled 1.0001)

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilon' 1e-6
    3.983629038066359e7
    (rev' @(OR.Array 5 Double) (recycled . tunScalar)  1.0001)

concatBuild :: ADReady r => r -> TensorOf 2 r
concatBuild r =
  tbuild1 7 (\i ->
    tappend (tappend (tbuild1 5 (\_j -> tscalar r))  -- TODO: i should work
                     (tkonst 1 (tfromIntOf0 i)))
            (tbuild1 13 (\_k -> tscalar r)))
-- TODO: reject via types or accept with type obligations:
--    tappend (tappend (tbuild1 (1 + i) (\_j -> tscalar r))  -- TODO: i should work
--                     (tkonst0N [1] (tfromIntOf0 i)))
--            (tbuild1 (13 - i) (\_k -> tscalar r)))

testConcatBuild :: Assertion
testConcatBuild =
  assertEqualUpToEpsilon 1e-10
    126.0
    (rev @(OR.Array 2 Double) concatBuild 3.4)

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    126.0
    (rev' @(OR.Array 2 Double) (concatBuild . tunScalar) 3.4)

-- TODO:
_concatBuild2 :: ADReady r => r -> TensorOf 2 r
_concatBuild2 _r =
-- TODO: tbuild0N (7, 14) (\ (i,j)
  tbuild1 7 $ \i -> tbuild1 14 $ \_j ->
    -- TODO: use classes Cond and Bool: if i == j then tfromIntOf0 i else r
   tfromIntOf0 i
      -- need to prove that i + 1 + (13 - i) = 14
