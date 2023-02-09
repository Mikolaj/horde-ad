{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
module TestAdaptorSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.MonoTraversable (Element)
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2foo" testFoo
  , testCase "2bar" testBar
  , testCase "2barADVal" testBarADVal
  , testCase "2baz old to force fooConstant" testBaz
  , testCase "2baz new to check if mere repetition breaks things" testBaz
  , testCase "2baz again to use fooConstant with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuild" testFooBuild





  , testCase "2fooMap" testFooMap
  , testCase "2fooNoGoAst" testFooNoGoAst
  , testCase "2nestedBuildMap" testNestedBuildMap
  , testCase "2nestedSumBuild" testNestedSumBuild
  , testCase "2nestedBuildIndex" testNestedBuildIndex
  , testCase "2barReluADVal" testBarReluADVal
  , testCase "2barReluAst0" testBarReluAst0
  , testCase "2barReluAst1" testBarReluAst1
  , testCase "2konstReluAst" testKonstReluAst
  , -- Tests by TomS:
    testCase "2F1" testF1
  , testCase "2F2" testF2
  , testCase "2F3" testF3
  , -- Hairy tests
    testCase "2braidedBuilds" testBraidedBuilds
  , testCase "2recycled" testRecycled
  , testCase "2concatBuild" testConcatBuild
  ]


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
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (revDt @(OR.Array 1 Double) fooBuild1 (OR.fromList [4] [1.1, 2.2, 3.3, 4]) (OR.constant [3] 1))





















fooMap1 :: ADReady r => r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] (tscalar r)
  in tmap0N (\x -> x * r + 5) v

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r))
       => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

-- A test with conditionals. We haven't defined a class for conditionals so far,
-- so this uses raw AST instead of sufficiently polymorphic code.
fooNoGoAst :: (Show r, Numeric r, RealFloat r, Floating (Vector r))
           => Ast 1 r -> Ast 1 r
fooNoGoAst v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       barAst (3.14, bar (3.14, tindex v [ix]))
       + AstCond (AstBoolOp AndOp  -- TODO: overload &&, <=, >, etc.
                             [ tindex v [ix * 2] `leqAst` 0
                             , 6 `gtIntAst` abs ix ])
                 r (5 * r))
     / tslice 1 3 (tmap0N (\x -> AstCond (x `gtAst` r) r x) v)
     * tbuild1 3 (const 1)

-- TODO: remove the need for the 2 type hints; using TensorOf 1 in the definition
-- of VectorLike class may be enough
nestedBuildMap :: forall r. ADReady r => r -> TensorOf 1 r
nestedBuildMap r =
  let w = tkonst0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = tkonst0N [177] (tscalar r) :: TensorOf 1 r
      nestedMap x = tmap0N (x /) (w (tscalar x))
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' [ix + iy]) :: TensorOf 1 r
      doublyBuild = tbuild1 5 (tminimum0 . variableLengthBuild)
  in tmap0N (\x -> x
                  * tunScalar (tsum0
                      (tbuild1 3 (\ix -> bar ( tscalar x
                                            , tindex v' [ix]) )
                       + fooBuild1 (nestedMap x)
                       / fooMap1 x))
           ) doublyBuild

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

nestedBuildIndex :: forall r. ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedBuildIndex v =
  tbuild1 2 $ \ix2 -> tindex @r @1 (tbuild1 3 $ \ix3 -> tindex (tbuild1 4 $ \ix4 -> tindex @r @1 v [ix4]) [ix3]) [ix2]

barRelu
  :: ( RealFloat (TensorOf n r), HasPrimal (TensorOf n r)
     , Ord (Element (PrimalOf (TensorOf n r)))
     , Fractional (Element (PrimalOf (TensorOf n r))) )
  => TensorOf n r -> TensorOf n r
barRelu x = relu1 $ bar (x, relu1 x)

-- TODO: merge with the above once rank-polymorphic relu is recovered
barReluAst
  :: (KnownNat n, Numeric r, RealFloat r, Floating (Vector r))
  => Ast n r -> Ast n r
barReluAst x = reluAst1 $ bar (x, reluAst1 x)
  -- TODO; barRelu @(Ast 0 r) fails
  -- due to relu using conditionals and @>@ instead of
  -- a generalization of those that have Ast instance:

konstReluAst
  :: forall r. (Show r, Numeric r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ reluAst1 @1 $ tkonst0N [7] x


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> tunScalar $ tsum0 (tbuild1 10 (\i -> tscalar arg * tfromIntOf0 i))

f2 :: ADReady a => a -> a
f2 = \arg ->
  let fun1 i = tscalar arg * tfromIntOf0 i
      v1a = tsum0 (tbuild1 10 fun1)
      v1b = tsum0 (tbuild1 20 fun1)
      fun2 y i = tscalar y * tfromIntOf0 i
      v2a = tsum0 (tbuild1 10 (fun2 arg))
      v2b = tsum0 (tbuild1 20 (fun2 (arg + 1)))
  in tunScalar $ v1a + v1b + v2a + v2b

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

-- * Hairy tests (many by TomS as well)

braidedBuilds :: forall r. ADReady r => r -> TensorOf 2 r
braidedBuilds r =
  tbuild1 3 (\ix1 ->
    tbuild1 4 (\ix2 -> tindex @r @1 (tfromList0N [4]
                                      [tunScalar $ tfromIntOf0 ix2, 7, r, -0.2]) [ix1]))

recycled :: ADReady r
         => r -> TensorOf 5 r
recycled r = tbuild1 2 $ \_ -> tbuild1 4 $ \_ -> tbuild1 2 $ \_ -> tbuild1 3 $ \_ ->
               nestedSumBuild (tkonst0N [7] (tscalar r))

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

-- TODOL
_concatBuild2 :: ADReady r => r -> TensorOf 2 r
_concatBuild2 _r =
-- TODO: tbuild0N (7, 14) (\ (i,j)
  tbuild1 7 $ \i -> tbuild1 14 $ \_j ->
    -- TODO: use classes Cond and Bool: if i == j then tfromIntOf0 i else r
   tfromIntOf0 i
      -- need to prove that i + 1 + (13 - i) = 14

-- * Test harness glue code

-- The glue for sufficiently polymorphic code;
testPoly00
  :: r ~ Double
  => (forall x. ADReady x => x -> x) -> r -> r
  -> Assertion
testPoly00 f input expected = do
  let domainsInput =
        domainsFrom01 (V.singleton input) V.empty
      domainsExpected =
        domainsFrom01 (V.singleton expected) V.empty
      (astGrad, astValue) =
        revOnDomains 1
          (\adinputs -> unScalar $
             interpretAst (IM.singleton 0
                             (AstVarR $ from1X $ scalar $ adinputs `at0` 0))
                          (f (AstVar [] (AstVarName 0))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains 1
          (\adinputs -> f $ adinputs `at0` 0)
          domainsInput
      val = f input
  astValue @?~ val
  advalValue @?~ val
  domains0 astGrad @?~ domains0 domainsExpected
  domains0 advalGrad @?~ domains0 domainsExpected

testPoly01
  :: r ~ Double
  => (forall x. ADReady x => x -> TensorOf 1 x) -> Int -> r -> r
  -> Assertion
testPoly01 f outSize input expected = do
  let domainsInput =
        domainsFrom01 (V.singleton input) V.empty
      domainsExpected =
        domainsFrom01 (V.singleton expected) V.empty
      dt = vToVec $ LA.konst 1 outSize
        -- "1" wrong due to fragility of hmatrix and tensor numeric instances
      (astGrad, astValue) =
        revOnDomains dt
          (\adinputs ->
             interpretAst (IM.singleton 0
                             (AstVarR $ from1X $ scalar $ adinputs `at0` 0))
                          (f (AstVar [] (AstVarName 0))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains dt
          (\adinputs -> f $ adinputs `at0` 0)
          domainsInput
      val = f input
  astValue @?~ val
  advalValue @?~ val
  domains0 astGrad @?~ domains0 domainsExpected
  domains0 advalGrad @?~ domains0 domainsExpected

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

testPolyn
  :: (KnownNat n, r ~ Double)
  => (forall x. ADReady x => x -> TensorOf n x)
  -> OR.ShapeL -> r -> r
  -> Assertion
testPolyn f sh input expected = do
  let domainsInput =
        domainsFrom01 (V.singleton input) V.empty
      domainsExpected =
        domainsFrom01 (V.singleton expected) V.empty
      dt = OR.fromVector sh $ LA.konst 1 $ product sh
        -- "1" wrong due to fragility of hmatrix and tensor numeric instances
      (astGrad, astValue) =
        revOnDomains dt
          (\adinputs ->
             interpretAst (IM.singleton 0
                             (AstVarR $ from1X $ scalar $ adinputs `at0` 0))
                          (f (AstVar [] (AstVarName 0))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains dt
          (\adinputs -> f $ adinputs `at0` 0)
          domainsInput
      val = f input
  astValue @?~ val
  advalValue @?~ val
  domains0 astGrad @?~ domains0 domainsExpected
  domains0 advalGrad @?~ domains0 domainsExpected








testFooMap :: Assertion
testFooMap =
  testPoly01 fooMap1 3
    1.1
    4.438131773948916e7

testFooNoGoAst :: Assertion
testFooNoGoAst =
  (domains1 $ fst
   $ revOnDomains
       (vToVec $ LA.konst 1 3)
        -- "1" wrong due to fragility of hmatrix and tensor numeric instances
       (\adinputs ->
          interpretAst (IM.singleton 0
                          (AstVarR $ from1X $ at1 @1 adinputs 0))
                        (fooNoGoAst (AstVar [5] (AstVarName 0))))
       (domainsFrom0V V.empty
                      (V.singleton (V.fromList
                                      [1.1 :: Double, 2.2, 3.3, 4, 5]))))
  @?~ domains1 (domainsFrom0V V.empty (V.singleton (V.fromList [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])))

testNestedBuildMap :: Assertion
testNestedBuildMap =
  testPoly01 nestedBuildMap 5
    1.1
    107.25984443006627

testNestedSumBuild :: Assertion
testNestedSumBuild =
  testPoly11 nestedSumBuild 13
    [1.1, 2.2, 3.3, 4, -5.22]
    [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612]

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  testPoly11 nestedBuildIndex 2
    [1.1, 2.2, 3.3, 4, -5.22]
    [1,1,0,0,0]

testBarReluADVal :: Assertion
testBarReluADVal =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> unScalar $ barRelu (scalar $ adinputs `at0` 0))
       (domainsFrom01 (V.fromList [1.1 :: Double]) V.empty))
  @?~ V.fromList [191.20462646925841]

testBarReluAst0 :: Assertion
testBarReluAst0 =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> unScalar $
          interpretAst (IM.singleton 0
                          (AstVarR $ from1X $ scalar $ adinputs `at0` 0))
                        (barReluAst (AstVar [] (AstVarName 0))))
       (domainsFrom01 (V.fromList [1.1 :: Double]) V.empty))
  @?~ V.fromList [191.20462646925841]

testBarReluAst1 :: Assertion
testBarReluAst1 =
  (domains1 $ fst
   $ revOnDomains
       (vToVec $ LA.konst 1 5)
         -- "1" wrong due to fragility of hmatrix and tensor numeric instances
       (\adinputs ->
          interpretAst (IM.singleton 0
                          (AstVarR $ from1X $ at1 @1 adinputs 0))
                       (barReluAst (AstVar [5] (AstVarName 0))))
       (domainsFrom0V V.empty
                      (V.singleton (V.fromList
                                      [1.1 :: Double, 2.2, 3.3, 4, 5]))))
  @?~ domains1 (domainsFrom0V V.empty (V.singleton (V.fromList [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])))

testKonstReluAst :: Assertion
testKonstReluAst =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> unScalar $
          interpretAst (IM.singleton 0
                          (AstVarR $ from1X $ scalar $ adinputs `at0` 0))
                        (konstReluAst (AstVar [] (AstVarName 0))))
       (domainsFrom01 (V.fromList [1.1 :: Double]) V.empty))
  @?~ V.fromList [295.4]

testF1 :: Assertion
testF1 =
  testPoly00 f1
    1.1
    45.0

testF2 :: Assertion
testF2 =
  testPoly00 f2
    1.1
    470.0

testF3 :: Assertion
testF3 = do
  let input = 1.1
      expected = 470.0
      fAst = -- unScalar $
-- TODO:        interpretAst (IM.singleton 0 (AstVarR input))
                     (f3 @(Ast 0 Double) (AstVar [] (AstVarName 0)))
      valViaAst = fAst  -- TODO: input
      val = f3 @Double input
  let _res = val @?~ expected in return ()  -- stubs would fail
  let _res2 = valViaAst {-TODO: @?~ expected-} in return ()  -- stubs would fail

testBraidedBuilds :: Assertion
testBraidedBuilds =
  testPolyn braidedBuilds [3, 4]
  3.4
  4.0

testRecycled :: Assertion
testRecycled =
  testPolyn recycled [2, 4, 2, 3, 13]
  1.0001
  3.983629038066359e7

testConcatBuild :: Assertion
testConcatBuild =
  testPolyn concatBuild [7, 14]
  3.4
  91
