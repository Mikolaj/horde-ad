{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees, rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShorter
  , t16, t16b, t48, t128, t128b, t128c
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.ADValTensor
import HordeAd.Core.Ast
import HordeAd.Core.DualClass (inputConstant)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2foo" testFoo
  , testCase "2bar" testBar
  , testCase "2barADVal" testBarADVal
  , testCase "2baz old to force fooConstant" testBaz
  , testCase "2baz if repetition breaks things" testBaz
  , testCase "2baz again with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuild" testFooBuild
  , testCase "2fooMap1" testFooMap1
  , testCase "2fooNoGoAst" testFooNoGoAst
  , testCase "2fooNoGo" testFooNoGo
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
        ( KnownNat n, KnownNat m, ADNum r, ADReady r, InterpretAst r
        , a ~ OR.Array m r, ScalarOf r ~ r
        , TensorOf n r ~ OR.Array n r
        , TensorOf n (ADVal r)
          ~ ADVal (OR.Array n r)
        , TensorOf m (ADVal r)
          ~ ADVal (OR.Array m r)
        , ADReady (ADVal r) )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> OR.Array n r
     -> ( TensorOf m r, a, a, a, a, a
        , OR.Array n r, OR.Array n r, OR.Array n r, OR.Array n r, OR.Array n r
        , Ast m r, Ast m r )
rev' f vals =
  let value0 = f vals
      dt = inputConstant @a 1
      g inputs = f $ parseADInputs vals inputs
      (advalGrad, value1) = revOnDomainsFun dt g (toDomains vals)
      gradient1 = parseDomains vals advalGrad
      h :: ADReady x
        => (TensorOf m x -> Ast m r) -> (Ast n r -> TensorOf n x)
        -> (Ast m r -> Ast m r) -> ADInputs r
        -> ADVal (OR.Array m r)
      h fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseADInputs vals inputs) IM.empty
        in interpretAst env (gx ast)
      (astGrad, value2) = revOnDomainsFun dt (h id id id) (toDomains vals)
      gradient2 = parseDomains vals astGrad
      (astSimple, value3) =
        revOnDomainsFun dt (h id id simplifyAst) (toDomains vals)
      gradient3 = parseDomains vals astSimple
      (astPrimal, value4) =
        revOnDomainsFun dt (h unAstPrimalPart AstPrimalPart id)
                           (toDomains vals)
          -- use the AstPrimalPart instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradient4 = parseDomains vals astPrimal
      (astPSimple, value5) =
        revOnDomainsFun dt (h unAstPrimalPart AstPrimalPart simplifyAst)
                           (toDomains vals)
      gradient5 = parseDomains vals astPSimple
      astVectSimp = simplifyAst $ snd $ funToAstR (tshape vals) f
      astSimp =
        simplifyAst $ snd
        $ funToAstR (tshape vals) (unAstPrimalPart . f . AstPrimalPart)
  in ( value0, value1, value2, value3, value4, value5
     , gradient1, gradient2, gradient3, gradient4, gradient5
     , astVectSimp, astSimp )

assertEqualUpToEpsilon'
    :: ( AssertEqualUpToEpsilon z a, AssertEqualUpToEpsilon z b
       , KnownNat m, Show r, Numeric r, Num (Vector r), HasCallStack )
    => z  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> (b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r)
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin expected
    ( value0, value1, value2, value3, value4, value5
    , gradient1, gradient2, gradient3, gradient4, gradient5
    , astVectSimp, astSimp ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val NotVect" errMargin value0 value4
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad NotVect" errMargin expected gradient4
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  -- No Eq instance, so let's compare the text.
  show (simplifyAst astVectSimp) @?= show astVectSimp
  show (simplifyAst astSimp) @?= show astSimp

assertEqualUpToEpsilonShorter
    :: ( AssertEqualUpToEpsilon z a, AssertEqualUpToEpsilon z b
       , KnownNat m, Show r, Numeric r, Num (Vector r), HasCallStack )
    => z  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> (b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r)   -- ^ actual values
    -> Assertion
assertEqualUpToEpsilonShorter
    errMargin expected
    ( value0, value1, value2, value3, _value4, value5
    , gradient1, gradient2, gradient3, _gradient4, gradient5
    , astVectSimp, astSimp ) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  show (simplifyAst astVectSimp) @?= show astVectSimp
  show (simplifyAst astSimp) @?= show astSimp

t16 :: (Numeric r, Fractional r) => OR.Array 5 r
t16 = OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t16b :: (Numeric r, Fractional r) => OR.Array 4 r
t16b = OR.fromList [2, 2, 2, 2] [5, 2, 6, 1, -2, 0, 0.1, -0.2, 13.1, 9, 8, -4, 582934, 2.99432, -335, 26]

t48 :: (Numeric r, Fractional r) => OR.Array 7 r
t48 = OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (Numeric r, Fractional r) => OR.Array 10 r
t128 = OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

t128b :: (Numeric r, Fractional r) => OR.Array 4 r
t128b = OR.reshape [4, 2, 4, 4] t128

t128c :: (Numeric r, Fractional r) => OR.Array 4 r
t128c = OR.reshape [2, 2, 8, 4] t128


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
    (rev (bar @(ADVal Double)) (1.1, 2.2))

barADVal :: forall r. ADNum r => (ADVal r, ADVal r) -> ADVal r
barADVal = bar @(ADVal r)

testBarADVal :: Assertion
testBarADVal =
  assertEqualUpToEpsilon 1e-9
    (11.49618087412679,-135.68959896367525)
    (revDt (barADVal @Double) (1.1, 3) 42.2)

barADVal2 :: forall r a. (a ~ ADVal r, r ~ Double)
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
baz :: ( ADVal Double
       , ADVal Double
       , ADVal Double )
    -> ADVal Double
baz (_x,y,z) =
  let w = fooConstant * barADVal2 (y,y,z) * sin y
  in atan2 z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal Double
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
fooD :: forall r. ADNum r => [ADVal r] -> ADVal r
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
      v' = tminimum v
  in tbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * tminimum v * v')
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

fooMap1 :: ADReady r => TensorOf 0 r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] r
  in tmap0N (\x -> x * r + 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-6
    4.438131773948916e7
    (rev' @(OR.Array 1 Double) fooMap1 1.1)

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
       barAst (3.14, bar (3.14, tindex v [(ix + tfloor r) `min` 2 `max` 0]))
       + astCond (AstBoolOp AndOp
                    [ tindex v (ix * 2 :. ZI) <=* 0
                        -- @1 not required thanks to :.; see below for @ and []
                    , 6 >* abs ix ])
                 r (5 * r))
     / tslice 1 3 (tmap0N (\x -> astCond (x >* r) r x) v)
     * tbuild1 3 (const 1)

testFooNoGoAst :: Assertion
testFooNoGoAst =
  let f :: (ADNum r, InterpretAst r)
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (fooNoGoAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (rev @(OR.Array 1 Double) f
             (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

fooNoGo :: forall r. ADReady r
        => TensorOf 1 r -> TensorOf 1 r
fooNoGo v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       bar (3.14, bar (3.14, tindex v [(ix + tfloor r) `min` 2 `max` 0]))
       + ifB ((&&*) (tindex @r @1 v [ix * 2] <=* 0)
                    (6 >* abs ix))
               r (5 * r))
     / tslice 1 3 (tmap0N (\x -> ifB (x >* r) r x) v)
     * tbuild1 3 (const 1)

testFooNoGo :: Assertion
testFooNoGo =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
   (rev' @(OR.Array 1 Double) fooNoGo
         (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall r. ADReady r => TensorOf 0 r -> TensorOf 1 r
nestedBuildMap r =
  let w = tkonst0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = tkonst0N [177] r :: TensorOf 1 r
      nestedMap x = tmap0N (x /) (w x)
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' (ix + iy :. ZI))
      doublyBuild = tbuild1 5 (tminimum . variableLengthBuild)
  in tmap0N (\x -> x * tsum0
                         (tbuild1 3 (\ix -> bar (x, tindex v' [ix]))
                          + fooBuild1 (nestedMap x)
                          / fooMap1 x)
            ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilonShorter 1e-10
    107.25984443006627
    (rev' @(OR.Array 1 Double) nestedBuildMap 1.1)

nestedSumBuild :: ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedSumBuild v =
  tbuild1 13 (\ix ->
    tsum (tbuild1 4 (\ix2 ->
      flip tindex [ix2]
        (tbuild1 5 (\ _ -> tsum v)
         * tfromList
             [ tfromIndex0 ix
             , tsum (tbuild1 9 tfromIndex0)
             , tsum (tbuild1 6 (\_ -> tsum v))
             , tindex v [ix2]
             , tsum (tbuild1 3 (\ix7 ->
                 tsum (tkonst 5 (tfromIndex0 ix7))))
-- dynamic shapes:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + 1] (tfromIndex0 ix7))))
-- irregular array:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + ix7 + 1] 2.4)))
             ]))))
  + tbuild1 13 (\ix ->
      nestedBuildMap (tsum0 v) `tindex` [min ix 4])

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilonShorter 1e-8
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
  :: ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
  => TensorOf n r -> TensorOf n r
barRelu x = relu1 $ bar (x, relu1 x)

testBarReluADValDt :: Assertion
testBarReluADValDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]) 42.2)

testBarReluADVal :: Assertion
testBarReluADVal =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]))

testBarReluADVal3 :: Assertion
testBarReluADVal3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @(OR.Array 3 Double) barRelu (OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluAst
  :: forall n r.
     (KnownNat n, Numeric r, RealFloat r, Floating (Vector r), Show r)
  => Ast n r -> Ast n r
barReluAst x = relu1 @n @(Ast 0 r) $ bar (x, relu1 x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: (ADNum r, InterpretAst r)
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [191.20462646925841])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: (ADNum r, InterpretAst r)
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (rev @(OR.Array 1 Double) f (OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. (Show r, Numeric r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ relu1 $ tkonst0N (7 :$ ZS) x

testKonstReluAst :: Assertion
testKonstReluAst =
  let f :: (ADNum r, InterpretAst r)
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (konstReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [295.4])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> tunScalar $ tsum0 (tbuild1 10 (\i -> tscalar arg * tfromIndex0 i))

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
  let fun1 i = tscalar arg * tfromIndex0 i
      v1a = tsum0 (tbuild1 10 fun1)
      v1b = tsum0 (tbuild1 20 fun1)
      fun2 y i = tscalar y * tfromIndex0 i
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
                            x + tunScalar (tfromIndex0 (headIndex i)))
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
      [tunScalar $ tfromIndex0 ix2, 7, r, -0.2]) (ix1 :. ZI)))

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
    348356.9278600814
    (rev @(OR.Array 5 Double) recycled 0.0000001)

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilonShorter 1e-6
    348356.9278600814
    (rev' @(OR.Array 5 Double) (recycled . tunScalar) 0.0000001)

concatBuild :: ADReady r => r -> TensorOf 2 r
concatBuild r =
  tbuild1 7 (\i ->
    tappend (tappend (tbuild1 5 (\_j -> tscalar r))  -- TODO: i should work
                     (tkonst 1 (tfromIndex0 i)))
            (tbuild1 13 (\_k -> tscalar r)))
-- TODO: reject via types or accept with type obligations:
--    tappend (tappend (tbuild1 (1 + i) (\_j -> tscalar r))  -- TODO: i should work
--                     (tkonst0N [1] (tfromIndex0 i)))
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
    -- TODO: use classes Cond and Bool: if i == j then tfromIndex0 i else r
   tfromIndex0 i
      -- need to prove that i + 1 + (13 - i) = 14
