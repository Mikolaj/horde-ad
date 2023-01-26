{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, RankNTypes,
             TypeFamilies, TypeOperators #-}
module TestSimplified (testTrees) where

import Prelude

import           Data.MonoTraversable (MonoFunctor)
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd

import Tool.EqEpsilon

import Prelude ()

testTrees :: [TestTree]
testTrees = [ testCase "barADVal" testBarADVal
            , testCase "fooBuild1" testFooBuild
            , testCase "fooMap1" testFooMap
            , testCase "fooNoGoAst" testFooNoGoAst
            , testCase "nestedBuildMap" testNestedBuildMap
            , testCase "nestedSumBuild" testNestedSumBuild
            , testCase "nestedBuildIndex" testNestedBuildIndex
            , testCase "barReluADVal" testBarReluADVal
            , testCase "barReluAst0" testBarReluAst0
            , testCase "barReluAst1" testBarReluAst1
            , testCase "konstReluAst" testKonstReluAst
            , -- tests by TomS:
              testCase "F1" testF1
            , testCase "F2" testF2
            ]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r)) => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

barADVal :: forall r d. ADModeAndNum d r => (ADVal d r, ADVal d r) -> ADVal d r
barADVal = bar @(ADVal d r)

fooBuild1 :: ADReady r => VectorOf r -> VectorOf r
fooBuild1 v =
  let r = lsum0 v
      v' = lminimum0 v
  in lbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * lminimum0 v * v')
       + bar (r, lindex0 v (ix + 1))

fooMap1 :: ADReady r => r -> VectorOf r
fooMap1 r =
  let v = fooBuild1 $ lkonst1 130 r
  in lmap1 (\x -> x * r + 5) v

-- A test with conditionals. We haven't defined a class for conditionals so far,
-- so this uses raw AST instead of sufficiently polymorphic code.
fooNoGoAst :: (Numeric r, RealFloat r, Floating (Vector r))
           => Ast 1 r -> Ast 1 r
fooNoGoAst v =
  let r = lsum0 v
  in lbuild1 3 (\ix ->
       (barAst (3.14, bar (3.14, lindex0 v ix)))
       + AstCond (AstBoolOp AndOp  -- TODO: overload &&, <=, >, etc.
                             [ lindex0 v (ix * 2) `leqAst` 0
                             , 6 `gtIntAst` abs ix ])
                 r (5 * r))
     / lslice1 1 3 (lmap1 (\x -> AstCond (x `gtAst` r) r x) v)
     * lbuild1 3 (\ _ix -> 1)

-- TODO: remove the need for the 2 type hints; using VectorOf in the definition
-- of VectorLike class may be enough
nestedBuildMap :: forall r. ADReady r => r -> VectorOf r
nestedBuildMap r =
  let w x = lkonst1 4 x  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = lkonst1 7 r :: VectorOf r
      nestedMap x = lmap1 (\y -> x / y) (w x)
      variableLengthBuild iy = lbuild1 (iy + 1) (\ix -> lindex0 v' (ix + 1)) :: VectorOf r
      doublyBuild = lbuild1 5 (\iy -> lminimum0 (variableLengthBuild iy))
  in lmap1 (\x -> x
                  * lsum0
                      (lbuild1 3 (\ix -> bar ( x
                                             , lindex0 v' ix) )
                       + fooBuild1 (nestedMap x)
                       / fooMap1 x)
           ) doublyBuild

nestedSumBuild :: ADReady r => VectorOf r -> VectorOf r
nestedSumBuild v =
  lbuild1 13 (\ix ->
    lsum0 (lbuild1 4 (\ix2 ->
      flip lindex0 ix2
        (lbuild1 5 (\ _ -> lsum0 v)
         * lfromList1
             [ fromIntOf0 ix
             , lsum0 (lbuild1 9 (\ix5 -> fromIntOf0 ix5))
             , lsum0 (lbuild1 6 (\_ -> lsum0 v))
             , lindex0 v ix2
             , lsum0 (lbuild1 3 (\ix7 ->
                 lsum0 (lkonst1 (ix2 + 1) (fromIntOf0 ix7))))
-- irregular array:
--             , lsum0 (lbuild1 3 (\ix7 ->
--                 lsum0 (lkonst1 (ix2 + ix7 + 1) 2.4)))
             ]))))
  + lbuild1 13 (\ix ->
      nestedBuildMap (lsum0 v) `lindex0` min ix 4)

nestedBuildIndex :: ADReady r => VectorOf r -> VectorOf r
nestedBuildIndex v =
  lbuild1 2 $ \ix2 -> lindex0 (lbuild1 3 $ \ix3 -> lindex0 (lbuild1 4 $ \ix4 -> lindex0 v ix4) ix3) ix2

barRelu
  :: ( RealFloat a
     , HasPrimal a, MonoFunctor (PrimalOf a), Num (PrimalOf a)
     , Ord (Element (PrimalOf a)), Fractional (Element (PrimalOf a)) )
  => a -> a
barRelu x = relu $ bar (x, relu x)

barReluAst0
  :: ( Numeric r, RealFloat r, MonoFunctor (AstPrimalPart1 0 r)
     , Floating (Vector r) )
  => Ast 0 r -> Ast 0 r
barReluAst0 x = reluAst $ bar (x, reluAst x)
  -- TODO; fails due to relu using conditionals and @>@ instead of
  -- a generalization of those that have Ast instance: barRelu @(Ast 0 r)

-- TODO: merge with the above once rank-polymorphic relu is recovered
barReluAst1
  :: ( KnownNat n, Numeric r, RealFloat r
     , MonoFunctor (AstPrimalPart1 n r), Floating (Vector r) )
  => Ast n r -> Ast n r
barReluAst1 x = reluAst $ bar (x, reluAst x)
                  -- TODO; fails: barRelu @(Ast n r)

konstReluAst
  :: forall r.
     (Numeric r, Num (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = lsum0 $ reluAst $ lkonst1 7 x


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> lsum0 (lbuild1 10 (\i -> arg * fromIntOf0 i))

f2 :: ADReady a => a -> a
f2 = \arg ->
  let fun1 i = arg * fromIntOf0 i
      v1a = lsum0 (lbuild1 10 fun1)
      v1b = lsum0 (lbuild1 20 fun1)
      fun2 y i = y * fromIntOf0 i
      v2a = lsum0 (lbuild1 10 (fun2 arg))
      v2b = lsum0 (lbuild1 20 (fun2 (arg + 1)))
  in v1a + v1b + v2a + v2b


-- * Test harness glue code

-- The glue for sufficiently polymorphic code;
testPoly00
  :: (HasDelta r, r ~ Double)
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
             interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                           (f (AstVar0 (AstVarName (-1)))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains 1
          (\adinputs -> f $ adinputs `at0` 0)
          domainsInput
      value = f input
  astValue @?~ value
  advalValue @?~ value
  domains0 astGrad @?~ domains0 domainsExpected
  domains0 advalGrad @?~ domains0 domainsExpected

testPoly01
  :: (HasDelta r, r ~ Double)
  => (forall x. ADReady x => x -> VectorOf x) -> Int -> r -> r
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
             interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                           (f (AstVar0 (AstVarName (-1)))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains dt
          (\adinputs -> f $ adinputs `at0` 0)
          domainsInput
      value = f input
  astValue @?~ value
  advalValue @?~ value
  domains0 astGrad @?~ domains0 domainsExpected
  domains0 advalGrad @?~ domains0 domainsExpected

testPoly11
  :: (HasDelta r, r ~ Double)
  => (forall x. ADReady x => VectorOf x -> VectorOf x) -> Int -> [r] -> [r]
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
             interpretAst (IM.singleton (-1) (AstVarR1 $ adinputs `at1` 0))
                           (f (AstVar1 (AstVarName (-1)))))
          domainsInput
      (advalGrad, advalValue) =
        revOnDomains dt
          (\adinputs -> f $ adinputs `at1` 0)
          domainsInput
      value = f (vToVec $ V.fromList input)
  astValue @?~ value
  advalValue @?~ value
  domains1 astGrad @?~ domains1 domainsExpected
  domains1 advalGrad @?~ domains1 domainsExpected

-- In simplified horde-ad we don't have access to the highest level API
-- (adaptors), so the testing glue is tedious:
testBarADVal :: Assertion
testBarADVal =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> barADVal (adinputs `at0` 0, adinputs `at0` 1))
       (domainsFrom01 (V.fromList [1.1 :: Double, 3]) V.empty))
  @?~ V.fromList [11.49618087412679,-135.68959896367525]

-- For sufficiently polymorphic code, we test vectorization with a fallback
-- to other methods, so the test harness is even more complex.
testFooBuild :: Assertion
testFooBuild =
  testPoly11 fooBuild1 3
    [1.1, 2.2, 3.3, 4]
    [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627]

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
          interpretAst (IM.singleton (-1) (AstVarR1 $ adinputs `at1` 0))
                        (fooNoGoAst (AstVar1 (AstVarName (-1)))))
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
       (\adinputs -> barRelu (adinputs `at0` 0))
       (domainsFrom01 (V.fromList [1.1 :: Double]) V.empty))
  @?~ V.fromList [191.20462646925841]

testBarReluAst0 :: Assertion
testBarReluAst0 =
  (domains0 $ fst
   $ revOnDomains
       42.2
       (\adinputs -> unScalar $
          interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                        (barReluAst0 (AstVar0 (AstVarName (-1)))))
       (domainsFrom01 (V.fromList [1.1 :: Double]) V.empty))
  @?~ V.fromList [191.20462646925841]

testBarReluAst1 :: Assertion
testBarReluAst1 =
  (domains1 $ fst
   $ revOnDomains
       (vToVec $ LA.konst 1 5)
         -- "1" wrong due to fragility of hmatrix and tensor numeric instances
       (\adinputs ->
          interpretAst (IM.singleton (-1) (AstVarR1 $ adinputs `at1` 0))
                       (barReluAst1 (AstVar1 (AstVarName (-1)))))
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
          interpretAst (IM.singleton (-1) (AstVarR0 $ adinputs `at0` 0))
                        (konstReluAst (AstVar0 (AstVarName (-1)))))
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
