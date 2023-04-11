{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees, rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16b, t48, t128, t128b, t128c
  , scale1, relu1, reluLeaky1
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.EnumMap.Strict as EM
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd.Core.Ast
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal (ADTensor)
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2zero" testZero
  , testCase "2foo" testFoo
  , testCase "2fooPP" testFooPP
  , testCase "2fooLet" testFooLet
  , testCase "2fooLetPP" testFooLetPP
  , testCase "2bar" testBar
  , testCase "2barADVal" testBarADVal
  , testCase "2baz old to force fooConstant" testBaz
  , testCase "2baz if repetition breaks things" testBaz
  , testCase "2baz again with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuild" testFooBuild
  , testCase "2fooBuildPP" testFooBuildPP
  , testCase "2fooMap1" testFooMap1
  , testCase "2fooMap1PP" testFooMap1PP
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
  , testCase "2emptyArgs0" testEmptyArgs0
  , testCase "2emptyArgs1" testEmptyArgs1
  , testCase "2emptyArgs4" testEmptyArgs4
  , testCase "2blowupPP" fblowupPP
  , testCase "2blowupLetPP" fblowupLetPP
  , blowupTests
  ]

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m, Floating (Vector r), ADTensor r, ADReady r
        , InterpretAst (ADVal r), InterpretAst r, DomainsTensor r
        , a ~ TensorOf m r, ScalarOf r ~ r, ScalarOf (ADVal r) ~ r
        , IsPrimalWithScalar (TensorOf m r) r, DomainsOf r ~ Domains r
        , Adaptable (ADVal (TensorOf n r))
        , TensorOf n (ADVal r) ~ ADVal (TensorOf n r)
        , TensorOf m (ADVal r) ~ ADVal (TensorOf m r)
        , ADReady (ADVal r), TensorOf n r ~ OR.Array n r )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> TensorOf n r
     -> ( TensorOf m r, a, a, a, a, a
        , TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r
        , Ast m r, Ast m r
        , a, a, a, a, a
        , TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r, TensorOf n r )
rev' f vals =
  let value0 = f vals
      dt = Nothing
      g inputs = f $ parseADInputs vals inputs
      (advalGrad, value1) = revOnDomains dt g (toDomains vals)
      gradient1 = parseDomains vals advalGrad
      g9 inputs = f $ parseADInputs vals inputs
      (advalGrad9, value9) = revAstOnDomains g9 (toDomains vals) dt
      gradient9 = parseDomains vals advalGrad9
      h :: ADReady x
        => (TensorOf m x -> Ast m r) -> (Ast n r -> TensorOf n x)
        -> (Ast m r -> Ast m r) -> ADInputs r
        -> ADVal (TensorOf m r)
      h fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseADInputs vals inputs) EM.empty
        in snd $ interpretAst env EM.empty (gx ast)
      (astGrad, value2) = revOnDomains dt (h id id id) (toDomains vals)
      gradient2 = parseDomains vals astGrad
      (astSimple, value3) =
        revOnDomains dt (h id id simplifyAst) (toDomains vals)
      gradient3 = parseDomains vals astSimple
      (astPrimal, value4) =
        revOnDomains dt (h unAstNoVectorize AstNoVectorize id)
                        (toDomains vals)
          -- use the AstNoVectorize instance that does no vectorization
          -- and then interpret the results as the Ast instance
      gradient4 = parseDomains vals astPrimal
      (astPSimple, value5) =
        revOnDomains dt (h unAstNoVectorize AstNoVectorize simplifyAst)
                        (toDomains vals)
      gradient5 = parseDomains vals astPSimple
      astVectSimp = simplifyAst $ snd $ funToAstR (tshape vals) f
      astSimp =
        simplifyAst $ snd
        $ funToAstR (tshape vals) (unAstNoVectorize . f . AstNoVectorize)
      -- Here comes the part with Ast gradients.
      hAst :: ADReady x
           => (TensorOf m x -> Ast m r) -> (Ast n r -> TensorOf n x)
           -> (Ast m r -> Ast m r) -> ADInputs (Ast0 r)
           -> ADVal (Ast m r)
      hAst fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseADInputs vals inputs) EM.empty
        in snd $ interpretAst env EM.empty (gx ast)
      (astGradAst, value2Ast) =
        revAstOnDomains (hAst id id id) (toDomains vals) dt
      gradient2Ast = parseDomains vals astGradAst
      (astSimpleAst, value3Ast) =
        revAstOnDomains (hAst id id simplifyAst) (toDomains vals) dt
      gradient3Ast = parseDomains vals astSimpleAst
      (astPrimalAst, value4Ast) =
        revAstOnDomains (hAst unAstNoVectorize AstNoVectorize id)
                        (toDomains vals) dt
      gradient4Ast = parseDomains vals astPrimalAst
      (astPSimpleAst, value5Ast) =
        revAstOnDomains (hAst unAstNoVectorize AstNoVectorize simplifyAst)
                        (toDomains vals) dt
      gradient5Ast = parseDomains vals astPSimpleAst
  in ( value0, value1, value2, value3, value4, value5
     , gradient1, gradient2, gradient3, gradient4, gradient5
     , astVectSimp, astSimp
     , value9, value2Ast, value3Ast, value4Ast, value5Ast
     , gradient9, gradient2Ast, gradient3Ast, gradient4Ast, gradient5Ast )

assertEqualUpToEpsilon'
    :: ( AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon b
       , KnownNat m, ShowAstSimplify r, HasCallStack )
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> ( b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r
       , b, b, b, b, b, a, a, a, a, a )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon'
    errMargin expected
    ( value0, value1, value2, value3, value4, value5
    , gradient1, gradient2, gradient3, gradient4, gradient5
    , astVectSimp, astSimp
    , value9, value2Ast, value3Ast, value4Ast, value5Ast
    , gradient9, gradient2Ast, gradient3Ast, gradient4Ast, gradient5Ast) = do
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
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp" errMargin value0 value3Ast
  assertEqualUpToEpsilonWithMark "Val Ast NotVect" errMargin value0 value4Ast
  assertEqualUpToEpsilonWithMark "Val Ast Simplified" errMargin value0 value5Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized"
                                 errMargin expected gradient2Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp"
                                 errMargin expected gradient3Ast
  assertEqualUpToEpsilonWithMark "Grad Ast NotVect"
                                 errMargin expected gradient4Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Simplified"
                                 errMargin expected gradient5Ast
  assertEqualUpToEpsilonWithMark "Val ADVal Ast" errMargin value0 value9
  assertEqualUpToEpsilonWithMark "Grad ADVal Ast" errMargin expected gradient9
  -- No Eq instance, so let's compare the text.
  show (simplifyAst astVectSimp) @?= show astVectSimp
  show (simplifyAst astSimp) @?= show astSimp

assertEqualUpToEpsilonShort
    :: ( AssertEqualUpToEpsilon a, AssertEqualUpToEpsilon b
       , KnownNat m, ShowAstSimplify r, HasCallStack )
    => Rational  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> ( b, b, b, b, b, b, a, a, a, a, a, Ast m r, Ast m r
       , b, b, b, b, b, a, a, a, a, a )
         -- ^ actual values
    -> Assertion
assertEqualUpToEpsilonShort
    errMargin expected
    ( value0, value1, value2, value3, _value4, value5
    , gradient1, gradient2, gradient3, _gradient4, gradient5
    , astVectSimp, astSimp
    , _value9, value2Ast, value3Ast, _value4Ast, _value5Ast
    , _gradient9, gradient2Ast, gradient3Ast, _gradient4Ast, _gradient5Ast) = do
  assertEqualUpToEpsilonWithMark "Val ADVal" errMargin value0 value1
  assertEqualUpToEpsilonWithMark "Val Vectorized" errMargin value0 value2
  assertEqualUpToEpsilonWithMark "Val Vect+Simp" errMargin value0 value3
  assertEqualUpToEpsilonWithMark "Val Simplified" errMargin value0 value5
  assertEqualUpToEpsilonWithMark "Grad ADVal" errMargin expected gradient1
  assertEqualUpToEpsilonWithMark "Grad Vectorized" errMargin expected gradient2
  assertEqualUpToEpsilonWithMark "Grad Vect+Simp" errMargin expected gradient3
  assertEqualUpToEpsilonWithMark "Grad Simplified" errMargin expected gradient5
  assertEqualUpToEpsilonWithMark "Val Ast Vectorized" errMargin value0 value2Ast
  assertEqualUpToEpsilonWithMark "Val Ast Vect+Simp" errMargin value0 value3Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vectorized"
                                 errMargin expected gradient2Ast
  assertEqualUpToEpsilonWithMark "Grad Ast Vect+Simp"
                                 errMargin expected gradient3Ast
  -- No Eq instance, so let's compare the text.
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

scale1 :: (ADReady r, KnownNat n, Num (TensorOf n r))
       => TensorOf n (Primal r) -> TensorOf n r -> TensorOf n r
scale1 a d = tconstant a * d

relu1, reluLeaky1
  :: forall n r. (ADReady r, KnownNat n, Num (TensorOf n r))
  => TensorOf n r -> TensorOf n r
relu1 v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0)
                           (tprimalPart v)
  in scale1 oneIfGtZero v

reluLeaky1 v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0.01)
                           (tprimalPart v)
  in scale1 oneIfGtZero v


-- * Tensor tests

testZero :: Assertion
testZero =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @0 [] [0])
    (rev' @(OR.Array 0 Double) (const 3) 42)

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (srev @Double foo (1.1, 2.2, 3.3))

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (5, "dt")]
      fooT = foo @(Ast 0 Double)
      foo3 x = fooT (x, x, x)
      (AstVarName var3, ast3) = funToAstR ZS foo3
  "\\" ++ printAstVar IM.empty var3 "" ++ " -> " ++ printAstSimple IM.empty ast3
    @?= "\\x1 -> atan2 x1 (x1 * sin x1) + x1 * (x1 * sin x1)"
  resetVarCounter
  let (vars, AstVarName varDt, letGradientAst, vAst) = revDtFun fooT (4, 5, 6)
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 x3 x4 dt -> dlet (sin x3) (\\x6 -> dlet (x2 * x6) (\\x7 -> dlet (sin x3) (\\x8 -> dlet (x2 * x8) (\\x9 -> dlet (x4 * dt) (\\x10 -> dlet (negate (x4 * (tconst 1.0 / (x4 * x4 + x7 * x7))) * dt) (\\x11 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (x6 * x11 + x8 * x10), dfromR (cos x3 * (x2 * x11) + cos x3 * (x2 * x10)), dfromR ((x7 * (tconst 1.0 / (x4 * x4 + x7 * x7))) * dt + x9 * dt)])))))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 x3 x4 -> tlet (sin x3) (\\x6 -> tlet (x2 * x6) (\\x7 -> tlet (sin x3) (\\x8 -> tlet (x2 * x8) (\\x9 -> atan2 x4 x7 + x4 * x9))))"

fooLet :: forall r n. (RealFloat (TensorOf n r), Tensor r, KnownNat n)
       => (TensorOf n r, TensorOf n r, TensorOf n r) -> TensorOf n r
fooLet (x, y, z) = tlet @r @n (x * sin y) $ \w -> atan2 z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 fooLet (1.1, 2.2, 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (5, "dt")]
      fooLetT = fooLet @(Ast0 Double)
      fooLet3 x = fooLetT (x, x, x)
      (AstVarName var3, ast3) = funToAstR ZS fooLet3
  "\\" ++ printAstVar IM.empty var3 "" ++ " -> " ++ printAstSimple IM.empty ast3
    @?= "\\x1 -> tlet (x1 * sin x1) (\\x2 -> atan2 x1 x2 + x1 * x2)"
  resetVarCounter
  let (vars, AstVarName varDt, letGradientAst, vAst) =
        revDtFun fooLetT (4, 5, 6)
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 x3 x4 dt -> dlet (sin x3) (\\x7 -> dlet (x2 * x7) (\\x8 -> dlet (negate (x4 * (tconst 1.0 / (x4 * x4 + x8 * x8))) * dt + x4 * dt) (\\x9 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (x7 * x9), dfromR (cos x3 * (x2 * x9)), dfromR ((x8 * (tconst 1.0 / (x4 * x4 + x8 * x8))) * dt + x8 * dt)]))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 x3 x4 -> tlet (sin x3) (\\x7 -> tlet (x2 * x7) (\\x8 -> atan2 x4 x8 + x4 * x8))"

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (3.1435239435581166,-1.1053869545195814)
    (crev (bar @(ADVal Double)) (1.1, 2.2))

barADVal :: forall r. (IsPrimal r, RealFloat r)
         => (ADVal r, ADVal r) -> ADVal r
barADVal = bar @(ADVal r)

testBarADVal :: Assertion
testBarADVal =
  assertEqualUpToEpsilon 1e-9
    (11.49618087412679,-135.68959896367525)
    (crevDt (barADVal @Double) (1.1, 3) 42.2)

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
    (crev baz (1.1, 2.2, 3.3))

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
    (crev (\(x,y,z) -> z + baz (x,y,z)) (1.1, 2.2, 3.3))

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r. (IsPrimalWithScalar r r, RealFloat r)
     => [ADVal r] -> ADVal r
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [2.4396285219055063, -1.953374825727421, 0.9654825811012627]
    (crev fooD [1.1 :: Double, 2.2, 3.3])

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
    (revDt @Double @1 fooBuild1 (OR.fromList [4] [1.1, 2.2, 3.3, 4]) (OR.constant [3] 42))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @(OR.Array 1 Double) fooBuild1 (OR.fromList [4] [1.1, 2.2, 3.3, 4]))

testFooBuildPP :: Assertion
testFooBuildPP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (3, "dt")]
      fooBuild1T = fooBuild1 @(Ast0 Double)
  let (vars, AstVarName varDt, letGradientAst, vAst) =
        revDtFun fooBuild1T (OR.constant [4] 4)
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 dt -> dlet (tsum x2) (\\x5 -> dlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x6 -> dlet (x5 * x6) (\\x7 -> dlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x8 -> dlet (tconst 5.0) (\\x9 -> dlet (tsum x2) (\\x10 -> dlet (x9 * x10) (\\x11 -> dlet (tconst 3.0) (\\x12 -> dlet (sin x11) (\\x13 -> dlet (x7 * x8) (\\x14 -> dlet (x12 * x13) (\\x15 -> dlet (tsum x2) (\\x16 -> dlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x17 -> dlet (x16 * x17) (\\x18 -> dlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x19 -> dlet (tconst 5.0) (\\x20 -> dlet (tsum x2) (\\x21 -> dlet (x20 * x21) (\\x22 -> dlet (tconst 3.0) (\\x23 -> dlet (sin x22) (\\x24 -> dlet (x18 * x19) (\\x25 -> dlet (x23 * x24) (\\x26 -> dlet (tsum x2) (\\x27 -> dlet (atan2 x14 x15 + x25 * x26) (\\x28 -> dlet (tgather [3] x2 (\\[i29] -> [1 + i29])) (\\x30 -> dlet (tkonst 3 (tsum x2)) (\\x31 -> dlet (sin x30) (\\x32 -> dlet (tkonst 3 (tsum x2)) (\\x33 -> dlet (x31 * x32) (\\x34 -> dlet (tgather [3] x2 (\\[i35] -> [1 + i35])) (\\x36 -> dlet (tkonst 3 (tsum x2)) (\\x37 -> dlet (sin x36) (\\x38 -> dlet (tkonst 3 (tsum x2)) (\\x39 -> dlet (x37 * x38) (\\x40 -> dlet (tgather [3] x2 (\\[i41] -> [1 + i41])) (\\x42 -> dlet (atan2 x33 x34 + x39 * x40) (\\x43 -> dlet (sin x42) (\\x44 -> dlet (tkonst 3 (tsum x2)) (\\x45 -> dlet (x43 * x44) (\\x46 -> dlet (tgather [3] x2 (\\[i48] -> [1 + i48])) (\\x49 -> dlet (tkonst 3 (tsum x2)) (\\x50 -> dlet (sin x49) (\\x51 -> dlet (tkonst 3 (tsum x2)) (\\x52 -> dlet (x50 * x51) (\\x53 -> dlet (tgather [3] x2 (\\[i54] -> [1 + i54])) (\\x55 -> dlet (tkonst 3 (tsum x2)) (\\x56 -> dlet (sin x55) (\\x57 -> dlet (tkonst 3 (tsum x2)) (\\x58 -> dlet (x56 * x57) (\\x59 -> dlet (tgather [3] x2 (\\[i60] -> [1 + i60])) (\\x61 -> dlet (atan2 x52 x53 + x58 * x59) (\\x62 -> dlet (sin x61) (\\x63 -> dlet (tgather [3] x2 (\\[i47] -> [1 + i47])) (\\x64 -> dlet (x62 * x63) (\\x65 -> dlet (x64 * dt) (\\x66 -> dlet (x63 * x66) (\\x68 -> dlet (x58 * x68) (\\x69 -> dlet (negate (x52 * (tconst 1.0 / (x52 * x52 + x53 * x53))) * x68) (\\x71 -> dlet (negate (x45 * (tconst 1.0 / (x45 * x45 + x46 * x46))) * dt) (\\x74 -> dlet (x44 * x74) (\\x76 -> dlet (x39 * x76) (\\x77 -> dlet (negate (x33 * (tconst 1.0 / (x33 * x33 + x34 * x34))) * x76) (\\x79 -> dlet (tsum dt) (\\x81 -> dlet (x27 * x81) (\\x82 -> dlet (x25 * x82) (\\x83 -> dlet (cos x22 * (x23 * x83)) (\\x84 -> dlet (x26 * x82) (\\x85 -> dlet (x19 * x85) (\\x87 -> dlet (negate (x14 * (tconst 1.0 / (x14 * x14 + x15 * x15))) * x82) (\\x89 -> dlet (cos x11 * (x12 * x89)) (\\x90 -> dlet ((x15 * (tconst 1.0 / (x14 * x14 + x15 * x15))) * x82) (\\x91 -> dlet (x8 * x91) (\\x93 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tkonst 4 (x28 * x81) + tkonst 4 (x6 * x93) + tscatter [4] (tfromList [x5 * x93]) (\\[i94] -> [rem (tminIndex0 x2) 4]) + tscatter [4] (tfromList [x7 * x91]) (\\[i92] -> [rem (tminIndex0 x2) 4]) + tkonst 4 (x9 * x90) + tkonst 4 (x17 * x87) + tscatter [4] (tfromList [x16 * x87]) (\\[i88] -> [rem (tminIndex0 x2) 4]) + tscatter [4] (tfromList [x18 * x85]) (\\[i86] -> [rem (tminIndex0 x2) 4]) + tkonst 4 (x20 * x84) + tkonst 4 (tsum ((x46 * (tconst 1.0 / (x45 * x45 + x46 * x46))) * dt)) + tkonst 4 (tsum ((x34 * (tconst 1.0 / (x33 * x33 + x34 * x34))) * x76)) + tkonst 4 (tsum (x32 * x79)) + tscatter [4] (cos x30 * (x31 * x79)) (\\[i80] -> [1 + i80]) + tkonst 4 (tsum (x40 * x76)) + tkonst 4 (tsum (x38 * x77)) + tscatter [4] (cos x36 * (x37 * x77)) (\\[i78] -> [1 + i78]) + tscatter [4] (cos x42 * (x43 * x74)) (\\[i75] -> [1 + i75]) + tscatter [4] (x65 * dt) (\\[i73] -> [1 + i73]) + tkonst 4 (tsum ((x53 * (tconst 1.0 / (x52 * x52 + x53 * x53))) * x68)) + tkonst 4 (tsum (x51 * x71)) + tscatter [4] (cos x49 * (x50 * x71)) (\\[i72] -> [1 + i72]) + tkonst 4 (tsum (x59 * x68)) + tkonst 4 (tsum (x57 * x69)) + tscatter [4] (cos x55 * (x56 * x69)) (\\[i70] -> [1 + i70]) + tscatter [4] (cos x61 * (x62 * x66)) (\\[i67] -> [1 + i67]))])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 -> tlet (tsum x2) (\\x5 -> tlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x6 -> tlet (x5 * x6) (\\x7 -> tlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x8 -> tlet (tconst 5.0) (\\x9 -> tlet (tsum x2) (\\x10 -> tlet (x9 * x10) (\\x11 -> tlet (tconst 3.0) (\\x12 -> tlet (sin x11) (\\x13 -> tlet (x7 * x8) (\\x14 -> tlet (x12 * x13) (\\x15 -> tlet (tsum x2) (\\x16 -> tlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x17 -> tlet (x16 * x17) (\\x18 -> tlet (x2 ! [rem (tminIndex0 x2) 4]) (\\x19 -> tlet (tconst 5.0) (\\x20 -> tlet (tsum x2) (\\x21 -> tlet (x20 * x21) (\\x22 -> tlet (tconst 3.0) (\\x23 -> tlet (sin x22) (\\x24 -> tlet (x18 * x19) (\\x25 -> tlet (x23 * x24) (\\x26 -> tlet (tsum x2) (\\x27 -> tlet (atan2 x14 x15 + x25 * x26) (\\x28 -> tlet (tgather [3] x2 (\\[i29] -> [1 + i29])) (\\x30 -> tlet (tkonst 3 (tsum x2)) (\\x31 -> tlet (sin x30) (\\x32 -> tlet (tkonst 3 (tsum x2)) (\\x33 -> tlet (x31 * x32) (\\x34 -> tlet (tgather [3] x2 (\\[i35] -> [1 + i35])) (\\x36 -> tlet (tkonst 3 (tsum x2)) (\\x37 -> tlet (sin x36) (\\x38 -> tlet (tkonst 3 (tsum x2)) (\\x39 -> tlet (x37 * x38) (\\x40 -> tlet (tgather [3] x2 (\\[i41] -> [1 + i41])) (\\x42 -> tlet (atan2 x33 x34 + x39 * x40) (\\x43 -> tlet (sin x42) (\\x44 -> tlet (tkonst 3 (tsum x2)) (\\x45 -> tlet (x43 * x44) (\\x46 -> tlet (tgather [3] x2 (\\[i48] -> [1 + i48])) (\\x49 -> tlet (tkonst 3 (tsum x2)) (\\x50 -> tlet (sin x49) (\\x51 -> tlet (tkonst 3 (tsum x2)) (\\x52 -> tlet (x50 * x51) (\\x53 -> tlet (tgather [3] x2 (\\[i54] -> [1 + i54])) (\\x55 -> tlet (tkonst 3 (tsum x2)) (\\x56 -> tlet (sin x55) (\\x57 -> tlet (tkonst 3 (tsum x2)) (\\x58 -> tlet (x56 * x57) (\\x59 -> tlet (tgather [3] x2 (\\[i60] -> [1 + i60])) (\\x61 -> tlet (atan2 x52 x53 + x58 * x59) (\\x62 -> tlet (sin x61) (\\x63 -> tlet (tgather [3] x2 (\\[i47] -> [1 + i47])) (\\x64 -> tlet (x62 * x63) (\\x65 -> tkonst 3 (x27 * x28) + atan2 x45 x46 + x64 * x65))))))))))))))))))))))))))))))))))))))))))))))))))))))"

fooMap1 :: ADReady r => TensorOf 0 r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] r
  in tmap0N (\x -> x * r + 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-6
    4.438131773948916e7
    (rev' @(OR.Array 1 Double) fooMap1 1.1)

testFooMap1PP :: Assertion
testFooMap1PP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (3, "dt")]
      fooMap1T = fooMap1 @(Ast0 Double)
  let (vars, AstVarName varDt, letGradientAst, vAst) =
        revDtFun fooMap1T 4
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 dt -> dlet (tsum (tkonst 130 x2)) (\\x6 -> dlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x7 -> dlet (x6 * x7) (\\x8 -> dlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x9 -> dlet (tconst 5.0) (\\x10 -> dlet (tsum (tkonst 130 x2)) (\\x11 -> dlet (x10 * x11) (\\x12 -> dlet (tconst 3.0) (\\x13 -> dlet (sin x12) (\\x14 -> dlet (x8 * x9) (\\x15 -> dlet (x13 * x14) (\\x16 -> dlet (tsum (tkonst 130 x2)) (\\x17 -> dlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x18 -> dlet (x17 * x18) (\\x19 -> dlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x20 -> dlet (tconst 5.0) (\\x21 -> dlet (tsum (tkonst 130 x2)) (\\x22 -> dlet (x21 * x22) (\\x23 -> dlet (tconst 3.0) (\\x24 -> dlet (sin x23) (\\x25 -> dlet (x19 * x20) (\\x26 -> dlet (x24 * x25) (\\x27 -> dlet (tsum (tkonst 130 x2)) (\\x28 -> dlet (atan2 x15 x16 + x26 * x27) (\\x29 -> dlet (tkonst 3 x2) (\\x30 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x31 -> dlet (sin x30) (\\x32 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x33 -> dlet (x31 * x32) (\\x34 -> dlet (tkonst 3 x2) (\\x35 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x36 -> dlet (sin x35) (\\x37 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x38 -> dlet (x36 * x37) (\\x39 -> dlet (tkonst 3 x2) (\\x40 -> dlet (atan2 x33 x34 + x38 * x39) (\\x41 -> dlet (sin x40) (\\x42 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x43 -> dlet (x41 * x42) (\\x44 -> dlet (tkonst 3 x2) (\\x45 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x46 -> dlet (sin x45) (\\x47 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x48 -> dlet (x46 * x47) (\\x49 -> dlet (tkonst 3 x2) (\\x50 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x51 -> dlet (sin x50) (\\x52 -> dlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x53 -> dlet (x51 * x52) (\\x54 -> dlet (tkonst 3 x2) (\\x55 -> dlet (atan2 x48 x49 + x53 * x54) (\\x56 -> dlet (sin x55) (\\x57 -> dlet (tkonst 3 x2) (\\x58 -> dlet (x56 * x57) (\\x59 -> dlet (tkonst 3 (x28 * x29) + atan2 x43 x44 + x58 * x59) (\\x60 -> dlet (tkonst 3 x2) (\\x61 -> dlet (x61 * dt) (\\x62 -> dlet (x58 * x62) (\\x63 -> dlet (x57 * x63) (\\x64 -> dlet (x53 * x64) (\\x65 -> dlet (negate (x48 * (tconst 1.0 / (x48 * x48 + x49 * x49))) * x64) (\\x66 -> dlet (negate (x43 * (tconst 1.0 / (x43 * x43 + x44 * x44))) * x62) (\\x67 -> dlet (x42 * x67) (\\x68 -> dlet (x38 * x68) (\\x69 -> dlet (negate (x33 * (tconst 1.0 / (x33 * x33 + x34 * x34))) * x68) (\\x70 -> dlet (tsum x62) (\\x71 -> dlet (x28 * x71) (\\x72 -> dlet (x26 * x72) (\\x73 -> dlet (cos x23 * (x24 * x73)) (\\x74 -> dlet (x27 * x72) (\\x75 -> dlet (x20 * x75) (\\x77 -> dlet (negate (x15 * (tconst 1.0 / (x15 * x15 + x16 * x16))) * x72) (\\x79 -> dlet (cos x12 * (x13 * x79)) (\\x80 -> dlet ((x16 * (tconst 1.0 / (x15 * x15 + x16 * x16))) * x72) (\\x81 -> dlet (x9 * x81) (\\x83 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tsum (x60 * dt) + tsum (tkonst 130 (x29 * x71)) + tsum (tkonst 130 (x7 * x83)) + tsum (tscatter [130] (tfromList [x6 * x83]) (\\[i84] -> [rem (tminIndex0 (tkonst 130 x2)) 130])) + tsum (tscatter [130] (tfromList [x8 * x81]) (\\[i82] -> [rem (tminIndex0 (tkonst 130 x2)) 130])) + tsum (tkonst 130 (x10 * x80)) + tsum (tkonst 130 (x18 * x77)) + tsum (tscatter [130] (tfromList [x17 * x77]) (\\[i78] -> [rem (tminIndex0 (tkonst 130 x2)) 130])) + tsum (tscatter [130] (tfromList [x19 * x75]) (\\[i76] -> [rem (tminIndex0 (tkonst 130 x2)) 130])) + tsum (tkonst 130 (x21 * x74)) + tsum (tkonst 130 (tsum ((x44 * (tconst 1.0 / (x43 * x43 + x44 * x44))) * x62))) + tsum (tkonst 130 (tsum ((x34 * (tconst 1.0 / (x33 * x33 + x34 * x34))) * x68))) + tsum (tkonst 130 (tsum (x32 * x70))) + tsum (cos x30 * (x31 * x70)) + tsum (tkonst 130 (tsum (x39 * x68))) + tsum (tkonst 130 (tsum (x37 * x69))) + tsum (cos x35 * (x36 * x69)) + tsum (cos x40 * (x41 * x67)) + tsum (x59 * x62) + tsum (tkonst 130 (tsum ((x49 * (tconst 1.0 / (x48 * x48 + x49 * x49))) * x64))) + tsum (tkonst 130 (tsum (x47 * x66))) + tsum (cos x45 * (x46 * x66)) + tsum (tkonst 130 (tsum (x54 * x64))) + tsum (tkonst 130 (tsum (x52 * x65))) + tsum (cos x50 * (x51 * x65)) + tsum (cos x55 * (x56 * x63)))]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 -> tlet (tsum (tkonst 130 x2)) (\\x6 -> tlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x7 -> tlet (x6 * x7) (\\x8 -> tlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x9 -> tlet (tconst 5.0) (\\x10 -> tlet (tsum (tkonst 130 x2)) (\\x11 -> tlet (x10 * x11) (\\x12 -> tlet (tconst 3.0) (\\x13 -> tlet (sin x12) (\\x14 -> tlet (x8 * x9) (\\x15 -> tlet (x13 * x14) (\\x16 -> tlet (tsum (tkonst 130 x2)) (\\x17 -> tlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x18 -> tlet (x17 * x18) (\\x19 -> tlet (tkonst 130 x2 ! [rem (tminIndex0 (tkonst 130 x2)) 130]) (\\x20 -> tlet (tconst 5.0) (\\x21 -> tlet (tsum (tkonst 130 x2)) (\\x22 -> tlet (x21 * x22) (\\x23 -> tlet (tconst 3.0) (\\x24 -> tlet (sin x23) (\\x25 -> tlet (x19 * x20) (\\x26 -> tlet (x24 * x25) (\\x27 -> tlet (tsum (tkonst 130 x2)) (\\x28 -> tlet (atan2 x15 x16 + x26 * x27) (\\x29 -> tlet (tkonst 3 x2) (\\x30 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x31 -> tlet (sin x30) (\\x32 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x33 -> tlet (x31 * x32) (\\x34 -> tlet (tkonst 3 x2) (\\x35 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x36 -> tlet (sin x35) (\\x37 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x38 -> tlet (x36 * x37) (\\x39 -> tlet (tkonst 3 x2) (\\x40 -> tlet (atan2 x33 x34 + x38 * x39) (\\x41 -> tlet (sin x40) (\\x42 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x43 -> tlet (x41 * x42) (\\x44 -> tlet (tkonst 3 x2) (\\x45 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x46 -> tlet (sin x45) (\\x47 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x48 -> tlet (x46 * x47) (\\x49 -> tlet (tkonst 3 x2) (\\x50 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x51 -> tlet (sin x50) (\\x52 -> tlet (tkonst 3 (tsum (tkonst 130 x2))) (\\x53 -> tlet (x51 * x52) (\\x54 -> tlet (tkonst 3 x2) (\\x55 -> tlet (atan2 x48 x49 + x53 * x54) (\\x56 -> tlet (sin x55) (\\x57 -> tlet (tkonst 3 x2) (\\x58 -> tlet (x56 * x57) (\\x59 -> tlet (tkonst 3 (x28 * x29) + atan2 x43 x44 + x58 * x59) (\\x60 -> tlet (tkonst 3 x2) (\\x61 -> x60 * x61 + tkonst 3 (tconst 5.0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r))
       => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. (ShowAst r, RealFloat r, Floating (Vector r))
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
  let f :: ( ShowAst r, RealFloat r, Floating (Vector r)
           , TensorOf 1 r ~ OR.Array 1 r, InterpretAst (ADVal r)
           , TensorOf 1 (ADVal r) ~ ADVal (TensorOf 1 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           EM.empty
                           (fooNoGoAst (AstVar [5] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (crev @(OR.Array 1 Double) f
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
      nestedMap x0 = tlet x0 $ \x -> tmap0N (x /) (w x)
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' (ix + iy :. ZI))
      doublyBuild = tbuild1 5 (tminimum . variableLengthBuild)
  in tmap0N (\x0 -> tlet x0 $ \x -> x * tsum0
                         (tbuild1 3 (\ix -> bar (x, tindex v' [ix]))
                          + fooBuild1 (nestedMap x)
                          / fooMap1 x)
            ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @(OR.Array 1 Double) nestedBuildMap 1.1)

nestedSumBuild :: ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedSumBuild v0 = tlet v0 $ \v ->
 tlet (tsum (tbuild1 9 tfromIndex0)) (\tbtf ->
  (tbuild1 13 (\ix ->
    tsum (tbuild1 4 (\ix2 ->
      flip tindex [ix2]
        (tlet (tsum v) $ \tsumv -> tbuild1 5 (\ _ -> tsumv)
         * tfromList
             [ tfromIndex0 ix
             , tbtf
             , tsum (tbuild1 6 (\_ -> tsum v))
             , tindex v [ix2]
             , tsum (tbuild1 3 (\ix7 ->
                 tsum (tkonst 5 (tfromIndex0 ix7))))
             ]))))))
 + tlet (nestedBuildMap (tsum0 v)) (\nbmt -> (tbuild1 13 (\ix ->
     nbmt `tindex` [min ix 4])))

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
  :: ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
  => TensorOf n r -> TensorOf n r
barRelu x = relu1 $ bar (x, relu1 x)

testBarReluADValDt :: Assertion
testBarReluADValDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 barRelu (OR.fromList [] [1.1]) 42.2)

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
     (KnownNat n, ShowAst r, RealFloat r, Floating (Vector r))
  => Ast n r -> Ast n r
barReluAst x = relu1 @n @(Ast0 r) $ bar (x, relu1 x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: ( ShowAst r, RealFloat r, Floating (Vector r)
           , TensorOf 0 r ~ OR.Array 0 r, InterpretAst (ADVal r)
           , TensorOf 0 (ADVal r) ~ ADVal (TensorOf 0 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           EM.empty
                           (barReluAst (AstVar [] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: ( ShowAst r, RealFloat r, Floating (Vector r)
           , TensorOf 1 r ~ OR.Array 1 r, InterpretAst (ADVal r)
           , TensorOf 1 (ADVal r) ~ ADVal (TensorOf 1 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           EM.empty
                           (barReluAst (AstVar [5] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @(OR.Array 1 Double) f (OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. (ShowAst r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ relu1 $ tkonst0N (7 :$ ZS) x

testKonstReluAst :: Assertion
testKonstReluAst =
  let f :: ( ShowAst r, RealFloat r, Floating (Vector r)
           , TensorOf 0 r ~ OR.Array 0 r, InterpretAst (ADVal r)
           , TensorOf 0 (ADVal r) ~ ADVal (TensorOf 0 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           EM.empty
                           (konstReluAst (AstVar [] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [295.4])
       (crevDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> tunScalar $ tsum0 (tbuild1 10 (\i -> tscalar arg * tfromIndex0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    45.0
    (srev @Double f1 1.1)

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
    (srev @Double f2 1.1)

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
    (rev @Double @2 braidedBuilds 3.4)

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @(OR.Array 2 Double) (braidedBuilds . tunScalar) 3.4)

recycled :: ADReady r
         => r -> TensorOf 5 r
recycled r =
  tlet (nestedSumBuild (tkonst0N [7] (tscalar r))) $ \nsb ->
    tbuild1 2 $ \_ -> tbuild1 4 $ \_ -> tbuild1 2 $ \_ -> tbuild1 3 $ \_ -> nsb

testRecycled :: Assertion
testRecycled =
  assertEqualUpToEpsilon 1e-6
    348356.9278600814
    (rev @Double @5 recycled 0.0000001)

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilon' 1e-6
    348356.9278600814
    (rev' @(OR.Array 5 Double) (recycled . tunScalar) 0.0000001)

concatBuild :: ADReady r => r -> TensorOf 2 r
concatBuild r =
  tbuild1 7 (\i ->
    tappend (tappend (tbuild1 5 (\_j -> tscalar r))
                     (tkonst 1 (tfromIndex0 i)))
            (tbuild1 13 (\_k -> tscalar r)))

testConcatBuild :: Assertion
testConcatBuild =
  assertEqualUpToEpsilon 1e-10
    126.0
    (rev @Double @2 concatBuild 3.4)

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    126.0
    (rev' @(OR.Array 2 Double) (concatBuild . tunScalar) 3.4)

emptyArgs :: forall r. ADReady r => TensorOf 1 r -> TensorOf 1 r
emptyArgs t =
  tfromList @r @0 []
  - tfromList0N (tshape @r (tfromList [])) []
  - treshape @r @1 [0] (tfromList [])
  - tgather1 0 (tfromList []) (:. ZI)
  - tsum (tgather1 0 (tfromList []) (const ZI))
  - tsum (tgather @r @2 (0 :$ 0 :$ ZS) (tfromList []) (const (0 :. ZI)))
  - tsum (tgather @r @2 @0 @1 [0, 0] (tfromList []) (const [0]))
  - tsum (treshape @r @1 [0, 0] (tfromList []))
  - tindex (tfromList0N (0 :$ 0 :$ ZS) []) (42 :. ZI)
  - tindex (tfromList0N (0 :$ tshape @r (tfromList [])) []) (42 :. ZI)
  - tsum (tfromList0N (0 :$ tshape @r (tfromList [])) [])
  * tsum (tfromList [ tsum (tfromList0N (0 :$ tshape @r (tfromList [])) [])
                    , treshape @r @1 [0] $ tfromList [] ])
  / tflatten (ttr (tgather1 0 t (const ZI)))
  + tbuild1 0 (\i -> t ! [fromIntegral (trank t) `quot` i] / tfromIndex0 i)
  -- - tsum (tbuild @r @2 (0 :$ 0 :$ ZS) (const 73))
  -- - tsum (tbuild @r @1 (0 :$ 0 :$ ZS) (const $ tfromList []))
       -- these fail and rightly so; TODO: make them fail earlier

testEmptyArgs0 :: Assertion
testEmptyArgs0 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [0] [])
    (rev' @(OR.Array 1 Double) emptyArgs (OR.fromList [0] []))

testEmptyArgs1 :: Assertion
testEmptyArgs1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @(OR.Array 1 Double) emptyArgs (OR.fromList [1] [0.24]))

testEmptyArgs4 :: Assertion
testEmptyArgs4 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @(OR.Array 1 Double)
          (\t -> tbuild [2, 5, 11, 0] (const $ emptyArgs t))
          (OR.fromList [1] [0.24]))

-- Catastrophic loss of sharing prevented.
fblowup :: forall r. ADReady r => Int -> TensorOf 1 r -> TensorOf 0 r
fblowup k inputs =
  let blowup :: Int -> TensorOf 0 r -> TensorOf 0 r
      blowup 0 y = y - tfromIndex0 0
      blowup n y =
        let ysum = y + y - tfromIndex0 0
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

fblowupLet :: forall r. ADReady r
           => IntOf r -> Int -> TensorOf 1 r -> TensorOf 0 r
fblowupLet i k inputs =
  let blowup :: Int -> TensorOf 0 r -> TensorOf 0 r
      blowup 0 y = y - tfromIndex0 i
      blowup n y1 = tlet y1 $ \y ->
        let ysum = y + y - tfromIndex0 i
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

-- Catastrophic loss of sharing prevented also with non-trivial multiplication.
fblowupMult :: forall r. ADReady r => Int -> TensorOf 1 r -> TensorOf 0 r
fblowupMult k inputs =
  let blowup :: Int -> TensorOf 0 r -> TensorOf 0 r
      blowup 0 y = y
      blowup n y =
        let ysum = y + y * y / (y - 0.000000001)
            yscaled = sqrt $ 0.499999985 * 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - tfromIndex0 0
      y0 = (inputs ! [0 `rem` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall r. ADReady r
               => IntOf r -> Int -> TensorOf 1 r -> TensorOf 0 r
fblowupMultLet i k inputs =
  let blowup :: Int -> TensorOf 0 r -> TensorOf 0 r
      blowup 0 y = y
      blowup n y1 = tlet y1 $ \y ->
        let ysum0 = y + y * y / (y - 0.000001)
            yscaled = tlet ysum0 $ \ysum ->
                        sqrt $ 0.499999985 * 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - tfromIndex0 i
      y0 = (inputs ! [i `rem` 2]) * (inputs ! [1])
  in blowup k y0

fblowupPP :: Assertion
fblowupPP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (3, "dt")]
      fblowupT = fblowup @(Ast0 Double) 1
  let (vars, AstVarName varDt, letGradientAst, vAst) =
        revDtFun fblowupT (OR.constant [4] 4)
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 dt -> dlet (x2 ! [0]) (\\x4 -> dlet (x2 ! [1]) (\\x5 -> dlet (x2 ! [0]) (\\x6 -> dlet (x2 ! [1]) (\\x7 -> dlet (tconst 0.499999985) (\\x8 -> dlet ((x4 / x5 + x6 / x7) - tconstant (tfromIndex0 0)) (\\x9 -> dlet (x8 * dt) (\\x10 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tscatter [4] (tfromList [recip x5 * x10]) (\\[i14] -> [0]) + tscatter [4] (tfromList [negate (x4 / (x5 * x5)) * x10]) (\\[i13] -> [1]) + tscatter [4] (tfromList [recip x7 * x10]) (\\[i12] -> [0]) + tscatter [4] (tfromList [negate (x6 / (x7 * x7)) * x10]) (\\[i11] -> [1]))]))))))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 -> tlet (x2 ! [0]) (\\x4 -> tlet (x2 ! [1]) (\\x5 -> tlet (x2 ! [0]) (\\x6 -> tlet (x2 ! [1]) (\\x7 -> tlet (tconst 0.499999985) (\\x8 -> tlet ((x4 / x5 + x6 / x7) - tconstant (tfromIndex0 0)) (\\x9 -> x8 * x9 - tconstant (tfromIndex0 0)))))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.fromList [(1, "s0"), (3, "dt")]
      fblowupLetT = fblowupLet @(Ast0 Double) 0 1
  let (vars, AstVarName varDt, letGradientAst, vAst) =
        revDtFun fblowupLetT (OR.constant [4] 4)
      varsPP = map (\(AstDynamicVarName (AstVarName var)) ->
                     printAstVar renames var "")
                   vars
      varsPPD = varsPP ++ [printAstVar renames varDt ""]
  "\\" ++ unwords varsPPD
       ++ " -> " ++ printAstDomainsSimple renames letGradientAst
    @?= "\\s0 x2 dt -> dlet (x2 ! [0]) (\\x5 -> dlet (x2 ! [1]) (\\x6 -> dlet (x5 / x6) (\\x7 -> dlet (tconst 0.499999985) (\\x8 -> dlet ((x7 + x7) - tconstant (tfromIndex0 0)) (\\x9 -> dlet (x8 * dt) (\\x10 -> dlet (x10 + x10) (\\x11 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tscatter [4] (tfromList [recip x6 * x11]) (\\[i13] -> [0]) + tscatter [4] (tfromList [negate (x5 / (x6 * x6)) * x11]) (\\[i12] -> [1]))]))))))))"
  "\\" ++ unwords varsPP ++ " -> " ++ printAstSimple renames vAst
    @?= "\\s0 x2 -> tlet (x2 ! [0]) (\\x5 -> tlet (x2 ! [1]) (\\x6 -> tlet (x5 / x6) (\\x7 -> tlet (tconst 0.499999985) (\\x8 -> tlet ((x7 + x7) - tconstant (tfromIndex0 0)) (\\x9 -> x8 * x9 - tconstant (tfromIndex0 0))))))"

-- TODO: should do 1000000 in a few seconds
blowupTests :: TestTree
blowupTests = testGroup "Catastrophic blowup avoidance tests"
  [ testCase "blowup 15" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333331833333646,-0.22222212222224305])
        (rev' @(OR.Array 0 Double) (fblowup 15) (OR.fromList [2] [2, 3]))
  , testCase "blowupLet 15" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333331833333646,-0.22222212222224305])
        (rev' @(OR.Array 0 Double) (fblowupLet 0 15) (OR.fromList [2] [2, 3]))
  , testCase "blowupLet 10000" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.33323334833020163,-0.22215556555346774])
        (rev' @(OR.Array 0 Double) (fblowupLet 0 10000)
                                   (OR.fromList [2] [2, 3]))
  , testCase "blowupLet tbuild1" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [33.332333348316844,-22.221555565544556])
        (rev' @(OR.Array 1 Double)
              (\intputs -> tbuild1 100 (\i -> fblowupLet i 1000 intputs))
              (OR.fromList [2] [2, 3]))
  , testCase "blowupMult 5" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.9999995500000267,1.9999997000000178])
        (rev' @(OR.Array 0 Double) (fblowupMult 5) (OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 5" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.9999995500000267,1.9999997000000178])
        (rev' @(OR.Array 0 Double) (fblowupMultLet 0 5)
                                   (OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 10000" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.9997300120201995,1.9998200080134665])  -- [2.9991001345552233,1.999400089703482])
        (rev' @(OR.Array 0 Double) (fblowupMultLet 0 3000)  -- !!! 10000
                                   (OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet tbuild1" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [14.99995479189822,39.999879676311515])  -- [14.999547940541992,39.998796798841916])
        (rev' @(OR.Array 1 Double)
              (\intputs -> tbuild1 100 (\i -> fblowupMultLet i 100 intputs))  -- !!! 1000
              (OR.fromList [2] [0.2, 0.3]))
  ]
