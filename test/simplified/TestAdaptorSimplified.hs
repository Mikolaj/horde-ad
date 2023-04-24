{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees, rev', assertEqualUpToEpsilon', assertEqualUpToEpsilonShort
  , t16, t16b, t48, t128, t128b, t128c
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
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor
import HordeAd.External.CommonRankedOps

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2zero" testZero
  , testCase "2foo" testFoo
  , testCase "2fooPP" testFooPP
  , testCase "2fooLet" testFooLet
  , testCase "2fooLetPP" testFooLetPP
  , testCase "2reluPP" testReluPP
  , testCase "2reluPP2" testReluPP2
  , testCase "2reluSimplerPP" testReluSimplerPP
  , testCase "2reluSimplerPP2" testReluSimplerPP2
  , testCase "2reluMaxPP" testReluMaxPP
  , testCase "2reluMaxPP2" testReluMaxPP2
  , testCase "2dot1PP" testDot1PP
  , testCase "2dot2PP" testDot2PP
  , testCase "2matmul1PP" testMatmul1PP
  , testCase "2matmul2PP" testMatmul2PP
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
  , testCase "2barReluADValMaxDt" testBarReluADValMaxDt
  , testCase "2barReluADValMax" testBarReluADValMax
  , testCase "2barReluADValMax3" testBarReluADValMax3
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
  let renames = IM.fromList [(3, "x"), (4, "y"), (5, "z")]
      renamesNull = IM.fromList [(1, "x1"), (2, "x2")]
      fooT = foo @(Ast 0 Double)
      foo3 x = fooT (x, x, x)
      (AstVarName var3, ast3) = funToAstR ZS foo3
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> atan2 x1 (x1 * sin x1) + x1 * (x1 * sin x1)"
  resetVarCounter
  let (artifact6, _) = revDtFun fooT (4, 5, 6)
  printGradient6Simple renames artifact6
    @?= "\\s0 dret x y z -> dlet (sin y) (\\x6 -> dlet (x * x6) (\\x7 -> dlet (recip (z * z + x7 * x7)) (\\x8 -> dlet (sin y) (\\x9 -> dlet (x * x9) (\\x10 -> dlet (z * dret) (\\x11 -> dlet (negate (z * x8) * dret) (\\x12 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (x6 * x12 + x9 * x11), dfromR (cos y * (x * x12) + cos y * (x * x11)), dfromR ((x7 * x8) * dret + x10 * dret)]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\s0 x y z -> tlet (sin y) (\\x6 -> tlet (x * x6) (\\x7 -> tlet (recip (z * z + x7 * x7)) (\\x8 -> tlet (sin y) (\\x9 -> tlet (x * x9) (\\x10 -> atan2 z x7 + z * x10)))))"

fooLet :: forall r n. (RealFloat (TensorOf n r), Tensor r, KnownNat n)
       => (TensorOf n r, TensorOf n r, TensorOf n r) -> TensorOf n r
fooLet (x, y, z) =
  let w0 = x * sin y
  in tlet w0 $ \w ->
     atan2 z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 fooLet (1.1, 2.2, 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let renames = IM.fromList [(3, "x"), (4, "y"), (5, "z")]
      renamesNull = IM.fromList [(1, "x1"), (2, "x2")]
      fooLetT = fooLet @(Ast0 Double)
      fooLet3 x = fooLetT (x, x, x)
      (AstVarName var3, ast3) = funToAstR ZS fooLet3
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tlet (x1 * sin x1) (\\x2 -> atan2 x1 x2 + x1 * x2)"
  resetVarCounter
  let (artifact6, _)= revDtFun fooLetT (4, 5, 6)
  printGradient6Simple renames artifact6
    @?= "\\s0 dret x y z -> dlet (sin y) (\\x7 -> dlet (x * x7) (\\x8 -> dlet (recip (z * z + x8 * x8)) (\\x9 -> dlet (negate (z * x9) * dret + z * dret) (\\x10 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (x7 * x10), dfromR (cos y * (x * x10)), dfromR ((x8 * x9) * dret + x8 * dret)])))))"
  printPrimal6Simple renames artifact6
    @?= "\\s0 x y z -> tlet (sin y) (\\x7 -> tlet (x * x7) (\\x8 -> tlet (recip (z * z + x8 * x8)) (\\x9 -> atan2 z x8 + z * x8)))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x y z -> let x7 = sin y ; x8 = x * x7 ; x9 = recip (z * z + x8 * x8) ; x10 = negate (z * x9) * dret + z * dret in (tfromList [], x7 * x10, cos y * (x * x10), (x8 * x9) * dret + x8 * dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x y z -> let x8 = x * sin y in atan2 z x8 + z * x8"

reluPrimal
  :: forall n r. (ADReady r, KnownNat n)
  => TensorOf n r -> TensorOf n r
reluPrimal v =
  let oneIfGtZero = tmap0N (\x -> ifB (x <=* 0) 0 1)
                           (tprimalPart v)
  in scale oneIfGtZero v

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT :: TensorOf 2 (Ast0 Double) -> TensorOf 2 (Ast0 Double)
      reluT = reluPrimal
      (AstVarName var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (x1 ! [i4, i3] <=* tconst 0.0) 0 1])) * x1"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT (OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (x3 ! [i7, i8] <=* tconst 0.0) 0 1]) in (tfromList [], x9 * dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> let x9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (x3 ! [i7, i8] <=* tconst 0.0) 0 1]) in x9 * x3"
  show deltas
    @?= "LetR 100000003 (ScaleR (AstVar [3,4] (AstVarId 100000009)) (InputR (InputId 0)))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT2 :: (TensorOf 1 (Ast0 Double), Ast0 Double)
             -> TensorOf 1 (Ast0 Double)
      reluT2 (t, r) = reluPrimal (t * tkonst 5 (tscalar r))
      (AstVarName var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i2] -> [ifB (x1 ! [i2] * tconst 7.0 <=* tconst 0.0) 0 1])) * (x1 * tkonst 5 (tconst 7.0))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT2 ((OR.constant [5] 128), 42)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x7 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x12 = x3 ! [i5] ; x13 = s0 ! [0] in x12 * x13) <=* tconst 0.0) 0 1]) ; x8 = x3 * x6 ; x9 = x7 * dret ; x11 = tscatter [1] (tfromList [tsum (x3 * x9)]) (\\[i10] -> [0]) in (tfromList [tconst 0.0 + x11 ! [0]], x6 * x9)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x7 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x12 = x3 ! [i5] ; x13 = s0 ! [0] in x12 * x13) <=* tconst 0.0) 0 1]) ; x8 = x3 * x6 in x7 * x8"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x9 = tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (x3 ! [i5] * s0 ! [0] <=* tconst 0.0) 0 1])) * dret in (tkonst 1 (tconst 0.0 + tscatter [1] (tkonst 1 (tsum (x3 * x9))) (\\[i10] -> [0]) ! [0]), x6 * x9)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x3 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (x3 ! [i5] * s0 ! [0] <=* tconst 0.0) 0 1])) * (x3 * tkonst 5 (s0 ! [0]))"
  show deltas
    @?= "LetR 100000013 (ScaleR (AstVar [5] (AstVarId 100000007)) (LetR 100000012 (AddR (ScaleR (AstVar [5] (AstVarId 100000006)) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000003)) (LetR 100000011 (ReshapeR [5] [5] (LetR 100000010 (KonstR 5 (LetR 100000009 (ScalarR (Let0 100000008 (UnScalar0 (LetR 100000007 (IndexZ (LetR 100000006 (FromVectorR [ScalarR (Input0 (InputId 0))])) [AstIntConst 0] [1]))))))))))))))"

testReluSimplerPP :: Assertion
testReluSimplerPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT :: TensorOf 2 (Ast0 Double) -> TensorOf 2 (Ast0 Double)
      reluT = relu
      (AstVarName var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (x1 ! [i4, i3] <=* tconst 0.0) 0 1])) * x1"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT (OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (x3 ! [i7, i8] <=* tconst 0.0) 0 1]) in (tfromList [], x9 * dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> let x9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (x3 ! [i7, i8] <=* tconst 0.0) 0 1]) in x9 * x3"
  show deltas
    @?= "LetR 100000003 (ScaleR (AstVar [3,4] (AstVarId 100000009)) (InputR (InputId 0)))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT2 :: (TensorOf 1 (Ast0 Double), Ast0 Double)
             -> TensorOf 1 (Ast0 Double)
      reluT2 (t, r) = relu (t * tkonst 5 (tscalar r))
      (AstVarName var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i2] -> [ifB (x1 ! [i2] * tconst 7.0 <=* tconst 0.0) 0 1])) * (x1 * tkonst 5 (tconst 7.0))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT2 ((OR.constant [5] 128), 42)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x7 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x12 = x3 ! [i5] ; x13 = s0 ! [0] in x12 * x13) <=* tconst 0.0) 0 1]) ; x8 = x3 * x6 ; x9 = x7 * dret ; x11 = tscatter [1] (tfromList [tsum (x3 * x9)]) (\\[i10] -> [0]) in (tfromList [tconst 0.0 + x11 ! [0]], x6 * x9)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x7 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x12 = x3 ! [i5] ; x13 = s0 ! [0] in x12 * x13) <=* tconst 0.0) 0 1]) ; x8 = x3 * x6 in x7 * x8"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x9 = tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (x3 ! [i5] * s0 ! [0] <=* tconst 0.0) 0 1])) * dret in (tkonst 1 (tconst 0.0 + tscatter [1] (tkonst 1 (tsum (x3 * x9))) (\\[i10] -> [0]) ! [0]), x6 * x9)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x3 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (x3 ! [i5] * s0 ! [0] <=* tconst 0.0) 0 1])) * (x3 * tkonst 5 (s0 ! [0]))"
  show deltas
    @?= "LetR 100000013 (ScaleR (AstVar [5] (AstVarId 100000007)) (LetR 100000012 (AddR (ScaleR (AstVar [5] (AstVarId 100000006)) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000003)) (LetR 100000011 (ReshapeR [5] [5] (LetR 100000010 (KonstR 5 (LetR 100000009 (ScalarR (Let0 100000008 (UnScalar0 (LetR 100000007 (IndexZ (LetR 100000006 (FromVectorR [ScalarR (Input0 (InputId 0))])) [AstIntConst 0] [1]))))))))))))))"

reluMax :: forall n r. (ADReady r, KnownNat n)
        => TensorOf n r -> TensorOf n r
reluMax v = tmap0N (maxB 0) v

testReluMaxPP :: Assertion
testReluMaxPP = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT :: TensorOf 2 (Ast0 Double) -> TensorOf 2 (Ast0 Double)
      reluT = reluMax
      (AstVarName var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tgather [3,4] (tfromList [tconstant (tkonst 3 (tkonst 4 (tconst 0.0))), x1]) (\\[i5, i4] -> [ifB (tconst 0.0 >=* x1 ! [i5, i4]) 0 1, i5, i4])"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT (OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x12 = tscatter [2,3,4] dret (\\[i10, i11] -> [ifB (tconst 0.0 >=* x3 ! [i10, i11]) 0 1, i10, i11]) in (tfromList [], x12 ! [1])"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> tgather [3,4] (tfromList [tkonst 3 (tkonst 4 (tconst 0.0)), x3]) (\\[i8, i9] -> [ifB (tconst 0.0 >=* x3 ! [i8, i9]) 0 1, i8, i9])"
  show deltas
    @?= "LetR 100000021 (GatherZ [3,4] (LetR 100000020 (FromListR [ZeroR,InputR (InputId 0)])) <function> [2,3,4])"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "x1"), (2, "i2")]
      reluT2 :: (TensorOf 1 (Ast0 Double), Ast0 Double)
             -> TensorOf 1 (Ast0 Double)
      reluT2 (t, r) = reluMax (t * tkonst 5 (tscalar r))
      (AstVarName var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarId renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tgather [5] (tfromList [tconstant (tkonst 5 (tconst 0.0)), x1 * tkonst 5 (tconst 7.0)]) (\\[i3] -> [ifB (tconst 0.0 >=* x1 ! [i3] * tconst 7.0) 0 1, i3])"
  resetVarCounter
  let (artifact6, deltas) = revDtFun reluT2 ((OR.constant [5] 128), 42)
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 -> let x6 = tkonst 5 (s0 ! [0]) ; x9 = tscatter [2,5] dret (\\[i8] -> [ifB (tconst 0.0 >=* (let x13 = x3 ! [i8] ; x14 = s0 ! [0] in x13 * x14)) 0 1, i8]) ; x10 = x9 ! [1] ; x12 = tscatter [1] (tfromList [tsum (x3 * x10)]) (\\[i11] -> [0]) in (tfromList [tconst 0.0 + x12 ! [0]], x6 * x10)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 -> let x6 = tkonst 5 (s0 ! [0]) in tgather [5] (tfromList [tkonst 5 (tconst 0.0), x3 * x6]) (\\[i7] -> [ifB (tconst 0.0 >=* (let x15 = x3 ! [i7] ; x16 = s0 ! [0] in x15 * x16)) 0 1, i7])"
  show deltas
    @?= "LetR 100000033 (GatherZ [5] (LetR 100000032 (FromListR [ZeroR,LetR 100000031 (AddR (ScaleR (AstVar [5] (AstVarId 100000006)) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000003)) (LetR 100000030 (ReshapeR [5] [5] (LetR 100000029 (KonstR 5 (LetR 100000028 (ScalarR (Let0 100000027 (UnScalar0 (LetR 100000026 (IndexZ (LetR 100000025 (FromVectorR [ScalarR (Input0 (InputId 0))])) [AstIntConst 0] [1]))))))))))))])) <function> [2,5])"

testDot1PP :: Assertion
testDot1PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun (uncurry (tdot0 @(Ast0 Double) @1))
                 ( OR.fromList [3] [1 .. 3]
                 , OR.fromList [7] [1 .. 7] )
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 x4 -> (tfromList [], x4 * tkonst 7 dret, x3 * tkonst 3 dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 -> tsum (x3 * x4)"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun (uncurry (tdot0 @(Ast0 Double) @2))
                 ( OR.fromList [2,3] [1 .. 6]
                 , OR.fromList [4,5] [1 .. 20] )
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 x4 -> let x5 = treshape [2,3] (tkonst 6 dret) in (tfromList [], x4 * x5, x3 * x5)"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 -> tsum (treshape [6] (x3 * x4))"

testMatmul1PP :: Assertion
testMatmul1PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun (uncurry tmatmul1) ( OR.fromList [2,3] [1 :: Double .. 6]
                                    , OR.fromList [7] [1 .. 7] )
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 x4 -> let x6 = tkonst 2 x4 ; x7 = ttranspose [1,0] (tkonst 7 dret) in (tfromList [], x6 * x7, tsum (x3 * x7))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 -> let x6 = tkonst 2 x4 in tsum (ttranspose [1,0] (x6 * x3))"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun (uncurry tmatmul2) ( OR.fromList [2,3] [1 :: Double .. 6]
                                    , OR.fromList [4,5] [1 .. 20] )
  printGradient6Pretty renames artifact6
    @?= "\\s0 dret x3 x4 -> let x7 = ttranspose [1,0] (tkonst 5 x3) ; x8 = tkonst 2 (ttranspose [1,0] x4) ; x9 = ttranspose [1,2,0] (tkonst 3 dret) in (tfromList [], tsum (ttranspose [1,0] (x8 * x9)), ttranspose [1,0] (tsum (x7 * x9)))"
  printPrimal6Pretty renames artifact6
    @?= "\\s0 x3 x4 -> let x7 = ttranspose [1,0] (tkonst 5 x3) ; x8 = tkonst 2 (ttranspose [1,0] x4) in tsum (ttranspose [2,0,1] (x7 * x8))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 dret x3 x4 -> let x9 = ttranspose [1,2,0] (tkonst 3 dret) in (tfromList [], tsum (ttranspose [1,0] (tkonst 2 (ttranspose [1,0] x4) * x9)), tsum (ttranspose [0,2,1] (ttranspose [1,0] (tkonst 5 x3) * x9)))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\s0 x3 x4 -> tsum (ttranspose [2,0,1] (ttranspose [1,0] (tkonst 5 x3) * tkonst 2 (ttranspose [1,0] x4)))"

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

fooMap1 :: ADReady r => TensorOf 0 r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] r
  in tmap0N (\x -> x * r + 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-3
    4.438131773975095e7
    (rev' @(OR.Array 1 Double) fooMap1 1.1)

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r))
       => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. (ShowAstSimplify r, RealFloat r, Floating (Vector r))
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
  let f :: ( ShowAstSimplify r, RealFloat r, Floating (Vector r)
           , TensorOf 1 r ~ OR.Array 1 r, InterpretAst (ADVal r)
           , TensorOf 1 (ADVal r) ~ ADVal (TensorOf 1 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           emptyMemo
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
barRelu x = relu $ bar (x, relu x)

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

barReluMax
  :: ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
  => TensorOf n r -> TensorOf n r
barReluMax x = reluMax $ bar (x, reluMax x)

testBarReluADValMaxDt :: Assertion
testBarReluADValMaxDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 barReluMax (OR.fromList [] [1.1]) 42.2)

testBarReluADValMax :: Assertion
testBarReluADValMax =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @(OR.Array 0 Double) barReluMax (OR.fromList [] [1.1]))

testBarReluADValMax3 :: Assertion
testBarReluADValMax3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @(OR.Array 3 Double) barReluMax (OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluAst
  :: forall n r.
     (KnownNat n, ShowAstSimplify r, RealFloat r, Floating (Vector r))
  => Ast n r -> Ast n r
barReluAst x = relu @n @(Ast0 r) $ bar (x, relu x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: ( ShowAstSimplify r, RealFloat r, Floating (Vector r)
           , TensorOf 0 r ~ OR.Array 0 r, InterpretAst (ADVal r)
           , TensorOf 0 (ADVal r) ~ ADVal (TensorOf 0 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           emptyMemo
                           (barReluAst (AstVar [] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: ( ShowAstSimplify r, RealFloat r, Floating (Vector r)
           , TensorOf 1 r ~ OR.Array 1 r, InterpretAst (ADVal r)
           , TensorOf 1 (ADVal r) ~ ADVal (TensorOf 1 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 1 r) -> ADVal (OR.Array 1 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           emptyMemo
                           (barReluAst (AstVar [5] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @(OR.Array 1 Double) f (OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. (ShowAstSimplify r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ relu $ tkonst0N (7 :$ ZS) x

testKonstReluAst :: Assertion
testKonstReluAst =
  let f :: ( ShowAstSimplify r, RealFloat r, Floating (Vector r)
           , TensorOf 0 r ~ OR.Array 0 r, InterpretAst (ADVal r)
           , TensorOf 0 (ADVal r) ~ ADVal (TensorOf 0 r)
           , DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
           , ScalarOf (ADVal r) ~ r )
        => ADVal (OR.Array 0 r) -> ADVal (OR.Array 0 r)
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstVarR $ dfromR x))
                           emptyMemo
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
  let renames = IM.empty
      fblowupT = fblowup @(Ast0 Double) 1
  let (artifact6, _) = revDtFun fblowupT (OR.constant [4] 4)
  printGradient6Simple renames artifact6
    @?= "\\s0 dret x3 -> dlet (x3 ! [0]) (\\x4 -> dlet (x3 ! [1]) (\\x5 -> dlet (x3 ! [0]) (\\x6 -> dlet (x3 ! [1]) (\\x7 -> dlet (tconst 0.499999985) (\\x8 -> dlet ((x4 / x5 + x6 / x7) - tconstant (tfromIndex0 0)) (\\x9 -> dlet (x8 * dret) (\\x10 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tscatter [4] (tfromList [recip x5 * x10]) (\\[i14] -> [0]) + tscatter [4] (tfromList [negate (x4 / (x5 * x5)) * x10]) (\\[i13] -> [1]) + tscatter [4] (tfromList [recip x7 * x10]) (\\[i12] -> [0]) + tscatter [4] (tfromList [negate (x6 / (x7 * x7)) * x10]) (\\[i11] -> [1]))]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\s0 x3 -> tlet (x3 ! [0]) (\\x4 -> tlet (x3 ! [1]) (\\x5 -> tlet (x3 ! [0]) (\\x6 -> tlet (x3 ! [1]) (\\x7 -> tlet (tconst 0.499999985) (\\x8 -> tlet ((x4 / x5 + x6 / x7) - tconstant (tfromIndex0 0)) (\\x9 -> x8 * x9 - tconstant (tfromIndex0 0)))))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupLetT = fblowupLet @(Ast0 Double) 0 1
  let (artifact6, _) = revDtFun fblowupLetT (OR.constant [4] 4)
  printGradient6Simple renames artifact6
    @?= "\\s0 dret x3 -> dlet (x3 ! [0]) (\\x5 -> dlet (x3 ! [1]) (\\x6 -> dlet (x5 / x6) (\\x7 -> dlet (tconst 0.499999985) (\\x8 -> dlet ((x7 + x7) - tconstant (tfromIndex0 0)) (\\x9 -> dlet (x8 * dret) (\\x10 -> dlet (x10 + x10) (\\x11 -> dmkDomains (fromList [dfromR (tfromList []), dfromR (tscatter [4] (tfromList [recip x6 * x11]) (\\[i13] -> [0]) + tscatter [4] (tfromList [negate (x5 / (x6 * x6)) * x11]) (\\[i12] -> [1]))]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\s0 x3 -> tlet (x3 ! [0]) (\\x5 -> tlet (x3 ! [1]) (\\x6 -> tlet (x5 / x6) (\\x7 -> tlet (tconst 0.499999985) (\\x8 -> tlet ((x7 + x7) - tconstant (tfromIndex0 0)) (\\x9 -> x8 * x9 - tconstant (tfromIndex0 0))))))"

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
        (OR.fromList [2] [2.9991001345552233,1.999400089703482])
        (rev' @(OR.Array 0 Double) (fblowupMultLet 0 10000)
                                   (OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet tbuild1" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [14.999547940541992,39.998796798841916])
        (rev' @(OR.Array 1 Double)
              (\intputs -> tbuild1 100 (\i -> fblowupMultLet i 1000 intputs))
              (OR.fromList [2] [0.2, 0.3]))
  ]
