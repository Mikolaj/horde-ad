{-# LANGUAGE OverloadedLists #-}
module TestAdaptorSimplified
  ( testTrees
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
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
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorOps
import HordeAd.External.CommonRankedOps

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "2zero" testZero
  , testCase "2zeroS" testZeroS
  , testCase "2zero2S" testZero2S
  , testCase "2zero3S" testZero3S
  , testCase "2piecewiseLinearPP" testPiecewiseLinearPP
  , testCase "2piecewiseLinear2PP" testPiecewiseLinear2PP
  , testCase "2overleaf" testOverleaf
  , testCase "2overleafPP" testOverleafPP
  , testCase "2foo" testFoo
  , testCase "2fooPP" testFooPP
  , testCase "2fooLet" testFooLet
  , testCase "2fooLetPP" testFooLetPP
  , testCase "2reluPP" testReluPP
  , testCase "2reluPP2" testReluPP2
  , testCase "2reluSimpler" testReluSimpler
  , testCase "2reluSimplerPP" testReluSimplerPP
  , testCase "2reluSimplerPP2" testReluSimplerPP2
  , testCase "2reluSimplerPP3" testReluSimplerPP3
  , testCase "2reluSimplerPP4" testReluSimplerPP4
  , testCase "2reluSimpler3" testReluSimpler3
  , testCase "2reluSimpler4" testReluSimpler4
  , testCase "2reluMax" testReluMax
  , testCase "2reluMaxPP" testReluMaxPP
  , testCase "2reluMaxPP2" testReluMaxPP2
  , testCase "2reluMax3" testReluMax3
  , testCase "2dot1PP" testDot1PP
  , testCase "2dot2PP" testDot2PP
  , testCase "2matvecmulPP" testMatvecmulPP
  , testCase "2matmul2PP" testMatmul2PP
  , testCase "2bar" testBar
  , testCase "2barS" testBarS
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
  , testCase "2konstReluAst" testReplicateReluAst
  , -- Tests by TomS:
    testCase "2F1" testF1
  , testCase "2F11" testF11
  , testCase "2F2" testF2
  , testCase "2F21" testF21
--  , testCase "2F3" testF3
  , -- Hairy tests
    testCase "2braidedBuilds1" testBraidedBuilds1
  , testCase "2recycled1" testRecycled1
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
    (rev' @Double @0 (const 3) 42)

testZeroS :: Assertion
testZeroS =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [0])
    (crev (let f :: Num a => a -> a
               f = const 3
           in f @(ADVal (Flip OS.Array) Double '[])) 42)

testZero2S :: Assertion
testZero2S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [1])
    (crev (let f :: a -> a
               f = id
           in f @(ADVal (Flip OS.Array) Double '[])) 42)

testZero3S :: Assertion
testZero3S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [3.6174114266850617])
    (crev (\x -> bar @(ADVal (Flip OS.Array) Double '[]) (x, x)) 1)

testPiecewiseLinearPP :: Assertion
testPiecewiseLinearPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: AstRanked Double 0
         -> AstRanked Double 0
      fT x = ifB (x >* 0) (2 * x) (5 * x)
      (artifact6, deltas) = revDtFun True fT 42
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret x2 -> let v5 = tscatter [2] dret (\\[] -> [ifB (x2 >* tconst 0.0) 0 1]) in (tconst 2.0 * v5 ! [0] + tconst 5.0 * v5 ! [1])"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\x2 -> tfromList [tconst 2.0 * x2, tconst 5.0 * x2] ! [ifB (x2 >* tconst 0.0) 0 1]"
  show deltas
    @?= "LetR 100000004 (IndexR (LetR 100000003 (FromListR [LetR 100000001 (ScaleR (AstVar [] (AstVarId 100000003)) (InputR (InputId 0))),LetR 100000002 (ScaleR (AstVar [] (AstVarId 100000004)) (InputR (InputId 0)))])) [AstIntCond (AstRel GtOp [AstPrimalPart {unAstPrimalPart = AstLetADShare ADShareNil (AstVar [] (AstVarId 100000002))},AstPrimalPart {unAstPrimalPart = AstLetADShare ADShareNil (AstLetADShare ADShareNil (AstConst (fromList [] [0.0])))}]) (AstIntConst 0) (AstIntConst 1)] [2])"

testPiecewiseLinear2PP :: Assertion
testPiecewiseLinear2PP = do
  resetVarCounter
  let renames = IM.empty
      fT :: AstRanked Double 0
         -> AstRanked Double 0
      fT x = ifB (x >* 0) 2 5 * x
      (artifact6, deltas) = revDtFun True fT 42
  printGradient6Pretty renames artifact6
    @?= "\\dret x2 -> let x3 = tfromList [tconst 2.0, tconst 5.0] ! [ifB (x2 >* tconst 0.0) 0 1] in (x3 * dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\x2 -> let x3 = tfromList [tconst 2.0, tconst 5.0] ! [ifB (x2 >* tconst 0.0) 0 1] in x3 * x2"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret x2 -> (tconst (fromList [2] [2.0,5.0]) ! [ifB (x2 >* tconst 0.0) 0 1] * dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\x2 -> tconst (fromList [2] [2.0,5.0]) ! [ifB (x2 >* tconst 0.0) 0 1] * x2"
  show deltas
    @?= "LetR 100000007 (ScaleR (AstVar [] (AstVarId 100000003)) (InputR (InputId 0)))"

overleaf :: forall ranked r. (Tensor ranked, GoodScalar r) => ranked r 1 -> ranked r 0
overleaf v = let wrap i = i `rem` fromIntegral (tlength v)
             in tsum (tbuild @ranked @r @1 [50] (\[i] -> tindex v [wrap i]))

testOverleaf :: Assertion
testOverleaf =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @1 [28] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @0 overleaf (tfromList0N [28] (map (Flip . tscalarR) $ [0 .. 27])))

testOverleafPP :: Assertion
testOverleafPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v"), (2, "i")]
      fT :: (AstRanked Double 1)
         -> AstRanked Double 0
      fT = overleaf
      (var3, ast3) = funToAstR [28] fT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v -> tsum (tgather [50] v (\\[i] -> [rem i 28]))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True fT (Flip $ OR.fromList [28] [0 .. 27])
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 -> (tscatter [28] (treplicate 50 dret) (\\[i5] -> [rem i5 28]))"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 -> tsum (tgather [50] v2 (\\[i4] -> [rem i4 28]))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= printGradient6Pretty renames artifact6
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= printPrimal6Pretty renames artifact6
  show deltas
    @?= "LetR 100000002 (SumR 50 (LetR 100000001 (GatherR [50] (InputR (InputId 0)) <function> [28])))"

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 @(Flip OR.Array) foo (1.1, 2.2, 3.3))

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      fooT = foo @(AstRanked Double 0)
      foo3 x = fooT (x, x, x)
      (var3, ast3) = funToAstR ZS foo3
  "\\" ++ printAstVarName IM.empty var3
       ++ " -> " ++ printAstSimple IM.empty ast3
    @?= "\\dret -> atan2 dret (dret * sin dret) + dret * (dret * sin dret)"
  resetVarCounter
  let (artifact6, _) = revDtFun True fooT (4, 5, 6)
  printGradient6Simple renames artifact6
    @?= "\\dret x y z -> rletToDomainsOf (sin y) (\\x5 -> rletToDomainsOf (x * x5) (\\x6 -> rletToDomainsOf (recip (z * z + x6 * x6)) (\\x7 -> rletToDomainsOf (sin y) (\\x8 -> rletToDomainsOf (x * x8) (\\x9 -> rletToDomainsOf (z * dret) (\\x10 -> rletToDomainsOf (negate (z * x7) * dret) (\\x11 -> dmkDomains (fromList [dfromR (x5 * x11 + x8 * x10), dfromR (cos y * (x * x11) + cos y * (x * x10)), dfromR ((x6 * x7) * dret + x9 * dret)]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\x y z -> tlet (sin y) (\\x5 -> tlet (x * x5) (\\x6 -> tlet (recip (z * z + x6 * x6)) (\\x7 -> tlet (sin y) (\\x8 -> tlet (x * x8) (\\x9 -> atan2 z x6 + z * x9)))))"

fooLet :: forall ranked r n. (RealFloat (ranked r n), Tensor ranked, KnownNat n, GoodScalar r)
       => (ranked r n, ranked r n, ranked r n) -> ranked r n
fooLet (x, y, z) =
  let w0 = x * sin y
  in tlet w0 $ \w ->
     atan2 z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 @(Flip OR.Array) fooLet (1.1, 2.2, 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      renamesNull = IM.fromList [(1, "x1"), (2, "x2")]
      fooLetT = fooLet @AstRanked @Double
      fooLet3 x = fooLetT (x, x, x)
      (var3, ast3) = funToAstR ZS fooLet3
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tlet (x1 * sin x1) (\\x2 -> atan2 x1 x2 + x1 * x2)"
  resetVarCounter
  let (artifact6, _)= revDtFun True fooLetT (4, 5, 6)
  printGradient6Simple renames artifact6
    @?= "\\dret x y z -> rletToDomainsOf (sin y) (\\x6 -> rletToDomainsOf (x * x6) (\\x7 -> rletToDomainsOf (recip (z * z + x7 * x7)) (\\x8 -> rletToDomainsOf (negate (z * x8) * dret + z * dret) (\\x9 -> dmkDomains (fromList [dfromR (x6 * x9), dfromR (cos y * (x * x9)), dfromR ((x7 * x8) * dret + x7 * dret)])))))"
  printPrimal6Simple renames artifact6
    @?= "\\x y z -> tlet (sin y) (\\x6 -> tlet (x * x6) (\\x7 -> tlet (recip (z * z + x7 * x7)) (\\x8 -> atan2 z x7 + z * x7)))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret x y z -> let x6 = sin y ; x7 = x * x6 ; x8 = recip (z * z + x7 * x7) ; x9 = negate (z * x8) * dret + z * dret in (x6 * x9, cos y * (x * x9), (x7 * x8) * dret + x7 * dret)"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\x y z -> let x7 = x * sin y in atan2 z x7 + z * x7"

reluPrimal
  :: forall ranked n r.
     (ADReady ranked r, KnownNat n)
  => ranked r n -> ranked r n
reluPrimal v =
  let oneIfGtZero = tmap0N (\x -> ifB (x <=* 0) 0.0 1.0)
                           (tprimalPart v)
  in scale oneIfGtZero v

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked Double 2 -> AstRanked Double 2
      reluT = reluPrimal
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (m1 ! [i4, i3] <=* tconst 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 -> let m8 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i6, i7] -> [ifB (m2 ! [i6, i7] <=* tconst 0.0) 0 1]) in (m8 * dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 -> let m8 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i6, i7] -> [ifB (m2 ! [i6, i7] <=* tconst 0.0) 0 1]) in m8 * m2"
  show deltas
    @?= "LetR 100000002 (ScaleR (AstVar [3,4] (AstVarId 100000008)) (InputR (InputId 0)))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked Double 1, AstRanked Double 0)
             -> AstRanked Double 1
      reluT2 (t, r) = reluPrimal (t * treplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i2] -> [ifB (v1 ! [i2] * tconst 7.0 <=* tconst 0.0) 0 1])) * (v1 * treplicate 5 (tconst 7.0))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 x3 -> let v6 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x9 = v2 ! [i5] in x9 * x3) <=* tconst 0.0) 0 1]) ; v7 = v2 * treplicate 5 x3 ; v8 = v6 * dret in (treplicate 5 x3 * v8, tsum (v2 * v8))"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 x3 -> let v6 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x9 = v2 ! [i5] in x9 * x3) <=* tconst 0.0) 0 1]) ; v7 = v2 * treplicate 5 x3 in v6 * v7"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret v2 x3 -> let v8 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (v2 ! [i5] * x3 <=* tconst 0.0) 0 1]) * dret in (treplicate 5 x3 * v8, tsum (v2 * v8))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\v2 x3 -> tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (v2 ! [i5] * x3 <=* tconst 0.0) 0 1]) * (v2 * treplicate 5 x3)"
  show deltas
    @?= "LetR 100000007 (ScaleR (AstVar [5] (AstVarId 100000006)) (LetR 100000006 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000003))) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000002)) (LetR 100000005 (ReplicateR 5 (InputR (InputId 1))))))))"

testReluSimpler :: Assertion
testReluSimpler = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 relu (tfromList0N [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluSimplerPP :: Assertion
testReluSimplerPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked Double 2 -> AstRanked Double 2
      reluT = relu
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (m1 ! [i4, i3] <=* tconst 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 -> let m8 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i6, i7] -> [ifB (m2 ! [i6, i7] <=* tconst 0.0) 0 1]) in (m8 * dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 -> let m8 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i6, i7] -> [ifB (m2 ! [i6, i7] <=* tconst 0.0) 0 1]) in m8 * m2"
  show deltas
    @?= "LetR 100000002 (ScaleR (AstVar [3,4] (AstVarId 100000008)) (InputR (InputId 0)))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked Double 1, AstRanked Double 0)
             -> AstRanked Double 1
      reluT2 (t, r) = relu (t * treplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tconstant (tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i2] -> [ifB (v1 ! [i2] * tconst 7.0 <=* tconst 0.0) 0 1])) * (v1 * treplicate 5 (tconst 7.0))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 x3 -> let v6 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x9 = v2 ! [i5] in x9 * x3) <=* tconst 0.0) 0 1]) ; v7 = v2 * treplicate 5 x3 ; v8 = v6 * dret in (treplicate 5 x3 * v8, tsum (v2 * v8))"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 x3 -> let v6 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB ((let x9 = v2 ! [i5] in x9 * x3) <=* tconst 0.0) 0 1]) ; v7 = v2 * treplicate 5 x3 in v6 * v7"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret v2 x3 -> let v8 = tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (v2 ! [i5] * x3 <=* tconst 0.0) 0 1]) * dret in (treplicate 5 x3 * v8, tsum (v2 * v8))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\v2 x3 -> tgather [5] (tconst (fromList [2] [0.0,1.0])) (\\[i5] -> [ifB (v2 ! [i5] * x3 <=* tconst 0.0) 0 1]) * (v2 * treplicate 5 x3)"
  show deltas
    @?= "LetR 100000007 (ScaleR (AstVar [5] (AstVarId 100000006)) (LetR 100000006 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000003))) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000002)) (LetR 100000005 (ReplicateR 5 (InputR (InputId 1))))))))"

testReluSimplerPP3 :: Assertion
testReluSimplerPP3 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked Double 2, AstRanked Double 0)
             -> AstRanked Double 2
      reluT2 (t, r) = relu (t * treplicate 3 (treplicate 4 r))
      (var3, ast3) = funToAstR [3, 4] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (v1 ! [i4, i3] * tconst 7.0 <=* tconst 0.0) 0 1])) * (v1 * treplicate 3 (treplicate 4 (tconst 7.0)))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT2 (Flip $ OR.constant [3, 4] 128, 42)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 x3 -> let m9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB ((let x12 = m2 ! [i7, i8] in x12 * x3) <=* tconst 0.0) 0 1]) ; m10 = m2 * treplicate 3 (treplicate 4 x3) ; m11 = m9 * dret in (treplicate 3 (treplicate 4 x3) * m11, tsum (tsum (m2 * m11)))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 x3 -> let m9 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB ((let x12 = m2 ! [i7, i8] in x12 * x3) <=* tconst 0.0) 0 1]) ; m10 = m2 * treplicate 3 (treplicate 4 x3) in m9 * m10"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 x3 -> let m11 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (m2 ! [i7, i8] * x3 <=* tconst 0.0) 0 1]) * dret in (treplicate 3 (treplicate 4 x3) * m11, tsum (tsum (m2 * m11)))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 x3 -> tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (m2 ! [i7, i8] * x3 <=* tconst 0.0) 0 1]) * (m2 * treplicate 3 (treplicate 4 x3))"
  show deltas
    @?= "LetR 100000014 (ScaleR (AstVar [3,4] (AstVarId 100000009)) (LetR 100000013 (AddR (ScaleR (AstReplicate 3 (AstReplicate 4 (AstVar [] (AstVarId 100000003)))) (InputR (InputId 0))) (ScaleR (AstVar [3,4] (AstVarId 100000002)) (LetR 100000012 (ReplicateR 3 (LetR 100000011 (ReplicateR 4 (InputR (InputId 1))))))))))"

testReluSimplerPP4 :: Assertion
testReluSimplerPP4 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked Double 2, AstRanked Double 0)
             -> AstRanked Double 2
      reluT2 (t, r) = relu (t * treplicate0N [3, 4] r)
      (var3, ast3) = funToAstR [3, 4] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tconstant (tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifB (v1 ! [i4, i3] * tconst 7.0 <=* tconst 0.0) 0 1])) * (v1 * treshape [3,4] (treplicate 12 (tconst 7.0)))"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT2 (Flip $ OR.constant [3, 4] 128, 42)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 x3 -> let m9 = treshape [3,4] (treplicate 12 x3) ; m10 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB ((let x15 = m2 ! [i7, i8] in x15 * x3) <=* tconst 0.0) 0 1]) ; m11 = m2 * m9 ; m12 = m10 * dret in (m9 * m12, tsum (treshape [12] (m2 * m12)))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 x3 -> let m9 = treshape [3,4] (treplicate 12 x3) ; m10 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB ((let x15 = m2 ! [i7, i8] in x15 * x3) <=* tconst 0.0) 0 1]) ; m11 = m2 * m9 in m10 * m11"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 x3 -> let m12 = tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (m2 ! [i7, i8] * x3 <=* tconst 0.0) 0 1]) * dret in (treplicate 3 (treplicate 4 x3) * m12, tsum (treshape [12] (m2 * m12)))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 x3 -> tgather [3,4] (tconst (fromList [2] [0.0,1.0])) (\\[i7, i8] -> [ifB (m2 ! [i7, i8] * x3 <=* tconst 0.0) 0 1]) * (m2 * treplicate 3 (treplicate 4 x3))"
  show deltas
    @?= "LetR 100000021 (ScaleR (AstVar [3,4] (AstVarId 100000010)) (LetR 100000020 (AddR (ScaleR (AstVar [3,4] (AstVarId 100000009)) (InputR (InputId 0))) (ScaleR (AstVar [3,4] (AstVarId 100000002)) (LetR 100000019 (ReshapeR [12] [3,4] (LetR 100000018 (ReplicateR 12 (InputR (InputId 1))))))))))"

testReluSimpler3 :: Assertion
testReluSimpler3 = do
  let reluT2 :: (AstRanked Double 2, AstRanked Double 0)
             -> AstRanked Double 2
      reluT2 (t, r) = relu (t * treplicate 3 (treplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

testReluSimpler4 :: Assertion
testReluSimpler4 = do
  let reluT2 :: (AstRanked Double 2, AstRanked Double 0)
             -> AstRanked Double 2
      reluT2 (t, r) = relu (t * treplicate0N [3, 4] r)
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

reluMax :: forall ranked n r. (ADReady ranked r, KnownNat n)
        => ranked r n -> ranked r n
reluMax v = tmap0N (maxB 0) v

testReluMax :: Assertion
testReluMax = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 reluMax (tfromList0N [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluMaxPP :: Assertion
testReluMaxPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked Double 2 -> AstRanked Double 2
      reluT = reluMax
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> tgather [3,4] (tfromList [tconstant (treplicate 3 (treplicate 4 (tconst 0.0))), m1]) (\\[i5, i4] -> [ifB (tconst 0.0 >=* m1 ! [i5, i4]) 0 1, i5, i4])"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 -> let t11 = tscatter [2,3,4] dret (\\[i9, i10] -> [ifB (tconst 0.0 >=* m2 ! [i9, i10]) 0 1, i9, i10]) in (t11 ! [1])"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 -> tgather [3,4] (tfromList [treplicate 3 (treplicate 4 (tconst 0.0)), m2]) (\\[i7, i8] -> [ifB (tconst 0.0 >=* m2 ! [i7, i8]) 0 1, i7, i8])"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 -> (tscatter [2,3,4] dret (\\[i9, i10] -> [ifB (tconst 0.0 >=* m2 ! [i9, i10]) 0 1, i9, i10]) ! [1])"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 -> tgather [3,4] (tfromList [treplicate 3 (treplicate 4 (tconst 0.0)), m2]) (\\[i7, i8] -> [ifB (tconst 0.0 >=* m2 ! [i7, i8]) 0 1, i7, i8])"
  show deltas
    @?= "LetR 100000004 (GatherR [3,4] (LetR 100000003 (FromListR [ZeroR,InputR (InputId 0)])) <function> [2,3,4])"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked Double 1, AstRanked Double 0)
             -> AstRanked Double 1
      reluT2 (t, r) = reluMax (t * treplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tgather [5] (tfromList [tconstant (treplicate 5 (tconst 0.0)), v1 * treplicate 5 (tconst 7.0)]) (\\[i3] -> [ifB (tconst 0.0 >=* v1 ! [i3] * tconst 7.0) 0 1, i3])"
  resetVarCounter
  let (artifact6, deltas) = revDtFun True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 x3 -> let m9 = tscatter [2,5] dret (\\[i7] -> [ifB (tconst 0.0 >=* (let x8 = v2 ! [i7] in x8 * x3)) 0 1, i7]) ; v10 = m9 ! [1] in (treplicate 5 x3 * v10, tsum (v2 * v10))"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 x3 -> tgather [5] (tfromList [treplicate 5 (tconst 0.0), v2 * treplicate 5 x3]) (\\[i6] -> [ifB (tconst 0.0 >=* (let x11 = v2 ! [i6] in x11 * x3)) 0 1, i6])"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret v2 x3 -> let v10 = tscatter [2,5] dret (\\[i7] -> [ifB (tconst 0.0 >=* v2 ! [i7] * x3) 0 1, i7]) ! [1] in (treplicate 5 x3 * v10, tsum (v2 * v10))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\v2 x3 -> tgather [5] (tfromList [treplicate 5 (tconst 0.0), v2 * treplicate 5 x3]) (\\[i6] -> [ifB (tconst 0.0 >=* v2 ! [i6] * x3) 0 1, i6])"
  show deltas
    @?= "LetR 100000011 (GatherR [5] (LetR 100000010 (FromListR [ZeroR,LetR 100000009 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000003))) (InputR (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000002)) (LetR 100000008 (ReplicateR 5 (InputR (InputId 1))))))])) <function> [2,5])"

testReluMax3 :: Assertion
testReluMax3 = do
  let reluT2 :: (AstRanked Double 2, AstRanked Double 0)
             -> AstRanked Double 2
      reluT2 (t, r) = reluMax (t * treplicate 3 (treplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

testDot1PP :: Assertion
testDot1PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun True (uncurry (tdot0 @AstRanked @Double @1))
                 ( Flip $ OR.fromList [3] [1 .. 3]
                 , Flip $ OR.fromList [3] [4 .. 6] )
  printGradient6Pretty renames artifact6
    @?= "\\dret v2 v3 -> (v3 * treplicate 3 dret, v2 * treplicate 3 dret)"
  printPrimal6Pretty renames artifact6
    @?= "\\v2 v3 -> tsum (v2 * v3)"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, deltas) =
        revDtFun True (uncurry (tdot0 @AstRanked @Double @2))
                 ( Flip $ OR.fromList [2,3] [1 .. 6]
                 , Flip $ OR.fromList [2,3] [7 .. 12] )
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 m3 -> (m3 * treshape [2,3] (treplicate 6 dret), m2 * treshape [2,3] (treplicate 6 dret))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 m3 -> tsum (treshape [6] (m2 * m3))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 m3 -> (m3 * treplicate 2 (treplicate 3 dret), m2 * treplicate 2 (treplicate 3 dret))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 m3 -> tsum (treshape [6] (m2 * m3))"
  show deltas
    @?= "LetR 100000002 (AddR (Dot0R (AstVar [2,3] (AstVarId 100000003)) (InputR (InputId 0))) (Dot0R (AstVar [2,3] (AstVarId 100000002)) (InputR (InputId 1))))"

testMatvecmulPP :: Assertion
testMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun True (uncurry tmatvecmul)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3] [7 .. 9] )
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 v3 -> (treplicate 2 v3 * ttranspose [1,0] (treplicate 3 dret), tsum (m2 * ttranspose [1,0] (treplicate 3 dret)))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 v3 -> tsum (ttranspose [1,0] (treplicate 2 v3 * m2))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 v3 -> (treplicate 2 v3 * ttranspose [1,0] (treplicate 3 dret), tsum (m2 * ttranspose [1,0] (treplicate 3 dret)))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 v3 -> tsum (ttranspose [1,0] (treplicate 2 v3 * m2))"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifact6, _) =
        revDtFun True (uncurry tmatmul2)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3,4] [7 .. 18] )
  printGradient6Pretty renames artifact6
    @?= "\\dret m2 m3 -> (tsum (ttranspose [2,0,1] (treplicate 2 m3) * ttranspose [2,1,0] (treplicate 3 dret)), tsum (ttranspose [1,2,0] (treplicate 4 m2) * ttranspose [1,0] (treplicate 3 dret)))"
  printPrimal6Pretty renames artifact6
    @?= "\\m2 m3 -> tsum (ttranspose [2,1,0] (treplicate 4 m2) * ttranspose [1,0] (treplicate 2 m3))"
  printGradient6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\dret m2 m3 -> (tsum (ttranspose [2,0,1] (treplicate 2 m3) * ttranspose [2,1,0] (treplicate 3 dret)), tsum (ttranspose [1,2,0] (treplicate 4 m2) * ttranspose [1,0] (treplicate 3 dret)))"
  printPrimal6Pretty renames (simplifyArtifact6 artifact6)
    @?= "\\m2 m3 -> tsum (ttranspose [2,1,0] (treplicate 4 m2) * ttranspose [1,0] (treplicate 2 m3))"

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (3.1435239435581166,-1.1053869545195814)
    (crev (bar @(ADVal (Flip OR.Array) Double 0)) (1.1, 2.2))

testBarS :: Assertion
testBarS =
  assertEqualUpToEpsilon 1e-9
    (3.1435239435581166,-1.1053869545195814)
    (crev (bar @(ADVal (Flip OS.Array) Double '[])) (1.1, 2.2))

barADVal2 :: forall a. RealFloat a
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
baz :: ( ADVal (Flip OR.Array) Double 0
       , ADVal (Flip OR.Array) Double 0
       , ADVal (Flip OR.Array) Double 0 )
    -> ADVal (Flip OR.Array) Double 0
baz (_x,y,z) =
  let w = fooConstant * barADVal2 (y,y,z) * sin y
  in atan2 z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal (Flip OR.Array) Double 0
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
fooD :: forall r. r ~ Double
     => [ADVal (Flip OR.Array) r 0] -> ADVal (Flip OR.Array) r 0
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [2.4396285219055063, -1.953374825727421, 0.9654825811012627]
    (crev fooD [1.1, 2.2, 3.3])

fooBuild1 :: ADReady ranked r => ranked r 1 -> ranked r 1
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
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [4] [-189890.46351219364,-233886.08744601303,-222532.22669716467,-206108.68889329425])
    (revDt @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]) (Flip $ OR.constant [3] 42))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]))

fooMap1 :: ADReady ranked r => ranked r 0 -> ranked r 1
fooMap1 r =
  let v = fooBuild1 $ treplicate0N [130] r
  in tmap0N (\x -> x * r + 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-3
    4.438131773975095e7
    (rev' @Double @1 fooMap1 1.1)

barAst :: (Numeric r, Show r, RealFloat r, RealFloat (Vector r))
       => (AstRanked r 0, AstRanked r 0) -> AstRanked r 0
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. GoodScalar r
           => AstRanked r 1 -> AstRanked r 1
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
  let f :: ( InterpretAstR (ADVal (Flip OR.Array)) r )
        => ADVal (Flip OR.Array) r 1 -> ADVal (Flip OR.Array) r 1
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstEnvElemR $ dfromR x))
                           emptyMemo
                           (fooNoGoAst (AstVar [5] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon1 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (crev @1 f
             (Flip $ OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

fooNoGo :: forall ranked r. ADReady ranked r
        => ranked r 1 -> ranked r 1
fooNoGo v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       bar (3.14, bar (3.14, tindex v [(ix + tfloor r) `min` 2 `max` 0]))
       + ifB ((&&*) (tindex @ranked @r @1 v [ix * 2] <=* 0)
                    (6 >* abs ix))
               r (5 * r))
     / tslice 1 3 (tmap0N (\x -> ifB (x >* r) r x) v)
     * tbuild1 3 (const 1)

testFooNoGo :: Assertion
testFooNoGo =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
   (rev' @Double @1 fooNoGo
         (Flip $ OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall ranked r. ADReady ranked r => ranked r 0 -> ranked r 1
nestedBuildMap r =
  let w = treplicate0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v0' = treplicate0N [177] r :: ranked r 1
  in tlet v0' $ \v' ->
    let nestedMap x0 = tlet x0 $ \x -> tmap0N (x /) (w x)
        variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' (ix + iy :. ZI))
        doublyBuild = tbuild1 5 (tminimum . variableLengthBuild)
    in tmap0N (\x0 -> tlet x0 $ \x -> x * tsum0
                           (tbuild1 3 (\ix -> bar (x, tindex v' [ix]))
                            + (tlet (nestedMap x) $ \x3 -> fooBuild1 x3)
                            / (tlet x $ \x4 -> fooMap1 x4))
              ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @Double @1 nestedBuildMap 1.1)

nestedSumBuild :: ADReady ranked r => ranked r 1 -> ranked r 1
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
                 tsum (treplicate 5 (tfromIndex0 ix7))))
             ]))))))
 + tlet (nestedBuildMap (tsum0 v)) (\nbmt -> (tbuild1 13 (\ix ->
     nbmt `tindex` [min ix 4])))

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @Double @1 nestedSumBuild (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall ranked r. ADReady ranked r => ranked r 1 -> ranked r 1
nestedBuildIndex v =
  tbuild1 2 $ \ix2 -> tindex (tbuild1 3 $ \ix3 -> tindex (tbuild1 4 $ \ix4 -> tindex v (ix4 :. ZI)) [ix3]) (ix2 :. ZI)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @Double @1 nestedBuildIndex (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( ADReady ranked r, KnownNat n, RealFloat (ranked r n) )
  => ranked r n -> ranked r n
barRelu x = relu $ bar (x, relu x)

testBarReluADValDt :: Assertion
testBarReluADValDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 @(Flip OR.Array) barRelu (Flip $ OR.fromList [] [1.1]) 42.2)

testBarReluADVal :: Assertion
testBarReluADVal =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barRelu (Flip $ OR.fromList [] [1.1]))

testBarReluADVal3 :: Assertion
testBarReluADVal3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barRelu (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluMax
  :: ( ADReady ranked r, KnownNat n, RealFloat (ranked r n) )
  => ranked r n -> ranked r n
barReluMax x = reluMax $ bar (x, reluMax x)

testBarReluADValMaxDt :: Assertion
testBarReluADValMaxDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 @(Flip OR.Array) barReluMax (Flip $ OR.fromList [] [1.1]) 42.2)

testBarReluADValMax :: Assertion
testBarReluADValMax =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barReluMax (Flip $ OR.fromList [] [1.1]))

testBarReluADValMax3 :: Assertion
testBarReluADValMax3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barReluMax (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluAst
  :: forall n r.
     (KnownNat n, ADReady AstRanked r)
  => AstRanked r n -> AstRanked r n
barReluAst x = relu $ bar (x, relu x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: ( ADReady AstRanked r
           , InterpretAstR (ADVal (Flip OR.Array)) r )
        => ADVal (Flip OR.Array) r 0 -> ADVal (Flip OR.Array) r 0
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstEnvElemR $ dfromR x))
                           emptyMemo
                           (barReluAst (AstVar [] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @0 @Double f (Flip $ OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: ( ADReady AstRanked r
           , InterpretAstR (ADVal (Flip OR.Array)) r )
        => ADVal (Flip OR.Array) r 1 -> ADVal (Flip OR.Array) r 1
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstEnvElemR $ dfromR x))
                           emptyMemo
                           (barReluAst (AstVar [5] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @1 @Double f (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. ADReady AstRanked r
  => AstRanked r 0 -> AstRanked r 0
konstReluAst x = tsum0 $ relu $ treplicate0N (7 :$ ZS) x

testReplicateReluAst :: Assertion
testReplicateReluAst =
  let f :: ( ADReady AstRanked r
           , InterpretAstR (ADVal (Flip OR.Array)) r )
        => ADVal (Flip OR.Array) r 0 -> ADVal (Flip OR.Array) r 0
      f x = snd
            $ interpretAst (EM.singleton (intToAstVarId 100000000) (AstEnvElemR $ dfromR x))
                           emptyMemo
                           (konstReluAst (AstVar [] (intToAstVarId 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [295.4])
       (crevDt @0 @Double f (Flip $ OR.fromList [] [1.1]) 42.2)


-- * Tests by TomS

f1 :: ADReady ranked r => ranked r 0 -> ranked r 0
f1 = \arg -> tsum0 (tbuild1 10 (\i -> arg * tfromIndex0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    45.0
    (rev @Double @0 @(Flip OR.Array) f1 1.1)

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    45.0
    (rev' @Double @0 f1 1.1)

f2 :: ADReady ranked r => ranked r 0 -> ranked r 0
f2 = \arg ->
  let fun1 i = arg * tfromIndex0 i
      v1a = tsum0 (tbuild1 10 fun1)
      v1b = tsum0 (tbuild1 20 fun1)
      fun2 y i = y * tfromIndex0 i
      v2a = tsum0 (tbuild1 10 (fun2 arg))
      v2b = tsum0 (tbuild1 20 (fun2 (arg + 1)))
  in v1a + v1b + v2a + v2b

testF2 :: Assertion
testF2 =
  assertEqualUpToEpsilon 1e-10
    470
    (rev @Double @0 @(Flip OR.Array) f2 1.1)

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    470
    (rev' @Double @0 f2 1.1)


-- * Hairy tests (many by TomS as well)

braidedBuilds :: forall ranked r. ADReady ranked r => ranked r 0 -> ranked r 2
braidedBuilds r =
  tbuild1 3 (\ix1 ->
    tbuild1 4 (\ix2 -> tindex (tfromList0N [4]
      [tfromIndex0 ix2, 7, r, -0.2]) (ix1 :. ZI)))

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @Double @2 braidedBuilds 3.4)

recycled :: ADReady ranked r
         => ranked r 0 -> ranked r 5
recycled r =
  tlet (nestedSumBuild (treplicate0N [7] r)) $ \nsb ->
    tbuild1 2 $ \_ -> tbuild1 4 $ \_ -> tbuild1 2 $ \_ -> tbuild1 3 $ \_ -> nsb

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilonShort 1e-6
    348356.9278600814
    (rev' @Double @5 recycled 0.0000001)

concatBuild :: ADReady ranked r => ranked r 0 -> ranked r 2
concatBuild r =
  tbuild1 7 (\i ->
    tappend (tappend (tbuild1 5 (\_j -> r))
                     (treplicate 1 (tfromIndex0 i)))
            (tbuild1 13 (\_k -> r)))

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    126.0
    (rev' @Double @2 concatBuild 3.4)

emptyArgs :: forall ranked r. ADReady ranked r => ranked r 1 -> ranked r 1
emptyArgs t =
  tfromList @ranked @r @0 []
  - tfromList0N (tshape @ranked @r (tfromList [])) []
  - treshape @ranked @r @1 [0] (tfromList [])
  - tgather1 0 (tfromList []) (:. ZI)
  - tsum (tgather1 0 (tfromList []) (const ZI))
  - tsum (tgather @ranked @r @2 (0 :$ 0 :$ ZS) (tfromList []) (const (0 :. ZI)))
  - tsum (tgather @ranked @r @2 @0 @1 [0, 0] (tfromList []) (const [0]))
  - tsum (treshape @ranked @r @1 [0, 0] (tfromList []))
  - tindex (tfromList0N (0 :$ 0 :$ ZS) []) (42 :. ZI)
  - tindex (tfromList0N (0 :$ tshape @ranked @r (tfromList [])) []) (42 :. ZI)
  - tsum (tfromList0N (0 :$ tshape @ranked @r (tfromList [])) [])
  * tsum (tfromList [tsum (tfromList0N (0 :$ tshape @ranked @r (tfromList [])) [])])
  * tflatten (ttr (tgather1 0 t (const ZI)))
  + tbuild1 0 (\i -> t ! [fromIntegral (trank t) `quot` i] / tfromIndex0 i)
  -- - tsum (tbuild @ranked @r @2 (0 :$ 0 :$ ZS) (const 73))
  -- - tsum (tbuild @ranked @r @1 (0 :$ 0 :$ ZS) (const $ tfromList []))
       -- these fail and rightly so; TODO: make them fail earlier

testEmptyArgs0 :: Assertion
testEmptyArgs0 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [0] [])
    (rev' @Double @1 emptyArgs (Flip $ OR.fromList [0] []))

testEmptyArgs1 :: Assertion
testEmptyArgs1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @Double @1 emptyArgs (Flip $ OR.fromList [1] [0.24]))

testEmptyArgs4 :: Assertion
testEmptyArgs4 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @Double @1
          (\t -> tbuild [2, 5, 11, 0] (const $ emptyArgs t))
          (Flip $ OR.fromList [1] [0.24]))

-- Catastrophic loss of sharing prevented.
fblowup :: forall ranked r. ADReady ranked r => Int -> ranked r 1 -> ranked r 0
fblowup k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y - tfromIndex0 0
      blowup n y =
        let ysum = y + y - tfromIndex0 0
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

fblowupLet :: forall ranked r. ADReady ranked r
           => IntOf ranked r -> Int -> ranked r 1 -> ranked r 0
fblowupLet i k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y - tfromIndex0 i
      blowup n y1 = tlet y1 $ \y ->
        let ysum = y + y - tfromIndex0 i
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

-- Catastrophic loss of sharing prevented also with non-trivial multiplication.
fblowupMult :: forall ranked r. ADReady ranked r => Int -> ranked r 1 -> ranked r 0
fblowupMult k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y
      blowup n y =
        let ysum = y + y * y / (y - 0.000000001)
            yscaled = sqrt $ 0.499999985 * 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - tfromIndex0 0
      y0 = (inputs ! [0 `rem` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall ranked r. ADReady ranked r
               => IntOf ranked r -> Int -> ranked r 1 -> ranked r 0
fblowupMultLet i k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
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
      fblowupT = fblowup @AstRanked @Double 1
  let (artifact6, _) = revDtFun True fblowupT (Flip $ OR.constant [4] 4)
  printGradient6Simple renames artifact6
    @?= "\\dret v2 -> rletToDomainsOf (v2 ! [0]) (\\x3 -> rletToDomainsOf (v2 ! [1]) (\\x4 -> rletToDomainsOf (v2 ! [0]) (\\x5 -> rletToDomainsOf (v2 ! [1]) (\\x6 -> rletToDomainsOf (tconst 0.499999985) (\\x7 -> rletToDomainsOf ((x3 / x4 + x5 / x6) - tfromIndex0 0) (\\x8 -> rletToDomainsOf (x7 * dret) (\\x9 -> dmkDomains (fromList [dfromR (tscatter [4] (recip x4 * x9) (\\[] -> [0]) + tscatter [4] (negate (x3 / (x4 * x4)) * x9) (\\[] -> [1]) + tscatter [4] (recip x6 * x9) (\\[] -> [0]) + tscatter [4] (negate (x5 / (x6 * x6)) * x9) (\\[] -> [1]))]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\v2 -> tlet (v2 ! [0]) (\\x3 -> tlet (v2 ! [1]) (\\x4 -> tlet (v2 ! [0]) (\\x5 -> tlet (v2 ! [1]) (\\x6 -> tlet (tconst 0.499999985) (\\x7 -> tlet ((x3 / x4 + x5 / x6) - tfromIndex0 0) (\\x8 -> x7 * x8 - tfromIndex0 0))))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupLetT = fblowupLet @AstRanked @Double 0 1
  let (artifact6, _) = revDtFun True fblowupLetT (Flip $ OR.constant [4] 4)
  printGradient6Simple renames artifact6
    @?= "\\dret v2 -> rletToDomainsOf (v2 ! [0]) (\\x4 -> rletToDomainsOf (v2 ! [1]) (\\x5 -> rletToDomainsOf (x4 / x5) (\\x6 -> rletToDomainsOf (tconst 0.499999985) (\\x7 -> rletToDomainsOf ((x6 + x6) - tfromIndex0 0) (\\x8 -> rletToDomainsOf (x7 * dret) (\\x9 -> rletToDomainsOf (x9 + x9) (\\x10 -> dmkDomains (fromList [dfromR (tscatter [4] (recip x5 * x10) (\\[] -> [0]) + tscatter [4] (negate (x4 / (x5 * x5)) * x10) (\\[] -> [1]))]))))))))"
  printPrimal6Simple renames artifact6
    @?= "\\v2 -> tlet (v2 ! [0]) (\\x4 -> tlet (v2 ! [1]) (\\x5 -> tlet (x4 / x5) (\\x6 -> tlet (tconst 0.499999985) (\\x7 -> tlet ((x6 + x6) - tfromIndex0 0) (\\x8 -> x7 * x8 - tfromIndex0 0)))))"

-- TODO: should do 1000000 in a few seconds
blowupTests :: TestTree
blowupTests = testGroup "Catastrophic blowup avoidance tests"
  [ testCase "blowup 7" $ do
      assertEqualUpToEpsilon' 1e-5
        (OR.fromList [2] [0.3333332333333467,-0.22222215555556446])
        (rev' @Double @0 (fblowup 7) (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet 15" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333331833333646,-0.22222212222224305])
        (rev' @Double @0 (fblowupLet 0 15) (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet 1000" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333233334831686,-0.22221555565544573])
        (rev' @Double @0 (fblowupLet 0 1000)
                                   (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (OR.fromList [2] [33.332333348316844,-22.221555565544556])
        (rev' @Double @1
              (\intputs -> tbuild1 100 (\i -> fblowupLet i 1000 intputs))
              (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupMult 3" $ do
      assertEqualUpToEpsilon' 1e-5
        (OR.fromList [2] [2.999999730000007,1.9999998200000046])
        (rev' @Double @0 (fblowupMult 3) (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 5" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.9999995500000267,1.9999997000000178])
        (rev' @Double @0 (fblowupMultLet 0 5)
                                   (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 50" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.999995500001215,1.99999700000081])
        (rev' @Double @0 (fblowupMultLet 0 50)
                                   (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (OR.fromList [2] [14.9999773958889,39.9999398380561])
        (rev' @Double @1
              (\intputs -> tbuild1 100 (\i -> fblowupMultLet i 50 intputs))
              (Flip $ OR.fromList [2] [0.2, 0.3]))
  ]
