{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fno-cse #-}
-- | Assorted rather low rank tensor tests.
module TestAdaptorSimplified
  ( testTrees
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.List (foldl1')
import qualified Data.Strict.IntMap as IM
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAstR, funToAstS, resetVarCounter)
import HordeAd.Core.IsPrimal (resetIdCounter)

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "2zeroZ" testZeroZ
  , testCase "2zeroS" testZeroS
  , testCase "2CFwdZeroS" testCFwdZeroS
  , testCase "2FwdZeroS" testFwdZeroS
  , testCase "2zero2S" testZero2S
  , testCase "2CFwdZero2S" testCFwdZero2S
  , testCase "2FwdZero2S" testFwdZero2S
  , testCase "2zero3S" testZero3S
  , testCase "2CFwdZero3S" testCFwdZero3S
  , testCase "2FwdZero3S" testFwdZero3S
  , testCase "2zero4S" testZero4S
  , testCase "2zero5S" testZero5S
  , testCase "2zero6S" testZero6S
  , testCase "2zero7S" testZero7S
  , testCase "2zero8" testZero8
  , testCase "2zero9S" testZero9S
  , testCase "2CFwdZero9S" testCFwdZero9S
  , testCase "2FwdZero9S" testFwdZero9S
  , testCase "2zero10S" testZero10S
  , testCase "2CFwdZero10S" testCFwdZero10S
  , testCase "2FwdZero10S" testFwdZero10S
  , testCase "2zero11S" testZero11S
  , testCase "2CFwdZero11S" testCFwdZero11S
  , testCase "2FwdZero11S" testFwdZero11S
  , testCase "2piecewiseLinearPP" testPiecewiseLinearPP
  , testCase "2piecewiseLinear2PP" testPiecewiseLinear2PP
  , testCase "2overleaf" testOverleaf
  , testCase "2overleafInt64n" testOverleafInt64
  , testCase "2overleafCIntn" testOverleafCInt
  , testCase "2overleafCIntToFloatn" testOverleafCIntToFloat
  , testCase "2overleafInt64p" testOverleafInt64p
  , testCase "2overleafCIntp" testOverleafCIntp
  , testCase "2overleafCIntToFloatp" testOverleafCIntToFloatp
  , testCase "2overleafPP" testOverleafPP
  , testCase "2foo" testFoo
  , testCase "2fooS" testFooS
  , testCase "2fooSToFloat" testFooSToFloat
  , testCase "2fooSBoth" testFooSBoth
  , testCase "2fooBoth" testFooBoth
  , testCase "2fooPP" testFooPP
  , testCase "2fooLet" testFooLet
  , testCase "2fooLetPP" testFooLetPP
  , testCase "2listProdPP" testListProdPP
  , testCase "2listProdrPP" testListProdrPP
  , testCase "2listProdrLongPP" testListProdrLongPP
  , testCase "2listProd" testListProd
  , testCase "2listProdr" testListProdr
  , testCase "2listSumrPP" testListSumrPP
  , testCase "2listSum2rPP" testListSum2rPP
  , testCase "2listSum22rPP" testListSum22rPP
  , testCase "2listSumk22rPP" testListSumk22rPP
  , testCase "2listSum2xpyrPP" testListSum2xpyrPP
  , testCase "2listSum2xyrPP" testListSum2xyrPP
  , testCase "2list2xyPP" test2xyPP
  , testCase "2listSum23rPP" testListSum23rPP
  , testCase "2list23PP" test23PP
  , testCase "2reluPP" testReluPP
  , testCase "2reluPP2" testReluPP2
  , testCase "2reluSimpler" testReluSimpler
  , testCase "2reluSimplerPP" testReluSimplerPP
  , testCase "2reluSimplerPP2" testReluSimplerPP2
  , testCase "2reluSimplerPP3" testReluSimplerPP3
  , testCase "2reluSimpler3" testReluSimpler3
  , testCase "2reluSimplerPP4" testReluSimplerPP4
  , testCase "2reluSimpler4" testReluSimpler4
  , testCase "2reluSimplerPP4S" testReluSimplerPP4S
  , testCase "2reluSimplerPP4S2" testReluSimplerPP4S2
  , testCase "2reluSimpler4S" testReluSimpler4S
  , testCase "2reluMax" testReluMax
  , testCase "2reluMaxPP" testReluMaxPP
  , testCase "2reluMaxPP2" testReluMaxPP2
  , testCase "2reluMax3" testReluMax3
  , testCase "2dot1PP" testDot1PP
  , testCase "2dot2PP" testDot2PP
  , testCase "2matvecmulPP" testMatvecmulPP
  , testCase "2matmul2PP" testMatmul2PP
  , testCase "2matmul2FromMatvecmulPP" testMatmul2FromMatvecmulPP
  , testCase "2matmul2PaperPP" testMatmul2PaperPP
  , testCase "2matmul2PPS" testMatmul2PPS
  , testCase "2bar" testBar
  , testCase "2barS" testBarS
  , testCase "2bar2S" testBar2S
  , testCase "2barCFwd" testBarCFwd
  , testCase "2barFwd" testBarFwd
  , testCase "2baz old to force fooConstant" testBaz
  , testCase "2baz if repetition breaks things" testBaz
  , testCase "2baz again with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuildCFwd" testFooBuildCFwd
  , testCase "2fooBuildFwd" testFooBuildFwd
  , testCase "2fooBuild" testFooBuild
  , testCase "2fooMap1" testFooMap1
  , testCase "2fooNoGoAst" testFooNoGoAst
  , testCase "2fooNoGo" testFooNoGo
  , testCase "2nestedBuildMap1" testNestedBuildMap1
  , testCase "2nestedSumBuild" testNestedSumBuild
  , testCase "2nestedBuildIndex" testNestedBuildIndex
  , testCase "2barReluDt" testBarReluDt
  , testCase "2barRelu" testBarRelu
  , testCase "2barRelu3" testBarRelu3
  , testCase "2barReluMaxDt" testBarReluMaxDt
  , testCase "2barReluMax" testBarReluMax
  , testCase "2barReluMax3" testBarReluMax3
  , testCase "2barReluMax3CFwd" testBarReluMax3CFwd
  , testCase "2barReluMax3FwdS" testBarReluMax3FwdS
  , testCase "2barReluMax3FwdFrom" testBarReluMax3FwdFrom
  , testCase "2barReluMax3FwdR" testBarReluMax3FwdR
  , testCase "2barReluAst0" testBarReluAst0
  , testCase "2barReluAst1" testBarReluAst1
  , testCase "2konstReluAst" testReplicateReluAst
  , testCase "2F1" testF1
  , testCase "2F11" testF11
  , testCase "2F2" testF2
  , testCase "2F21" testF21
  , testCase "2F2CFwd" testF2CFwd
  , testCase "2F2Fwd" testF2Fwd
  , testCase "2braidedBuilds1" testBraidedBuilds1
  , testCase "2recycled1" testRecycled1
  , testCase "2concatBuild1" testConcatBuild1
  , testCase "2emptyArgs0" testEmptyArgs0
  , testCase "2emptyArgs1" testEmptyArgs1
  , testCase "2emptyArgs4" testEmptyArgs4
  , testCase "2blowupPP" fblowupPP
  , testCase "2blowupLetPP" fblowupLetPP
  , blowupTests
  ]

testZeroZ :: Assertion
testZeroZ =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @0 [] [0])
    (rev' @Double @0 (let f :: forall f. ADReady f => f Double 0 -> f Double 0
                          f = const 3
                      in f) 42)

testZeroS :: Assertion
testZeroS =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (crev (let f :: Num a => a -> a
               f = const 3
           in f @(ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])) 42)

testCFwdZeroS :: Assertion
testCFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (cfwd (let f :: Num a => a -> a
               f = const 3
           in f @(ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])) 42 41)

testFwdZeroS :: Assertion
testFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (fwd (let f :: Num a => a -> a
              f = const 3
          in f @(AstShaped FullSpan Double '[0, 2, 4, 0, 1])) 42 41)

testZero2S :: Assertion
testZero2S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [1])
    (crev @Double @'[] @(Flip OS.Array)
          (let f :: a -> a
               f = id
           in f) 42)

testCFwdZero2S :: Assertion
testCFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [41])
    (cfwd @Double @'[] @(Flip OS.Array)
          (let f :: a -> a
               f = id
           in f) 42 41)

testFwdZero2S :: Assertion
testFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [41])
    (fwd @Double @'[]
          (let f :: a -> a
               f = id
           in f) 42 41)

testZero3S :: Assertion
testZero3S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[33, 2] (replicate 66 3.6174114266850617))
    (crev (\x -> bar @(ADVal (Flip OS.Array) Double '[33, 2]) (x, x)) 1)

testCFwdZero3S :: Assertion
testCFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[33, 2] (replicate 66 3.9791525693535674))
    (cfwd (\x -> bar @(ADVal (Flip OS.Array) Double '[33, 2]) (x, x)) 1 1.1)

testFwdZero3S :: Assertion
testFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[33, 2] (replicate 66 3.9791525693535674))
    (fwd (\x -> bar @(AstShaped FullSpan Double '[33, 2]) (x, x)) 1 1.1)

testZero4S :: Assertion
testZero4S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[] [0])
    (rev @Double @'[] @(AstShaped FullSpan)
         (let f :: Num a => a -> a
              f = const 3
          in f) 42)

testZero5S :: Assertion
testZero5S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[44] (replicate 44 1))
    (rev (let f :: a -> a
              f = id
          in f @(AstShaped FullSpan Double '[44])) 42)

testZero6S :: Assertion
testZero6S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] (replicate (product ([2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] :: [Int])) 3.6174114266850617))
    (rev @Double @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2]
         @(AstShaped FullSpan) (\x -> bar (x, x)) 1)

testZero7S :: Assertion
testZero7S =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[] [0])
    (rev (const 3 :: AstShaped FullSpan Double '[] -> AstRanked FullSpan Double 0) 42)

testZero8 :: Assertion
testZero8 =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [0])
    (rev (const 3 :: AstRanked FullSpan Double 0 -> AstShaped FullSpan Double '[]) 42)

testZero9S :: Assertion
testZero9S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OR.fromList [0, 2, 4, 0, 1] [])
    (crev (let f :: Num a => b -> a
               f = const 3
           in f @(ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])
                @(ADVal (Flip OR.Array) Double 5))
          (rreplicate0N [0, 2, 4, 0, 1] 42))

testCFwdZero9S :: Assertion
testCFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (cfwd (let f :: Num a => b -> a
               f = const 3
           in f @(ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])
                @(ADVal (Flip OR.Array) Double 5))
          (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testFwdZero9S :: Assertion
testFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (fwd (let f :: Num a => b -> a
              f = const 3
          in f @(AstShaped FullSpan Double '[0, 2, 4, 0, 1])
               @(AstRanked FullSpan Double 5))
          (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testZero10S :: Assertion
testZero10S =
  assertEqualUpToEpsilon 1e-9
    ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
    , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
    (crev (let f = const 3 . snd
           in f :: ( ADVal (Flip OR.Array) Double 5
                   , ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1] )
                   -> ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])
          (rreplicate0N [0, 2, 4, 0, 1] 42, 21))

testCFwdZero10S :: Assertion
testCFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (cfwd (let f = const 3 . snd
           in f :: ( ADVal (Flip OR.Array) Double 5
                   , ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1] )
                   -> ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1])
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] ))

testFwdZero10S :: Assertion
testFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OS.fromList @'[0, 2, 4, 0, 1] [])
    (fwd  (let f = const 3 . snd
           in f :: ( AstRanked FullSpan Double 5
                   , AstShaped FullSpan Double '[0, 2, 4, 0, 1] )
                   -> AstShaped FullSpan Double '[0, 2, 4, 0, 1])
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] ))

testZero11S :: Assertion
testZero11S =
  assertEqualUpToEpsilon 1e-9
    ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
    , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
    (crev (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal (Flip OR.Array) Double 5
                   , ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1] )
                   -> ADVal (Flip OR.Array) Double 5)
          (rreplicate0N [0, 2, 4, 0, 1] 42, 21))

testCFwdZero11S :: Assertion
testCFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OR.fromList [0, 2, 4, 0, 1] [])
    (cfwd (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal (Flip OR.Array) Double 5
                   , ADVal (Flip OS.Array) Double '[0, 2, 4, 0, 1] )
                   -> ADVal (Flip OR.Array) Double 5)
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] ))

testFwdZero11S :: Assertion
testFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (Flip $ OR.fromList [0, 2, 4, 0, 1] [])
    (fwd  (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( AstRanked FullSpan Double 5
                   , AstShaped FullSpan Double '[0, 2, 4, 0, 1] )
                   -> AstRanked FullSpan Double 5)
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] )
          ( Flip $ OR.fromList [0, 2, 4, 0, 1] []
          , Flip $ OS.fromList @'[0, 2, 4, 0, 1] [] ))

testPiecewiseLinearPP :: Assertion
testPiecewiseLinearPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: AstRanked FullSpan Double 0
         -> AstRanked FullSpan Double 0
      fT x = ifF (x >. 0) (2 * x) (5 * x)
      (artifactRev, deltas) = revArtifactAdapt True fT 42
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x2 x1 -> let v3 = rscatter [2] x2 (\\[] -> [ifF (x1 >. 0.0) 0 1]) in [2.0 * v3 ! [0] + 5.0 * v3 ! [1]]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 -> rfromList [2.0 * x1, 5.0 * x1] ! [ifF (x1 >. 0.0) 0 1]"
  show deltas
    @?= "LetR 100000004 (IndexR (LetR 100000003 (FromListR [LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0))),LetR 100000002 (ScaleR (AstConst (fromList [] [5.0])) (InputR [] (InputId 0)))])) [AstCond (AstRel GtOp (AstVar [] (AstVarId 100000001)) (AstConst (fromList [] [0.0]))) (AstConst (fromList [] [0])) (AstConst (fromList [] [1]))])"

testPiecewiseLinear2PP :: Assertion
testPiecewiseLinear2PP = do
  resetVarCounter
  let renames = IM.empty
      fT :: AstRanked FullSpan Double 0
         -> AstRanked FullSpan Double 0
      fT x = ifF (x >. 0) 2 5 * x
      (artifactRev, deltas) = revArtifactAdapt True fT 42
  printGradient6Pretty renames artifactRev
    @?= "\\x3 x1 -> let x2 = ifF (x1 >. 0.0) 2.0 5.0 in [x2 * x3]"
  printPrimal6Pretty renames artifactRev
    @?= "\\x1 -> let x2 = ifF (x1 >. 0.0) 2.0 5.0 in x2 * x1"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x3 x1 -> [ifF (x1 >. 0.0) 2.0 5.0 * x3]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 -> ifF (x1 >. 0.0) 2.0 5.0 * x1"
  show deltas
    @?= "LetR 100000005 (ScaleR (AstVar [] (AstVarId 100000002)) (InputR [] (InputId 0)))"

overleaf :: forall r ranked. (RankedTensor ranked, GoodScalar r)
         => ranked r 1 -> ranked r 0
overleaf v = let wrap i = i `rem` fromIntegral (rlength v)
             in rsum (rbuild @ranked @r @1 [50] (\[i] -> rindex v [wrap i]))

testOverleaf :: Assertion
testOverleaf =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @1 [28] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @0 overleaf (rfromList0N [28] (map (Flip . OR.scalar) [0 .. 27])))

testOverleafInt64 :: Assertion
testOverleafInt64 =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList @Int64 [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (crev @Int64 @0 overleaf (rfromList0N [28] (map (Flip . OR.scalar) [0 .. 27])))

testOverleafCInt :: Assertion
testOverleafCInt =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList @CInt [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev @CInt @0 @(AstRanked FullSpan) overleaf (rfromList0N [28] (map (Flip . OR.scalar) $ [0 .. 27])))

testOverleafCIntToFloat :: Assertion
testOverleafCIntToFloat =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList @Float @1 [28] (replicate 28 0.0))
    (rev @Float @0 @(AstRanked FullSpan) (rfromIntegral . overleaf @CInt . rfloor) (rfromList0N [28] (map (Flip . OR.scalar) [0 .. 27])))

testOverleafInt64p :: Assertion
testOverleafInt64p =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Int64 [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @Int64 @0 overleaf (rfromList0N [28] (map (Flip . OR.scalar) $ [0 .. 27])))

testOverleafCIntp :: Assertion
testOverleafCIntp =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @CInt [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @CInt @0 overleaf (rfromList0N [28] (map (Flip . OR.scalar) $ [0 .. 27])))

testOverleafCIntToFloatp :: Assertion
testOverleafCIntToFloatp =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Float @1 [28] (replicate 28 0.0))
    (let f :: forall f. ADReady f => f Float 1 -> f Float 0
         f = rfromIntegral . overleaf @CInt . rfloor
     in rev' @Float @0 f (rfromList0N [28] (map (Flip . OR.scalar) [0 .. 27])))

testOverleafPP :: Assertion
testOverleafPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v"), (2, "i")]
      fT :: AstRanked FullSpan Double 1
         -> AstRanked FullSpan Double 0
      fT = overleaf
      (var3, ast3) = funToAstR [28] fT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v -> rsum (rgather [50] v (\\[i] -> [rem i 28]))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True fT (Flip $ OR.fromList [28] [0 .. 27])
  printGradient6Pretty renames artifactRev
    @?= "\\x4 v1 -> [rscatter [28] (rreplicate 50 x4) (\\[i5] -> [rem i5 28])]"
  printPrimal6Pretty renames artifactRev
    @?= "\\v1 -> rsum (rgather [50] v1 (\\[i3] -> [rem i3 28]))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= printGradient6Pretty renames artifactRev
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= printPrimal6Pretty renames artifactRev
  show deltas
    @?= "LetR 100000002 (SumR (LetR 100000001 (GatherR [50] (InputR [28] (InputId 0)) <function>)))"

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 @(AstRanked FullSpan) foo (1.1, 2.2, 3.3))

testFooS :: Assertion
testFooS = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @'[3, 534, 3] @(AstShaped FullSpan) foo (1.1, 2.2, 3.3))

testFooSToFloat :: Assertion
testFooSToFloat = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Float @'[3, 534, 3] @(AstShaped FullSpan)
         (scast . foo)
         (1.1 :: Flip OS.Array Double '[3, 534, 3], 2.2, 3.3))

testFooSBoth :: Assertion
testFooSBoth = do
  assertEqualUpToEpsilon 1e-10
    (2.439628436155373, -1.9533749, 0.9654825479484146)
    (rev @Float @'[3, 534, 3] @(AstShaped FullSpan)
         (scast . foo . (\(d, f, d2) -> (d, scast f, d2)))
         ( 1.1 :: Flip OS.Array Double '[3, 534, 3]
         , 2.2 :: Flip OS.Array Float '[3, 534, 3]
         , 3.3 ))

testFooBoth :: Assertion
testFooBoth = do
  assertEqualUpToEpsilon 1e-10
    (2.439628436155373, -1.9533749, 0.9654825479484146)
    (rev @Float @0 @(AstRanked FullSpan)
         (rcast . foo . (\(d, f, d2) -> (d, rcast f, d2)))
         ( 1.1 :: Flip OR.Array Double 0
         , 2.2 :: Flip OR.Array Float 0
         , 3.3 ))

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      fooT = foo @(AstRanked FullSpan Double 0)
      foo3 x = fooT (x, x, x)
      (var3, ast3) = funToAstR ZS foo3
  "\\" ++ printAstVarName IM.empty var3
       ++ " -> " ++ printAstSimple IM.empty ast3
    @?= "\\x1 -> atan2 x1 (x1 * sin x1) + x1 * (x1 * sin x1)"
  resetVarCounter
  let (artifactRev, _) = revArtifactAdapt True fooT (4, 5, 6)
  printGradient6Simple renames artifactRev
    @?= "\\x9 x1 x y -> rletInHVector (sin x) (\\z -> rletInHVector (x1 * z) (\\x5 -> rletInHVector (recip (y * y + x5 * x5)) (\\x6 -> rletInHVector (sin x) (\\x7 -> rletInHVector (x1 * x7) (\\x8 -> rletInHVector (y * x9) (\\x10 -> rletInHVector (negate (y * x6) * x9) (\\x11 -> dmkHVector (fromList [DynamicRanked (z * x11 + x7 * x10), DynamicRanked (cos x * (x1 * x11) + cos x * (x1 * x10)), DynamicRanked ((x5 * x6) * x9 + x8 * x9)]))))))))"
  printPrimal6Simple renames artifactRev
    @?= "\\x1 x y -> rlet (sin x) (\\z -> rlet (x1 * z) (\\x5 -> rlet (recip (y * y + x5 * x5)) (\\x6 -> rlet (sin x) (\\x7 -> rlet (x1 * x7) (\\x8 -> atan2 y x5 + y * x8)))))"

fooLet :: forall ranked r n.
          (RealFloat (ranked r n), RankedTensor ranked, KnownNat n, GoodScalar r)
       => (ranked r n, ranked r n, ranked r n) -> ranked r n
fooLet (x, y, z) =
  let w0 = x * sin y
  in rlet w0 $ \w ->
     atan2 z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (rev @Double @0 @(AstRanked FullSpan) fooLet (1.1, 2.2, 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      renamesNull = IM.fromList [(1, "x1"), (2, "x2")]
      fooLetT = fooLet @(AstRanked FullSpan) @Double
      fooLet3 x = fooLetT (x, x, x)
      (var3, ast3) = funToAstR ZS fooLet3
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> rlet (x1 * sin x1) (\\x2 -> atan2 x1 x2 + x1 * x2)"
  resetVarCounter
  let (artifactRev, _)= revArtifactAdapt True fooLetT (4, 5, 6)
  printGradient6Simple renames artifactRev
    @?= "\\x8 x1 x y -> rletInHVector (sin x) (\\x5 -> rletInHVector (x1 * x5) (\\x6 -> rletInHVector (recip (y * y + x6 * x6)) (\\x7 -> rletInHVector (negate (y * x7) * x8 + y * x8) (\\x9 -> dmkHVector (fromList [DynamicRanked (x5 * x9), DynamicRanked (cos x * (x1 * x9)), DynamicRanked ((x6 * x7) * x8 + x6 * x8)])))))"
  printPrimal6Simple renames artifactRev
    @?= "\\x1 x y -> rlet (sin x) (\\x5 -> rlet (x1 * x5) (\\x6 -> rlet (recip (y * y + x6 * x6)) (\\x7 -> atan2 y x6 + y * x6)))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x8 x1 x y -> let x5 = sin x ; x6 = x1 * x5 ; x7 = recip (y * y + x6 * x6) ; x9 = negate (y * x7) * x8 + y * x8 in [x5 * x9, cos x * (x1 * x9), (x6 * x7) * x8 + x6 * x8]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x y -> let x6 = x1 * sin x in atan2 y x6 + y * x6"

shapedListProd :: (ShapedTensor shaped, GoodScalar r)
               => [shaped r '[]] -> shaped r '[]
shapedListProd = foldl1' (*)

testListProdPP :: Assertion
testListProdPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstShaped FullSpan Double '[]] -> AstShaped FullSpan Double '[]
      fT = shapedListProd
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6SimpleS renames artifactRev
    @?= "\\x7 x1 x2 x3 x4 -> sletInHVector (x1 * x2) (\\x5 -> sletInHVector (x5 * x3) (\\x6 -> sletInHVector (x4 * x7) (\\x8 -> sletInHVector (x3 * x8) (\\x9 -> dmkHVector (fromList [DynamicShaped (x2 * x9), DynamicShaped (x1 * x9), DynamicShaped (x5 * x8), DynamicShaped (x6 * x7)])))))"
  printPrimal6SimpleS renames artifactRev
    @?= "\\x1 x2 x3 x4 -> slet (x1 * x2) (\\x5 -> slet (x5 * x3) (\\x6 -> x6 * x4))"
  printGradient6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x5 = x1 * x2 ; x8 = x4 * x7 ; x9 = x3 * x8 in [x2 * x9, x1 * x9, x5 * x8, (x5 * x3) * x7]"
  printPrimal6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\x1 x2 x3 x4 -> ((x1 * x2) * x3) * x4"
  show deltas
    @?= "LetS 100000003 (AddS (ScaleS (AstVarS (AstVarId 100000004)) (LetS 100000002 (AddS (ScaleS (AstVarS (AstVarId 100000003)) (LetS 100000001 (AddS (ScaleS (AstVarS (AstVarId 100000002)) (InputS (InputId 0))) (ScaleS (AstVarS (AstVarId 100000001)) (InputS (InputId 1)))))) (ScaleS (AstVarS (AstVarId 100000005)) (InputS (InputId 2)))))) (ScaleS (AstVarS (AstVarId 100000006)) (InputS (InputId 3))))"

rankedListProdr :: (RankedTensor ranked, GoodScalar r)
                => [ranked r 0] -> ranked r 0
rankedListProdr = foldr1 (*)

testListProdrPP :: Assertion
testListProdrPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListProdr
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Simple renames artifactRev
    @?= "\\x7 x1 x2 x3 x4 -> rletInHVector (x3 * x4) (\\x5 -> rletInHVector (x2 * x5) (\\x6 -> rletInHVector (x1 * x7) (\\x8 -> rletInHVector (x2 * x8) (\\x9 -> dmkHVector (fromList [DynamicRanked (x6 * x7), DynamicRanked (x5 * x8), DynamicRanked (x4 * x9), DynamicRanked (x3 * x9)])))))"
  printPrimal6Simple renames artifactRev
    @?= "\\x1 x2 x3 x4 -> rlet (x3 * x4) (\\x5 -> rlet (x2 * x5) (\\x6 -> x1 * x6))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x5 = x3 * x4 ; x8 = x1 * x7 ; x9 = x2 * x8 in [(x2 * x5) * x7, x5 * x8, x4 * x9, x3 * x9]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> x1 * (x2 * (x3 * x4))"
  show deltas
    @?= "LetR 100000006 (AddR (ScaleR (AstVar [] (AstVarId 100000006)) (InputR [] (InputId 0))) (ScaleR (AstVar [] (AstVarId 100000001)) (LetR 100000005 (AddR (ScaleR (AstVar [] (AstVarId 100000005)) (InputR [] (InputId 1))) (ScaleR (AstVar [] (AstVarId 100000002)) (LetR 100000004 (AddR (ScaleR (AstVar [] (AstVarId 100000004)) (InputR [] (InputId 2))) (ScaleR (AstVar [] (AstVarId 100000003)) (InputR [] (InputId 3))))))))))"

testListProdrLongPP :: Assertion
testListProdrLongPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListProdr
  let (artifactRev, _)=
        revArtifactAdapt True fT [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  printGradient6Simple renames artifactRev
    @?= "\\x25 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> rletInHVector (x12 * x13) (\\x14 -> rletInHVector (x11 * x14) (\\x15 -> rletInHVector (x10 * x15) (\\x16 -> rletInHVector (x9 * x16) (\\x17 -> rletInHVector (x8 * x17) (\\x18 -> rletInHVector (x7 * x18) (\\x19 -> rletInHVector (x6 * x19) (\\x20 -> rletInHVector (x5 * x20) (\\x21 -> rletInHVector (x4 * x21) (\\x22 -> rletInHVector (x3 * x22) (\\x23 -> rletInHVector (x2 * x23) (\\x24 -> rletInHVector (x1 * x25) (\\x26 -> rletInHVector (x2 * x26) (\\x27 -> rletInHVector (x3 * x27) (\\x28 -> rletInHVector (x4 * x28) (\\x29 -> rletInHVector (x5 * x29) (\\x30 -> rletInHVector (x6 * x30) (\\x31 -> rletInHVector (x7 * x31) (\\x32 -> rletInHVector (x8 * x32) (\\x33 -> rletInHVector (x9 * x33) (\\x34 -> rletInHVector (x10 * x34) (\\x35 -> rletInHVector (x11 * x35) (\\x36 -> dmkHVector (fromList [DynamicRanked (x24 * x25), DynamicRanked (x23 * x26), DynamicRanked (x22 * x27), DynamicRanked (x21 * x28), DynamicRanked (x20 * x29), DynamicRanked (x19 * x30), DynamicRanked (x18 * x31), DynamicRanked (x17 * x32), DynamicRanked (x16 * x33), DynamicRanked (x15 * x34), DynamicRanked (x14 * x35), DynamicRanked (x13 * x36), DynamicRanked (x12 * x36)])))))))))))))))))))))))"
  printPrimal6Simple renames artifactRev
    @?= "\\x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> rlet (x12 * x13) (\\x14 -> rlet (x11 * x14) (\\x15 -> rlet (x10 * x15) (\\x16 -> rlet (x9 * x16) (\\x17 -> rlet (x8 * x17) (\\x18 -> rlet (x7 * x18) (\\x19 -> rlet (x6 * x19) (\\x20 -> rlet (x5 * x20) (\\x21 -> rlet (x4 * x21) (\\x22 -> rlet (x3 * x22) (\\x23 -> rlet (x2 * x23) (\\x24 -> x1 * x24)))))))))))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x25 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> let x14 = x12 * x13 ; x15 = x11 * x14 ; x16 = x10 * x15 ; x17 = x9 * x16 ; x18 = x8 * x17 ; x19 = x7 * x18 ; x20 = x6 * x19 ; x21 = x5 * x20 ; x22 = x4 * x21 ; x23 = x3 * x22 ; x26 = x1 * x25 ; x27 = x2 * x26 ; x28 = x3 * x27 ; x29 = x4 * x28 ; x30 = x5 * x29 ; x31 = x6 * x30 ; x32 = x7 * x31 ; x33 = x8 * x32 ; x34 = x9 * x33 ; x35 = x10 * x34 ; x36 = x11 * x35 in [(x2 * x23) * x25, x23 * x26, x22 * x27, x21 * x28, x20 * x29, x19 * x30, x18 * x31, x17 * x32, x16 * x33, x15 * x34, x14 * x35, x13 * x36, x12 * x36]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> x1 * (x2 * (x3 * (x4 * (x5 * (x6 * (x7 * (x8 * (x9 * (x10 * (x11 * (x12 * x13)))))))))))"

testListProd :: Assertion
testListProd = do
  assertEqualUpToEpsilon 1e-10
    [24, 12, 8, 6]
    (rev @Double @'[] @(AstShaped FullSpan) shapedListProd [1, 2, 3, 4])

testListProdr :: Assertion
testListProdr = do
  assertEqualUpToEpsilon 1e-10
    [24, 12, 8, 6]
    (rev @Double @0 @(AstRanked FullSpan) rankedListProdr [1, 2, 3, 4])

rankedListSumr :: (RankedTensor ranked, GoodScalar r)
                => [ranked r 0] -> ranked r 0
rankedListSumr = foldr1 (+)

testListSumrPP :: Assertion
testListSumrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSumr
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x5 x1 x2 x3 x4 -> [x5, x5, x5, x5]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> x1 + x2 + x3 + x4"
  show deltas
    @?= "LetR 100000003 (AddR (InputR [] (InputId 0)) (LetR 100000002 (AddR (InputR [] (InputId 1)) (LetR 100000001 (AddR (InputR [] (InputId 2)) (InputR [] (InputId 3)))))))"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum2r :: (RankedTensor ranked, GoodScalar r)
                => [ranked r 0] -> ranked r 0
rankedListSum2r = foldr1 (\x y -> x + 2 * y)

testListSum2rPP :: Assertion
testListSum2rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum2r
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x8 = 2.0 * x7 ; x9 = 2.0 * x8 in [x7, x8, x9, 2.0 * x9]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> x1 + 2.0 * (x2 + 2.0 * (x3 + 2.0 * x4))"
  show deltas
    @?= "LetR 100000006 (AddR (InputR [] (InputId 0)) (LetR 100000005 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000004 (AddR (InputR [] (InputId 1)) (LetR 100000003 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000002 (AddR (InputR [] (InputId 2)) (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 3)))))))))))))"

rankedListSum22r :: (RankedTensor ranked, GoodScalar r)
                 => [ranked r 0] -> ranked r 0
rankedListSum22r = foldr1 (\x y -> 2 * x + 2 * y)

testListSum22rPP :: Assertion
testListSum22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum22r
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x8 = 2.0 * x7 ; x9 = 2.0 * x8 in [2.0 * x7, 2.0 * x8, 2.0 * x9, 2.0 * x9]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> 2.0 * x1 + 2.0 * (2.0 * x2 + 2.0 * (2.0 * x3 + 2.0 * x4))"
  show deltas
    @?= "LetR 100000009 (AddR (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0)))) (LetR 100000008 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000007 (AddR (LetR 100000002 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 1)))) (LetR 100000006 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000005 (AddR (LetR 100000003 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 2)))) (LetR 100000004 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 3)))))))))))))"

-- Note how this rlet did not change anything, in particular the sharing.
rankedListSumk22r :: (RankedTensor ranked, GoodScalar r)
                 => [ranked r 0] -> ranked r 0
rankedListSumk22r = foldr1 (\x y -> rlet 2 (\k -> k * x + k * y))

testListSumk22rPP :: Assertion
testListSumk22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSumk22r
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x8 = 2.0 * x7 ; x9 = 2.0 * x8 in [2.0 * x7, 2.0 * x8, 2.0 * x9, 2.0 * x9]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> 2.0 * x1 + 2.0 * (2.0 * x2 + 2.0 * (2.0 * x3 + 2.0 * x4))"
  show deltas
    @?= "LetR 100000009 (AddR (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0)))) (LetR 100000008 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000007 (AddR (LetR 100000002 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 1)))) (LetR 100000006 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000005 (AddR (LetR 100000003 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 2)))) (LetR 100000004 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 3)))))))))))))"

rankedListSum2xpyr :: (RankedTensor ranked, GoodScalar r)
                   => [ranked r 0] -> ranked r 0
rankedListSum2xpyr = foldr1 (\x y -> 2 * (x + y))

testListSum2xpyrPP :: Assertion
testListSum2xpyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum2xpyr
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x8 x1 x2 x3 x4 -> let x9 = 2.0 * x8 ; x10 = 2.0 * x9 ; x11 = 2.0 * x10 in [x9, x10, x11, x11]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> 2.0 * (x1 + 2.0 * (x2 + 2.0 * (x3 + x4)))"
  show deltas
    @?= "LetR 100000006 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000005 (AddR (InputR [] (InputId 0)) (LetR 100000004 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000003 (AddR (InputR [] (InputId 1)) (LetR 100000002 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000001 (AddR (InputR [] (InputId 2)) (InputR [] (InputId 3)))))))))))))"

rankedListSum2xyr :: (RankedTensor ranked, GoodScalar r)
                  => [ranked r 0] -> ranked r 0
rankedListSum2xyr = foldr1 (\x y -> 2 * (x * y))

testListSum2xyrPP :: Assertion
testListSum2xyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum2xyr
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x10 x1 x2 x3 x4 -> let x6 = 2.0 * (x3 * x4) ; x11 = 2.0 * x10 ; x12 = 2.0 * (x1 * x11) ; x13 = 2.0 * (x2 * x12) in [(2.0 * (x2 * x6)) * x11, x6 * x12, x4 * x13, x3 * x13]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> 2.0 * (x1 * (2.0 * (x2 * (2.0 * (x3 * x4)))))"
  show deltas
    @?= "LetR 100000006 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000005 (AddR (ScaleR (AstVar [] (AstVarId 100000008)) (InputR [] (InputId 0))) (ScaleR (AstVar [] (AstVarId 100000001)) (LetR 100000004 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000003 (AddR (ScaleR (AstVar [] (AstVarId 100000006)) (InputR [] (InputId 1))) (ScaleR (AstVar [] (AstVarId 100000002)) (LetR 100000002 (ScaleR (AstConst (fromList [] [2.0])) (LetR 100000001 (AddR (ScaleR (AstVar [] (AstVarId 100000004)) (InputR [] (InputId 2))) (ScaleR (AstVar [] (AstVarId 100000003)) (InputR [] (InputId 3))))))))))))))))"

ranked2xy :: (RankedTensor ranked, GoodScalar r)
          => (ranked r 0, ranked r 0) -> ranked r 0
ranked2xy = \(x, y) -> 2 * x * y

test2xyPP :: Assertion
test2xyPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstRanked FullSpan Double 0, AstRanked FullSpan Double 0)
         -> AstRanked FullSpan Double 0
      fT = ranked2xy
  let (artifactRev, deltas)= revArtifactAdapt True fT (4, 5)
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x4 x1 x2 -> [2.0 * (x2 * x4), (2.0 * x1) * x4]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 -> (2.0 * x1) * x2"
  show deltas
    @?= "LetR 100000002 (AddR (ScaleR (AstVar [] (AstVarId 100000002)) (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0))))) (ScaleR (AstVar [] (AstVarId 100000003)) (InputR [] (InputId 1))))"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum23r :: (RankedTensor ranked, GoodScalar r)
                 => [ranked r 0] -> ranked r 0
rankedListSum23r = foldr1 (\x y -> 2 * x + 3 * y)

testListSum23rPP :: Assertion
testListSum23rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum23r
  let (artifactRev, deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x7 x1 x2 x3 x4 -> let x8 = 3.0 * x7 ; x9 = 3.0 * x8 in [2.0 * x7, 2.0 * x8, 2.0 * x9, 3.0 * x9]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 x3 x4 -> 2.0 * x1 + 3.0 * (2.0 * x2 + 3.0 * (2.0 * x3 + 3.0 * x4))"
  show deltas
    @?= "LetR 100000009 (AddR (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0)))) (LetR 100000008 (ScaleR (AstConst (fromList [] [3.0])) (LetR 100000007 (AddR (LetR 100000002 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 1)))) (LetR 100000006 (ScaleR (AstConst (fromList [] [3.0])) (LetR 100000005 (AddR (LetR 100000003 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 2)))) (LetR 100000004 (ScaleR (AstConst (fromList [] [3.0])) (InputR [] (InputId 3)))))))))))))"

ranked23 :: (RankedTensor ranked, GoodScalar r)
         => (ranked r 0, ranked r 0) -> ranked r 0
ranked23 = \(x, y) -> 2 * x + 3 * y

test23PP :: Assertion
test23PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstRanked FullSpan Double 0, AstRanked FullSpan Double 0)
         -> AstRanked FullSpan Double 0
      fT = ranked23
  let (artifactRev, deltas)= revArtifactAdapt True fT (4, 5)
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x3 x1 x2 -> [2.0 * x3, 3.0 * x3]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x1 x2 -> 2.0 * x1 + 3.0 * x2"
  show deltas
    @?= "LetR 100000003 (AddR (LetR 100000001 (ScaleR (AstConst (fromList [] [2.0])) (InputR [] (InputId 0)))) (LetR 100000002 (ScaleR (AstConst (fromList [] [3.0])) (InputR [] (InputId 1)))))"

reluPrimal
  :: forall ranked n r.
     (ADReady ranked, GoodScalar r, KnownNat n, Differentiable r)
  => ranked r n -> ranked r n
reluPrimal v =
  let oneIfGtZero = rmap0N (\x -> ifF (x <=. 0) 0.0 1.0)
                           (rprimalPart v)
  in scale oneIfGtZero v

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = reluPrimal
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifactRev
    @?= "\\m8 m1 -> let m7 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) in [m7 * m8]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 -> let m7 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) in m7 * m1"
  show deltas
    @?= "LetR 100000003 (ScaleR (AstVar [3,4] (AstVarId 100000007)) (InputR [3,4] (InputId 0)))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = reluPrimal (t * rreplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rconstant (rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i2] -> [ifF (rprimalPart v1 ! [i2] * 7.0 <=. 0.0) 0 1])) * (v1 * rreplicate 5 (rconstant 7.0))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifactRev
    @?= "\\v8 v1 x2 -> let v6 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i4] -> [ifF ((let x5 = v1 ! [i4] in x5 * x2) <=. 0.0) 0 1]) ; v7 = v1 * rreplicate 5 x2 ; v9 = v6 * v8 in [rreplicate 5 x2 * v9, rsum (v1 * v9)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\v1 x2 -> let v6 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i4] -> [ifF ((let x5 = v1 ! [i4] in x5 * x2) <=. 0.0) 0 1]) ; v7 = v1 * rreplicate 5 x2 in v6 * v7"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v8 v1 x2 -> let v9 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i4] -> [ifF (v1 ! [i4] * x2 <=. 0.0) 0 1]) * v8 in [rreplicate 5 x2 * v9, rsum (v1 * v9)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v1 x2 -> rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i4] -> [ifF (v1 ! [i4] * x2 <=. 0.0) 0 1]) * (v1 * rreplicate 5 x2)"
  show deltas
    @?= "LetR 100000009 (ScaleR (AstVar [5] (AstVarId 100000006)) (LetR 100000008 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000002))) (InputR [5] (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000001)) (LetR 100000007 (ReplicateR 5 (InputR [] (InputId 1))))))))"

testReluSimpler :: Assertion
testReluSimpler = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 relu (rfromList0N [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluSimplerPP :: Assertion
testReluSimplerPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = relu
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifactRev
    @?= "\\m8 m1 -> let m7 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) in [m7 * m8]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 -> let m7 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) in m7 * m1"
  show deltas
    @?= "LetR 100000003 (ScaleR (AstVar [3,4] (AstVarId 100000007)) (InputR [3,4] (InputId 0)))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = relu (t * rreplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rlet (v1 * rreplicate 5 (rconstant 7.0)) (\\i2 -> rconstant (rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i3] -> [ifF (rprimalPart i2 ! [i3] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifactRev
    @?= "\\v8 v1 x2 -> let v5 = v1 * rreplicate 5 x2 ; v7 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i6] -> [ifF (v5 ! [i6] <=. 0.0) 0 1]) ; v9 = v7 * v8 in [rreplicate 5 x2 * v9, rsum (v1 * v9)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\v1 x2 -> let v5 = v1 * rreplicate 5 x2 ; v7 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i6] -> [ifF (v5 ! [i6] <=. 0.0) 0 1]) in v7 * v5"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v8 v1 x2 -> let v9 = rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i6] -> [ifF (v1 ! [i6] * x2 <=. 0.0) 0 1]) * v8 in [rreplicate 5 x2 * v9, rsum (v1 * v9)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v1 x2 -> let v5 = v1 * rreplicate 5 x2 in rgather [5] (rconst (fromList [2] [0.0,1.0])) (\\[i6] -> [ifF (v5 ! [i6] <=. 0.0) 0 1]) * v5"
  show deltas
    @?= "LetR 100000008 (ScaleR (AstVar [5] (AstVarId 100000007)) (LetR 100000005 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000002))) (InputR [5] (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000001)) (LetR 100000004 (ReplicateR 5 (InputR [] (InputId 1))))))))"

testReluSimplerPP3 :: Assertion
testReluSimplerPP3 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
      (var3, ast3) = funToAstR [3, 4] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rlet (v1 * rreplicate 3 (rreplicate 4 (rconstant 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OR.constant [3, 4] 128, 42)
  printGradient6Pretty renames artifactRev
    @?= "\\m11 m1 x2 -> let m7 = m1 * rreplicate 3 (rreplicate 4 x2) ; m10 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (m7 ! [i8, i9] <=. 0.0) 0 1]) ; m12 = m10 * m11 in [rreplicate 3 (rreplicate 4 x2) * m12, rsum (rsum (m1 * m12))]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 x2 -> let m7 = m1 * rreplicate 3 (rreplicate 4 x2) ; m10 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (m7 ! [i8, i9] <=. 0.0) 0 1]) in m10 * m7"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m11 m1 x2 -> let m12 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (m1 ! [i8, i9] * x2 <=. 0.0) 0 1]) * m11 in [rreplicate 3 (rreplicate 4 x2) * m12, rsum (rsum (m1 * m12))]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 x2 -> let m7 = m1 * rreplicate 3 (rreplicate 4 x2) in rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (m7 ! [i8, i9] <=. 0.0) 0 1]) * m7"
  show deltas
    @?= "LetR 100000014 (ScaleR (AstVar [3,4] (AstVarId 100000010)) (LetR 100000011 (AddR (ScaleR (AstReplicate 3 (AstReplicate 4 (AstVar [] (AstVarId 100000002)))) (InputR [3,4] (InputId 0))) (ScaleR (AstVar [3,4] (AstVarId 100000001)) (LetR 100000010 (ReplicateR 3 (LetR 100000009 (ReplicateR 4 (InputR [] (InputId 1))))))))))"

testReluSimpler3 :: Assertion
testReluSimpler3 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

testReluSimplerPP4 :: Assertion
testReluSimplerPP4 = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
      (var3, ast3) = funToAstR [3, 4] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rlet (v1 * rreshape [3,4] (rreplicate 12 (rconstant 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OR.constant [3, 4] 128, 42)
  printGradient6Pretty renames artifactRev
    @?= "\\m12 m1 x2 -> let m7 = rreshape [3,4] (rreplicate 12 x2) ; m8 = m1 * m7 ; m11 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i9, i10] -> [ifF (m8 ! [i9, i10] <=. 0.0) 0 1]) ; m13 = m11 * m12 in [m7 * m13, rsum (rreshape [12] (m1 * m13))]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 x2 -> let m7 = rreshape [3,4] (rreplicate 12 x2) ; m8 = m1 * m7 ; m11 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i9, i10] -> [ifF (m8 ! [i9, i10] <=. 0.0) 0 1]) in m11 * m8"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m12 m1 x2 -> let m13 = rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i9, i10] -> [ifF (m1 ! [i9, i10] * x2 <=. 0.0) 0 1]) * m12 in [rreplicate 3 (rreplicate 4 x2) * m13, rsum (rreshape [12] (m1 * m13))]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 x2 -> let m8 = m1 * rreplicate 3 (rreplicate 4 x2) in rgather [3,4] (rconst (fromList [2] [0.0,1.0])) (\\[i9, i10] -> [ifF (m8 ! [i9, i10] <=. 0.0) 0 1]) * m8"
  show deltas
    @?= "LetR 100000006 (ScaleR (AstVar [3,4] (AstVarId 100000011)) (LetR 100000003 (AddR (ScaleR (AstVar [3,4] (AstVarId 100000007)) (InputR [3,4] (InputId 0))) (ScaleR (AstVar [3,4] (AstVarId 100000001)) (LetR 100000002 (ReshapeR [3,4] (LetR 100000001 (ReplicateR 12 (InputR [] (InputId 1))))))))))"

testReluSimpler4 :: Assertion
testReluSimpler4 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

testReluSimplerPP4S :: Assertion
testReluSimplerPP4S = do
  resetVarCounter
  let renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstShaped FullSpan Float '[3, 4], AstShaped FullSpan Float '[])
             -> AstShaped FullSpan Float '[3, 4]
      reluT2 (t, r) = reluS (t * sreplicate0N r)
      (var3, ast3) = funToAstS (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarNameS renamesNull var3
       ++ " -> " ++ printAstSimpleS renamesNull ast3
    @?= "\\v1 -> slet (v1 * sreshape (sreplicate (sconstant 7.0))) (\\i2 -> sconstant (sgather (sreplicate (sconst @[2] (fromList @[2] [0.0,1.0]))) (\\[i5, i4] -> [i5, ifF (sprimalPart i2 !$ [i5, i4] <=. 0.0) 0 1])) * i2)"

testReluSimplerPP4S2 :: Assertion
testReluSimplerPP4S2 = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      reluT2 :: (AstShaped FullSpan Double '[3, 4], AstShaped FullSpan Double '[])
             -> AstShaped FullSpan Double '[3, 4]
      -- This is tweaked compared to above to avoid test artifacts coming
      -- from counter resets, which are inherently unsafe (cse, etc.).
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OS.constant 128, 42)
  printGradient6PrettyS renames artifactRev
    @?= "\\m12 m1 x2 -> let m6 = sreshape (sreplicate x2) ; m7 = m1 * m6 ; m11 = sgather (sreplicate (sconst @[2] (fromList @[2] [0.0,1.0]))) (\\[i8, i9] -> [i8, ifF (m7 !$ [i8, i9] <=. 0.0) 0 1]) ; m13 = m11 * m12 in [m6 * m13, ssum (sreshape (m1 * m13))]"
  printPrimal6PrettyS renames artifactRev
    @?= "\\m1 x2 -> let m6 = sreshape (sreplicate x2) ; m7 = m1 * m6 ; m11 = sgather (sreplicate (sconst @[2] (fromList @[2] [0.0,1.0]))) (\\[i8, i9] -> [i8, ifF (m7 !$ [i8, i9] <=. 0.0) 0 1]) in m11 * m7"
  printGradient6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\m12 m1 x2 -> let m6 = sreshape (sreplicate x2) ; m13 = sgather (sreplicate (sconst @[2] (fromList @[2] [0.0,1.0]))) (\\[i8, i9] -> [i8, ifF (m1 !$ [i8, i9] * m6 !$ [i8, i9] <=. 0.0) 0 1]) * m12 in [m6 * m13, ssum (sreshape (m1 * m13))]"
  printPrimal6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\m1 x2 -> let m7 = m1 * sreshape (sreplicate x2) in sgather (sreplicate (sconst @[2] (fromList @[2] [0.0,1.0]))) (\\[i8, i9] -> [i8, ifF (m7 !$ [i8, i9] <=. 0.0) 0 1]) * m7"
  show deltas
    @?= "LetS 100000007 (ScaleS (AstVarS (AstVarId 100000011)) (LetS 100000003 (AddS (ScaleS (AstVarS (AstVarId 100000006)) (InputS (InputId 0))) (ScaleS (AstVarS (AstVarId 100000001)) (LetS 100000002 (ReshapeS (LetS 100000001 (ReplicateS (InputS (InputId 1))))))))))"

testReluSimpler4S :: Assertion
testReluSimpler4S = do
  let reluT2 :: (AstShaped FullSpan Double '[3, 4], AstShaped FullSpan Double '[])
             -> AstShaped FullSpan Double '[3, 4]
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OS.fromList @'[3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @'[3, 4] reluT2 (Flip $ OS.fromList @'[3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

reluMax :: forall ranked n r. (ADReady ranked, GoodScalar r, KnownNat n)
        => ranked r n -> ranked r n
reluMax = rmap0N (maxF 0)

testReluMax :: Assertion
testReluMax = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 reluMax (rfromList0N [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluMaxPP :: Assertion
testReluMaxPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = reluMax
      (var3, ast3) = funToAstR [3, 4] reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rgather [3,4] (rfromList [rconstant (rreplicate 3 (rreplicate 4 0.0)), m1]) (\\[i5, i4] -> [ifF (0.0 >=. rprimalPart m1 ! [i5, i4]) 0 1, i5, i4])"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (Flip $ OR.constant [3, 4] 4)
  printGradient6Pretty renames artifactRev
    @?= "\\m8 m1 -> let t11 = rscatter [2,3,4] m8 (\\[i9, i10] -> [ifF (0.0 >=. m1 ! [i9, i10]) 0 1, i9, i10]) in [t11 ! [1]]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 -> rgather [3,4] (rfromList [rreplicate 3 (rreplicate 4 0.0), m1]) (\\[i6, i7] -> [ifF (0.0 >=. m1 ! [i6, i7]) 0 1, i6, i7])"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m8 m1 -> [rscatter [2,3,4] m8 (\\[i9, i10] -> [ifF (0.0 >=. m1 ! [i9, i10]) 0 1, i9, i10]) ! [1]]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 -> rgather [3,4] (rfromList [rreplicate 3 (rreplicate 4 0.0), m1]) (\\[i6, i7] -> [ifF (0.0 >=. m1 ! [i6, i7]) 0 1, i6, i7])"
  show deltas
    @?= "LetR 100000005 (GatherR [3,4] (LetR 100000003 (FromListR [ZeroR [3,4],InputR [3,4] (InputId 0)])) <function>)"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = reluMax (t * rreplicate 5 r)
      (var3, ast3) = funToAstR [5] (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rgather [5] (rfromList [rconstant (rreplicate 5 0.0), v1 * rreplicate 5 (rconstant 7.0)]) (\\[i3] -> [ifF (0.0 >=. rprimalPart v1 ! [i3] * 7.0) 0 1, i3])"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT2 (Flip $ OR.constant [5] 128, 42)
  printGradient6Pretty renames artifactRev
    @?= "\\v7 v1 x2 -> let m10 = rscatter [2,5] v7 (\\[i8] -> [ifF (0.0 >=. (let x9 = v1 ! [i8] in x9 * x2)) 0 1, i8]) ; v11 = m10 ! [1] in [rreplicate 5 x2 * v11, rsum (v1 * v11)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\v1 x2 -> rgather [5] (rfromList [rreplicate 5 0.0, v1 * rreplicate 5 x2]) (\\[i5] -> [ifF (0.0 >=. (let x6 = v1 ! [i5] in x6 * x2)) 0 1, i5])"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v7 v1 x2 -> let v11 = rscatter [2,5] v7 (\\[i8] -> [ifF (0.0 >=. v1 ! [i8] * x2) 0 1, i8]) ! [1] in [rreplicate 5 x2 * v11, rsum (v1 * v11)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v1 x2 -> rgather [5] (rfromList [rreplicate 5 0.0, v1 * rreplicate 5 x2]) (\\[i5] -> [ifF (0.0 >=. v1 ! [i5] * x2) 0 1, i5])"
  show deltas
    @?= "LetR 100000013 (GatherR [5] (LetR 100000010 (FromListR [ZeroR [5],LetR 100000009 (AddR (ScaleR (AstReplicate 5 (AstVar [] (AstVarId 100000002))) (InputR [5] (InputId 0))) (ScaleR (AstVar [5] (AstVarId 100000001)) (LetR 100000008 (ReplicateR 5 (InputR [] (InputId 1))))))])) <function>)"

testReluMax3 :: Assertion
testReluMax3 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = reluMax (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( Flip
      $ OR.fromList [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , 57.1 )
    (rev @Double @2 reluT2 (Flip $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], 7))

testDot1PP :: Assertion
testDot1PP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt True (uncurry (rdot0 @(AstRanked FullSpan) @Double @1))
                 ( Flip $ OR.fromList [3] [1 .. 3]
                 , Flip $ OR.fromList [3] [4 .. 6] )
  printGradient6Pretty renames artifactRev
    @?= "\\x3 v1 v2 -> [v2 * rreplicate 3 x3, v1 * rreplicate 3 x3]"
  printPrimal6Pretty renames artifactRev
    @?= "\\v1 v2 -> rsum (v1 * v2)"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      (artifactRev, deltas) =
        revArtifactAdapt True (uncurry (rdot0 @(AstRanked FullSpan) @Double @2))
                 ( Flip $ OR.fromList [2,3] [1 .. 6]
                 , Flip $ OR.fromList [2,3] [7 .. 12] )
  printGradient6Pretty renames artifactRev
    @?= "\\x3 m1 m2 -> [m2 * rreshape [2,3] (rreplicate 6 x3), m1 * rreshape [2,3] (rreplicate 6 x3)]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 m2 -> rsum (rreshape [6] (m1 * m2))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\x3 m1 m2 -> [m2 * rreplicate 2 (rreplicate 3 x3), m1 * rreplicate 2 (rreplicate 3 x3)]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 m2 -> rsum (rreshape [6] (m1 * m2))"
  show deltas
    @?= "LetR 100000001 (AddR (Dot0R (AstVar [2,3] (AstVarId 100000002)) (InputR [2,3] (InputId 0))) (Dot0R (AstVar [2,3] (AstVarId 100000001)) (InputR [2,3] (InputId 1))))"

testMatvecmulPP :: Assertion
testMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True (uncurry rmatvecmul)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3] [7 .. 9] )
  printGradient6Pretty renames artifactRev
    @?= "\\v4 m1 v2 -> [rreplicate 2 v2 * rtranspose [1,0] (rreplicate 3 v4), rsum (m1 * rtranspose [1,0] (rreplicate 3 v4))]"
  printPrimal6Pretty renames artifactRev
    @?= "\\m1 v2 -> rsum (rtranspose [1,0] (rreplicate 2 v2 * m1))"
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\v4 m1 v2 -> [rreplicate 2 v2 * rtranspose [1,0] (rreplicate 3 v4), rsum (m1 * rtranspose [1,0] (rreplicate 3 v4))]"
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= "\\m1 v2 -> rsum (rtranspose [1,0] (rreplicate 2 v2 * m1))"

-- The results in the three following tests are the same and the extra
-- post factum simplification doesn't change the terms.
sGradient6Pretty, sPrimal6Pretty :: String
sGradient6Pretty = "\\m3 m1 m2 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m2) * rtranspose [2,1,0] (rreplicate 3 m3)), rsum (rtranspose [1,2,0] (rreplicate 4 m1) * rtranspose [1,0] (rreplicate 3 m3))]"
sPrimal6Pretty = "\\m1 m2 -> rsum (rtranspose [2,1,0] (rreplicate 4 m1) * rtranspose [1,0] (rreplicate 2 m2))"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt @Double @2 @(AstRanked FullSpan)
                 True (uncurry rmatmul2)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3,4] [7 .. 18] )
  printGradient6Pretty renames artifactRev
    @?= sGradient6Pretty
  printPrimal6Pretty renames artifactRev
    @?= sPrimal6Pretty
  printGradient6Pretty renames (simplifyArtifactRev artifactRev)
    @?= sGradient6Pretty
  printPrimal6Pretty renames (simplifyArtifactRev artifactRev)
    @?= sPrimal6Pretty

testMatmul2FromMatvecmulPP :: Assertion
testMatmul2FromMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2F :: (RankedTensor ranked, GoodScalar r)
                => ranked r 2 -> ranked r 2 -> ranked r 2
      rmatmul2F m1 m2 =
        rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
      (artifactRev, _) =
        revArtifactAdapt @Double @2 @(AstRanked FullSpan)
                 True (uncurry rmatmul2F)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3,4] [7 .. 18] )
  printGradient6Pretty renames artifactRev
    @?= "\\m5 m1 m2 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m2) * rtranspose [2,1,0] (rreplicate 3 m5)), rsum (rtranspose [1,2,0] (rreplicate 4 m1) * rtranspose [1,0] (rreplicate 3 m5))]"
  printPrimal6Pretty renames artifactRev
    @?= sPrimal6Pretty

testMatmul2PaperPP :: Assertion
testMatmul2PaperPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2P :: (RankedTensor ranked, GoodScalar r)
                => ranked r 2 -> ranked r 2 -> ranked r 2
      rmatmul2P a b =
        let k :$ m :$ _ = rshape a
            _ :$ n :$ _ = rshape b
        in rbuild1 k (\i ->
             rbuild1 n (\j ->
               rsum (rbuild1 m (\p -> a ! [i, p] * b ! [p, j]))))
      (artifactRev, _) =
        revArtifactAdapt @Double @2 @(AstRanked FullSpan)
                 True (uncurry rmatmul2P)
                 ( Flip $ OR.fromList [2,3] [1 :: Double .. 6]
                 , Flip $ OR.fromList [3,4] [7 .. 18] )
  printGradient6Pretty renames artifactRev
    @?= "\\m7 m1 m2 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m2) * rtranspose [2,1,0] (rreplicate 3 m7)), rsum (rtranspose [1,2,0] (rreplicate 4 m1) * rtranspose [1,0] (rreplicate 3 m7))]"
  printPrimal6Pretty renames artifactRev
    @?= sPrimal6Pretty

testMatmul2PPS :: Assertion
testMatmul2PPS = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt @Double @[2, 4] @(AstShaped FullSpan)
                 True (uncurry smatmul2)
                 ( Flip $ OS.fromList @'[2,3] [1 :: Double .. 6]
                 , Flip $ OS.fromList @'[3,4] [7 .. 18] )
  printGradient6PrettyS renames artifactRev
    @?= "\\m3 m1 m2 -> [ssum (stranspose (stranspose (sreplicate m2) * sreplicate m3)), ssum (stranspose (stranspose (sreplicate m1) * sreplicate m3))]"
  printPrimal6PrettyS renames artifactRev
    @?= "\\m1 m2 -> ssum (stranspose (sreplicate m1) * stranspose (sreplicate m2))"
  printGradient6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\m3 m1 m2 -> [ssum (stranspose (stranspose (sreplicate m2) * sreplicate m3)), ssum (stranspose (stranspose (sreplicate m1) * sreplicate m3))]"
  printPrimal6PrettyS renames (simplifyArtifactRevS artifactRev)
    @?= "\\m1 m2 -> ssum (stranspose (sreplicate m1) * stranspose (sreplicate m2))"

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

testBar2S :: Assertion
testBar2S =
  assertEqualUpToEpsilon 1e-9
    (3.1435239435581166,-1.1053869545195814)
    (rev (bar @(AstShaped FullSpan Double '[52, 2, 2, 1, 1, 3])) (1.1, 2.2))

testBarCFwd :: Assertion
testBarCFwd =
  assertEqualUpToEpsilon 1e-9
    9.327500345189534e-2
    (cfwd (bar @(ADVal (Flip OR.Array) Double 0)) (1.1, 2.2) (0.1, 0.2))

testBarFwd :: Assertion
testBarFwd =
  assertEqualUpToEpsilon 1e-9
    9.327500345189534e-2
    (fwd @Double @0 @(AstRanked FullSpan) bar (1.1, 2.2) (0.1, 0.2))

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

fooBuild1 :: (ADReady ranked, GoodScalar r, Differentiable r)
          => ranked r 1 -> ranked r 1
fooBuild1 v =
  let r = rsum0 v
      v' = rminimum v
  in rbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * rminimum v * v')
       + bar (r, rindex v [ix + 1])

testFooBuildDt :: Assertion
testFooBuildDt =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [4] [-189890.46351219364,-233886.08744601303,-222532.22669716467,-206108.68889329425])
    (revDt @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]) (Flip $ OR.constant [3] 42))

testFooBuildCFwd :: Assertion
testFooBuildCFwd =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (cfwd @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]) (Flip $ OR.constant [4] 42))

testFooBuildFwd :: Assertion
testFooBuildFwd =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (fwd @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]) (Flip $ OR.constant [4] 42))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @Double @1 fooBuild1 (Flip $ OR.fromList [4] [1.1, 2.2, 3.3, 4]))

fooMap1 :: (ADReady ranked, GoodScalar r, Differentiable r)
        => ranked r 0 -> ranked r 1
fooMap1 r =
  let v = fooBuild1 $ rreplicate0N [130] r
  in rmap0N (\x -> x * r + 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-3
    4.438131773975095e7
    (rev' @Double @1 fooMap1 1.1)

barAst :: (Numeric r, Show r, RealFloat r, RealFloat (Vector r))
       => (AstRanked PrimalSpan r 0, AstRanked PrimalSpan r 0) -> AstRanked PrimalSpan r 0
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. (GoodScalar r, Differentiable r)
           => AstRanked PrimalSpan r 1 -> AstRanked PrimalSpan r 1
fooNoGoAst v =
  let r = rsum0 v
  in rbuild1 3 (\ix ->
       barAst (3.14, bar (3.14, rindex v [(ix + (rprimalPart . rfloor) r) `minF` 2 `maxF` 0]))
       + ifF ( (&&*)
                    (rindex v (ix * 2 :. ZI) <=. 0)
                        -- @1 not required thanks to :.; see below for @ and []
                    (6 >. abs ix) )
                 r (5 * r))
     / rslice 1 3 (rmap0N (\x -> ifF (x >. r) r x) v)
     * rbuild1 3 (const 1)

testFooNoGoAst :: Assertion
testFooNoGoAst =
  let f :: (GoodScalar r, Differentiable r)
        => ADVal (Flip OR.Array) r 1 -> ADVal (Flip OR.Array) r 1
      f x = interpretAst (extendEnvR
                            (AstVarName $ intToAstVarId 100000000)
                            x EM.empty)
                         (fooNoGoAst (AstVar [5] (AstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (crev @Double @1 f
             (Flip $ OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

fooNoGo :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
        => ranked r 1 -> ranked r 1
fooNoGo v =
  let r = rsum0 v
  in rbuild1 3 (\ix ->
       bar (3.14, bar (3.14, rindex v [(ix + (rprimalPart . rfloor) r) `minF` 2 `maxF` 0]))
       + ifF ((&&*) (rindex @ranked @r @1 v [ix * 2] <=. 0)
                    (6 >. abs ix))
               r (5 * r))
     / rslice 1 3 (rmap0N (\x -> ifF (x >. r) r x) v)
     * rbuild1 3 (const 1)

testFooNoGo :: Assertion
testFooNoGo =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
   (rev' @Double @1 fooNoGo
         (Flip $ OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall ranked r.
                  (ADReady ranked, GoodScalar r, Differentiable r)
               => ranked r 0 -> ranked r 1
nestedBuildMap r =
  let w = rreplicate0N @ranked [4]
      v0' = rreplicate0N [177] r :: ranked r 1
  in rlet v0' $ \v' ->
    let nestedMap x0 = rlet x0 $ \x -> rmap0N (x /) (w x)
        variableLengthBuild iy = rbuild1 7 (\ix -> rindex v' (ix + iy :. ZI))
        doublyBuild = rbuild1 5 (rminimum . variableLengthBuild)
    in rmap0N (\x0 -> rlet x0 $ \x -> x * rsum0
                           (rbuild1 3 (\ix -> bar (x, rindex v' [ix]))
                            + (rlet (nestedMap x) $ \x3 -> fooBuild1 x3)
                            / (rlet x $ \x4 -> fooMap1 x4))
              ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @Double @1 nestedBuildMap 1.1)

nestedSumBuild :: (ADReady ranked, GoodScalar r, Differentiable r)
               => ranked r 1 -> ranked r 1
nestedSumBuild v0 = rlet v0 $ \v ->
 rlet (rsum (rbuild1 9 rfromIndex0)) (\tbtf ->
  (rbuild1 13 (\ix ->
    rsum (rbuild1 4 (\ix2 ->
      flip rindex [ix2]
        (rlet (rsum v) $ \tsumv -> rbuild1 5 (const tsumv)
         * rfromList
             [ rfromIndex0 ix
             , tbtf
             , rsum (rbuild1 6 (\_ -> rsum v))
             , rindex v [ix2]
             , rsum (rbuild1 3 (\ix7 ->
                 rsum (rreplicate 5 (rfromIndex0 ix7))))
             ]))))))
 + rlet (nestedBuildMap (rsum0 v)) (\nbmt -> (rbuild1 13 (\ix ->
     nbmt `rindex` [minF ix 4])))

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @Double @1 nestedSumBuild (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall ranked r. (ADReady ranked, GoodScalar r)
                 => ranked r 1 -> ranked r 1
nestedBuildIndex v =
  rbuild1 2 $ \ix2 -> rindex (rbuild1 3 $ \ix3 -> rindex (rbuild1 4 $ \ix4 -> rindex v (ix4 :. ZI)) [ix3]) (ix2 :. ZI)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @Double @1 nestedBuildIndex (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( ADReady ranked, GoodScalar r, KnownNat n, Differentiable r )
  => ranked r n -> ranked r n
barRelu x = relu $ bar (x, relu x)

testBarReluDt :: Assertion
testBarReluDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 @(AstRanked FullSpan) barRelu (Flip $ OR.fromList [] [1.1]) 42.2)

testBarRelu :: Assertion
testBarRelu =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barRelu (Flip $ OR.fromList [] [1.1]))

testBarRelu3 :: Assertion
testBarRelu3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barRelu (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluMax
  :: ( ADReady ranked, GoodScalar r, KnownNat n, RealFloat (ranked r n) )
  => ranked r n -> ranked r n
barReluMax x = reluMax $ bar (x, reluMax x)

testBarReluMaxDt :: Assertion
testBarReluMaxDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @Double @0 @(AstRanked FullSpan) barReluMax (Flip $ OR.fromList [] [1.1]) 42.2)

testBarReluMax :: Assertion
testBarReluMax =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barReluMax (Flip $ OR.fromList [] [1.1]))

testBarReluMax3 :: Assertion
testBarReluMax3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barReluMax (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

testBarReluMax3CFwd :: Assertion
testBarReluMax3CFwd =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (cfwd @Double @3 barReluMax
                     (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2])
                     (Flip $ OR.fromList [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

reluMaxS :: forall shaped sh r.
            (ADReadyS shaped, GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => shaped r sh -> shaped r sh
reluMaxS = smap0N (maxF 0)

barReluMaxS
  :: ( ADReadyS shaped, GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh)
     , RealFloat (shaped r sh) )
  => shaped r sh -> shaped r sh
barReluMaxS x = reluMaxS $ bar (x, reluMaxS x)

-- Previously the shape of FromListR[ZeroR] couldn't be determined
-- in buildDerivative, so this was needed. See below that it now works fine.
testBarReluMax3FwdS :: Assertion
testBarReluMax3FwdS =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @Double @'[2, 1, 2]
         barReluMaxS
         (Flip $ OS.fromList @'[2, 1, 2] [1.1, 2, 3, 4.2])
         (Flip $ OS.fromList @'[2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdFrom :: Assertion
testBarReluMax3FwdFrom =
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @Double @'[2, 1, 2]
         (sfromR . barReluMax . rfromS)
         (Flip $ OS.fromList @'[2, 1, 2] [1.1, 2, 3, 4.2])
         (Flip $ OS.fromList @'[2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdR :: Assertion
testBarReluMax3FwdR =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @Double @3
         barReluMax
         (Flip $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2])
         (Flip $ OR.fromList [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

barReluAst
  :: forall n r.
     ( KnownNat n, ADReady (AstRanked PrimalSpan), GoodScalar r
     , Differentiable r )
  => AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
barReluAst x = relu $ bar (x, relu x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: (GoodScalar r, Differentiable r)
        => ADVal (Flip OR.Array) r 0 -> ADVal (Flip OR.Array) r 0
      f x = interpretAst (extendEnvR
                            (AstVarName $ intToAstVarId 100000000)
                            x EM.empty)
                         (barReluAst (AstVar [] (AstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @Double @0 f (Flip $ OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: (GoodScalar r, Differentiable r)
        => ADVal (Flip OR.Array) r 1 -> ADVal (Flip OR.Array) r 1
      f x = interpretAst (extendEnvR
                            (AstVarName $ intToAstVarId 100000000)
                            x EM.empty)
                         (barReluAst (AstVar [5] (AstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @Double @1 f (Flip $ OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r.
     (ADReady (AstRanked PrimalSpan), GoodScalar r, Differentiable r)
  => AstRanked PrimalSpan r 0 -> AstRanked PrimalSpan r 0
konstReluAst x = rsum0 $ relu $ rreplicate0N (7 :$ ZS) x

testReplicateReluAst :: Assertion
testReplicateReluAst =
  let f :: (GoodScalar r, Differentiable r)
        => ADVal (Flip OR.Array) r 0 -> ADVal (Flip OR.Array) r 0
      f x = interpretAst (extendEnvR
                            (AstVarName $ intToAstVarId 100000000)
                            x EM.empty)
                         (konstReluAst (AstVar [] (AstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [295.4])
       (crevDt @Double @0 f (Flip $ OR.fromList [] [1.1]) 42.2)

f1 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 0
f1 = \arg -> rsum0 (rbuild1 10 (\i -> arg * rfromIndex0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    45.0
    (rev @Double @0 @(AstRanked FullSpan) f1 1.1)

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    45.0
    (rev' @Double @0 f1 1.1)

f2 :: forall ranked r. (ADReady ranked, GoodScalar r)
   => ranked r 0 -> ranked r 0
f2 = \arg ->
  let fun1 i = arg * rfromIndex0 i
      v1a = rsum0 (rbuild1 10 fun1)
      v1b = rsum0 (rbuild1 20 fun1)
      fun2 y i = y * rfromIndex0 @r i
      v2a = rsum0 (rbuild1 10 (fun2 arg))
      v2b = rsum0 (rbuild1 20 (fun2 (arg + 1)))
  in v1a + v1b + v2a + v2b

testF2 :: Assertion
testF2 =
  assertEqualUpToEpsilon 1e-10
    470
    (rev @Double @0 @(AstRanked FullSpan) f2 1.1)

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    470
    (rev' @Double @0 f2 1.1)

testF2CFwd :: Assertion
testF2CFwd =
  assertEqualUpToEpsilon 1e-10
    47
    (cfwd @Double @0 f2 1.1 0.1)

testF2Fwd :: Assertion
testF2Fwd =
  assertEqualUpToEpsilon 1e-10
    47
    (fwd @Double @0 @(AstRanked FullSpan) f2 1.1 0.1)

braidedBuilds :: forall ranked r.
                 (ADReady ranked, GoodScalar r, Differentiable r)
              => ranked r 0 -> ranked r 2
braidedBuilds r =
  rbuild1 3 (\ix1 ->
    rbuild1 4 (\ix2 -> rindex (rfromList0N [4]
      [rfromIndex0 ix2, 7, r, -0.2]) (ix1 :. ZI)))

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @Double @2 braidedBuilds 3.4)

recycled :: (ADReady ranked, GoodScalar r, Differentiable r)
         => ranked r 0 -> ranked r 5
recycled r =
  rlet (nestedSumBuild (rreplicate0N [7] r)) $ \nsb ->
    rbuild1 2 $ \_ -> rbuild1 4 $ \_ -> rbuild1 2 $ \_ -> rbuild1 3 $ const nsb

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilonShort 1e-6
    348356.9278600814
    (rev' @Double @5 recycled 0.0000001)

concatBuild :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 2
concatBuild r =
  rbuild1 7 (\i ->
    rappend (rappend (rbuild1 5 (const r))
                     (rreplicate 1 (rfromIndex0 i)))
            (rbuild1 13 (const r)))

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    126.0
    (rev' @Double @2 concatBuild 3.4)

emptyArgs :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
          => ranked r 1 -> ranked r 1
emptyArgs t =
  rfromList @ranked @r @0 []
  - rfromList0N (rshape @ranked @r (rfromList [])) []
  - rreshape @ranked @r @1 [0] (rfromList [])
  - rgather1 0 (rfromList []) (:. ZI)
  - rsum (rgather1 0 (rfromList []) (const ZI))
  - rsum (rgather @ranked @r @2 (0 :$ 0 :$ ZS) (rfromList []) (const (0 :. ZI)))
  - rsum (rgather @ranked @r @2 @0 @1 [0, 0] (rfromList []) (const [0]))
  - rsum (rreshape @ranked @r @1 [0, 0] (rfromList []))
  - rindex (rfromList0N (0 :$ 0 :$ ZS) []) (42 :. ZI)
  - rindex (rfromList0N (0 :$ rshape @ranked @r (rfromList [])) []) (42 :. ZI)
  - rsum (rfromList0N (0 :$ rshape @ranked @r (rfromList [])) [])
  * rsum (rfromList [rsum (rfromList0N (0 :$ rshape @ranked @r (rfromList [])) [])])
  * rflatten (rtr (rgather1 0 t (const ZI)))
  + rbuild1 0 (\i -> t ! [fromIntegral (rrank t) `quot` i] / rfromIndex0 i)
  -- - rsum (rbuild @ranked @r @2 (0 :$ 0 :$ ZS) (const 73))
  -- - rsum (rbuild @ranked @r @1 (0 :$ 0 :$ ZS) (const $ rfromList []))
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
          (\t -> rbuild [2, 5, 11, 0] (const $ emptyArgs t))
          (Flip $ OR.fromList [1] [0.24]))

-- Catastrophic loss of sharing prevented.
fblowup :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
        => Int -> ranked r 1 -> ranked r 0
fblowup k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y - rfromIndex0 0
      blowup n y =
        let ysum = y + y - rfromIndex0 0
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

fblowupLet :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
           => IntOf ranked -> Int -> ranked r 1 -> ranked r 0
fblowupLet i k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y - rfromIndex0 i
      blowup n y1 = rlet y1 $ \y ->
        let ysum = y + y - rfromIndex0 i
            yscaled = 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

-- Catastrophic loss of sharing prevented also with non-trivial multiplication.
fblowupMult :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
            => Int -> ranked r 1 -> ranked r 0
fblowupMult k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y
      blowup n y =
        let ysum = y + y * y / (y - 0.000000001)
            yscaled = sqrt $ 0.499999985 * 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 0
      y0 = (inputs ! [0 `rem` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall ranked r.
                  (ADReady ranked, GoodScalar r, Differentiable r)
               => IntOf ranked -> Int -> ranked r 1 -> ranked r 0
fblowupMultLet i k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y
      blowup n y1 = rlet y1 $ \y ->
        let ysum0 = y + y * y / (y - 0.000001)
            yscaled = rlet ysum0 $ \ysum ->
                        sqrt $ 0.499999985 * 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 i
      y0 = (inputs ! [i `rem` 2]) * (inputs ! [1])
  in blowup k y0

fblowupPP :: Assertion
fblowupPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupT = fblowup @(AstRanked FullSpan) @Double 1
  let (artifactRev, _) = revArtifactAdapt True fblowupT (Flip $ OR.constant [4] 4)
  printGradient6Simple renames artifactRev
    @?= "\\x7 v1 -> rletInHVector (v1 ! [0]) (\\x2 -> rletInHVector (v1 ! [1]) (\\x3 -> rletInHVector (v1 ! [0]) (\\x4 -> rletInHVector (v1 ! [1]) (\\x5 -> rletInHVector ((x2 / x3 + x4 / x5) - rfromIntegral 0) (\\x6 -> rletInHVector (0.499999985 * x7) (\\x8 -> dmkHVector (fromList [DynamicRanked (rscatter [4] (recip x3 * x8) (\\[] -> [0]) + rscatter [4] (negate (x2 / (x3 * x3)) * x8) (\\[] -> [1]) + rscatter [4] (recip x5 * x8) (\\[] -> [0]) + rscatter [4] (negate (x4 / (x5 * x5)) * x8) (\\[] -> [1]))])))))))"
  printPrimal6Simple renames artifactRev
    @?= "\\v1 -> rlet (v1 ! [0]) (\\x2 -> rlet (v1 ! [1]) (\\x3 -> rlet (v1 ! [0]) (\\x4 -> rlet (v1 ! [1]) (\\x5 -> rlet ((x2 / x3 + x4 / x5) - rfromIntegral 0) (\\x6 -> 0.499999985 * x6 - rfromIntegral 0)))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupLetT = fblowupLet @(AstRanked FullSpan) @Double 0 1
  let (artifactRev, _) = revArtifactAdapt True fblowupLetT (Flip $ OR.constant [4] 4)
  printGradient6Simple renames artifactRev
    @?= "\\x7 v1 -> rletInHVector (v1 ! [0]) (\\x3 -> rletInHVector (v1 ! [1]) (\\x4 -> rletInHVector (x3 / x4) (\\x5 -> rletInHVector ((x5 + x5) - rfromIntegral 0) (\\x6 -> rletInHVector (0.499999985 * x7) (\\x8 -> rletInHVector (x8 + x8) (\\x9 -> dmkHVector (fromList [DynamicRanked (rscatter [4] (recip x4 * x9) (\\[] -> [0]) + rscatter [4] (negate (x3 / (x4 * x4)) * x9) (\\[] -> [1]))])))))))"
  printPrimal6Simple renames artifactRev
    @?= "\\v1 -> rlet (v1 ! [0]) (\\x3 -> rlet (v1 ! [1]) (\\x4 -> rlet (x3 / x4) (\\x5 -> rlet ((x5 + x5) - rfromIntegral 0) (\\x6 -> 0.499999985 * x6 - rfromIntegral 0))))"

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
        (rev' @Double @0 (fblowupLet 0 1000) (Flip $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (OR.fromList [2] [33.332333348316844,-22.221555565544556])
        (rev' @Double @1
              (\intputs -> rbuild1 100 (\i -> fblowupLet i 1000 intputs))
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
              (\intputs -> rbuild1 100 (\i -> fblowupMultLet i 50 intputs))
              (Flip $ OR.fromList [2] [0.2, 0.3]))
  ]
