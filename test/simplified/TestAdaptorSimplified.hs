{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fno-cse #-}
-- | Assorted rather low rank tensor tests.
module TestAdaptorSimplified
  ( testTrees
  ) where

import Prelude

import Data.Array.RankedS qualified as OR
import Data.Int (Int64)
import Data.IntMap.Strict qualified as IM
import Data.List (foldl1')
import Data.List.NonEmpty qualified as NonEmpty
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested (Rank)
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAst, resetVarCounter)
import HordeAd.Core.DeltaFreshId (resetIdCounter)
import HordeAd.Core.TensorAst
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), IntegralF (..), RealFloatF (..))

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
  , testCase "2overleafInt64n" testOverleafInt64n
  , testCase "2overleafCIntn" testOverleafCIntn
  , testCase "2overleafCIntToFloatn" testOverleafCIntToFloatn
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
-- TODO:  , testCase "2listProdPP" testListProdPP
  , testCase "2listProdrPP" testListProdrPP
  , testCase "2listProdrLongPP" testListProdrLongPP
-- TODO  , testCase "2listProd" testListProd
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
  , testCase "2addSpeedBig" testAddSpeedBig
  , testCase "2matmul2SpeedBig" testMatmul2SpeedBig
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
  , testCase "2fooNoGo0" testFooNoGo0
  , testCase "2nestedBuildMap1" testNestedBuildMap1
  , testCase "2nestedSumBuild" testNestedSumBuild
  , testCase "2nestedBuildIndex" testNestedBuildIndex
  , testCase "2barReluDt" testBarReluDt
  , testCase "2barRelu" testBarRelu
  , testCase "2barRelu3" testBarRelu3
  , testCase "2barReluMaxDt" testBarReluMaxDt
  , testCase "2barReluMax" testBarReluMax
  , testCase "2barReluMax30" testBarReluMax30
  , testCase "2barReluMax31" testBarReluMax31
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
  , testCase "2concatBuild2" testConcatBuild2
  , testCase "2concatBuild3" testConcatBuild3
  , testCase "2concatBuild4" testConcatBuild4
  , testCase "2concatBuild5" testConcatBuild5
  , testCase "2concatBuild6" testConcatBuild6
  , testCase "2concatBuild7" testConcatBuild7
--  , testCase "2concatBuild8" testConcatBuild8
--  , testCase "2concatBuild9" testConcatBuild9
  , testCase "2concatBuild10" testConcatBuild10
  , testCase "2concatBuild11" testConcatBuild11
  , testCase "2concatBuild12" testConcatBuild12
  , testCase "2emptyArgs0" testEmptyArgs0
  , testCase "2emptyArgs1" testEmptyArgs1
  , testCase "2emptyArgs4" testEmptyArgs4
  , testCase "2filterPositiveFail" testFilterPositiveFail
  , testCase "2blowupPP" fblowupPP
  , testCase "2blowupLetPP" fblowupLetPP
  , blowupTests
  , testCase "22concatBuild3PP" testConcatBuild3PP
  , testCase "22concatBuild3PP2" testConcatBuild3PP2
  ]

testZeroZ :: Assertion
testZeroZ =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @0 [] [0])
    (rev' @Double @0 (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
                          f = const 3
                      in f) 42)

testZeroS :: Assertion
testZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (crev (let f :: ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
                 -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
               f = const (srepl 3)
           in f) (srepl 42))

testCFwdZeroS :: Assertion
testCFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f :: ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
                 -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
               f = const (srepl 3)
           in f) 42 41)

testFwdZeroS :: Assertion
testFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd (let f :: AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1])
                -> AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1])
              f = const (srepl 3)
          in f) (srepl 42) (srepl 41))

testZero2S :: Assertion
testZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[] knownShS [1])
    (crev @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42))

testCFwdZero2S :: Assertion
testCFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[] knownShS [41])
    (cfwd @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testFwdZero2S :: Assertion
testFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[] knownShS [41])
    (fwd @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testZero3S :: Assertion
testZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.6174114266850617))
    (crev (\x -> barF @(ADVal RepN (TKS Double '[33, 2])) (x, x)) (srepl 1))

testCFwdZero3S :: Assertion
testCFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (cfwd (\x -> barF @(ADVal RepN (TKS Double '[33, 2])) (x, x)) (srepl 1) (srepl 1.1))

testFwdZero3S :: Assertion
testFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (fwd (\x -> barF @(AstTensor AstMethodLet FullSpan (TKS Double '[33, 2])) (x, x)) (srepl 1) (srepl 1.1))

testZero4S :: Assertion
testZero4S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[] knownShS [0])
    (rev @(AstTensor AstMethodLet FullSpan (TKS Double '[])) @(TKS Double '[])
         (let f = const (srepl 3)
          in f) (srepl 42))

testZero5S :: Assertion
testZero5S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[44] knownShS (replicate 44 1))
    (rev (let f :: a -> a
              f = id
          in f @(AstTensor AstMethodLet FullSpan (TKS Double '[44]))) (srepl 42))

testZero6S :: Assertion
testZero6S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] knownShS (replicate (product ([2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] :: [Int])) 3.6174114266850617))
    (rev @_ @(TKS Double '[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2])
         (\x -> barF (x, x)) (srepl 1))

testZero7S :: Assertion
testZero7S =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[] knownShS [0])
    (rev (const 3 :: AstTensor AstMethodLet FullSpan (TKS Double '[]) -> AstTensor AstMethodLet FullSpan (TKR Double 0)) (srepl 42))

testZero8 :: Assertion
testZero8 =
  assertEqualUpToEpsilon 1e-10
    (rfromList0N [] [0])
    (rev (const (sscalar 3) :: AstTensor AstMethodLet FullSpan (TKR Double 0) -> AstTensor AstMethodLet FullSpan (TKS Double '[])) 42)

testZero9S :: Assertion
testZero9S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (crev (let f :: ADVal RepN (TKR Double 5)
                 -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
               f = const (srepl 3)
           in f)
          (rreplicate0N [0, 2, 4, 0, 1] 42))

testCFwdZero9S :: Assertion
testCFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f :: ADVal RepN (TKR Double 5)
                 -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1])
               f = const (srepl 3)
           in f)
          (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testFwdZero9S :: Assertion
testFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd (let f :: AstTensor AstMethodLet FullSpan (TKR Double 5)
                -> AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1])
              f = const (srepl 3)
          in f)
         (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testZero10S :: Assertion
testZero10S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (crev (let f = const (srepl 3) . snd
           in f :: ( ADVal RepN (TKR Double 5)
                   , ADVal RepN (TKS Double '[0, 2, 4, 0, 1]) )
                   -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1]))
          (rreplicate0N [0, 2, 4, 0, 1] 42, srepl 21))

testCFwdZero10S :: Assertion
testCFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f = const (srepl 3) . snd
           in f :: ( ADVal RepN (TKR Double 5)
                   , ADVal RepN (TKS Double '[0, 2, 4, 0, 1]) )
                   -> ADVal RepN (TKS Double '[0, 2, 4, 0, 1]))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero10S :: Assertion
testFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd  (let f = const (srepl 3) . snd
           in f :: ( AstTensor AstMethodLet FullSpan (TKR Double 5)
                   , AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1]) )
                   -> AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1]))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testZero11S :: Assertion
testZero11S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (crev (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal RepN (TKR Double 5)
                   , ADVal RepN (TKS Double '[0, 2, 4, 0, 1]) )
                   -> ADVal RepN (TKR Double 5))
          (rreplicate0N [0, 2, 4, 0, 1] 42, srepl 21))

testCFwdZero11S :: Assertion
testCFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (cfwd (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal RepN (TKR Double 5)
                   , ADVal RepN (TKS Double '[0, 2, 4, 0, 1]) )
                   -> ADVal RepN (TKR Double 5))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero11S :: Assertion
testFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (fwd  (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( AstTensor AstMethodLet FullSpan (TKR Double 5)
                   , AstTensor AstMethodLet FullSpan (TKS Double '[0, 2, 4, 0, 1]) )
                   -> AstTensor AstMethodLet FullSpan (TKR Double 5))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testPiecewiseLinearPP :: Assertion
testPiecewiseLinearPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: AstTensor AstMethodLet FullSpan (TKR Double 0)
         -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT x = ifF (x >. 0) (2 * x) (5 * x)
      (artifactRev, _deltas) = revArtifactAdapt True fT 42
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x2 x1 -> let v3 = rscatter [2] x2 (\\[] -> [ifF (x1 >. 0.0) 0 1]) in 2.0 * v3 ! [0] + 5.0 * v3 ! [1]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromVector (fromList [2.0 * x1, 5.0 * x1]) ! [ifF (x1 >. 0.0) 0 1]"

testPiecewiseLinear2PP :: Assertion
testPiecewiseLinear2PP = do
  resetVarCounter
  let renames = IM.empty
      fT :: AstTensor AstMethodLet FullSpan (TKR Double 0)
         -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT x = ifF (x >. 0) 2 5 * x
      (artifactRev, deltas) = revArtifactAdapt True fT 42
  printArtifactPretty renames artifactRev
    @?= "\\x3 x1 -> let x2 = ifF (x1 >. 0.0) 2.0 5.0 in x2 * x3"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let x2 = ifF (x1 >. 0.0) 2.0 5.0 in x2 * x1"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x3 x1 -> ifF (x1 >. 0.0) 2.0 5.0 * x3"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> ifF (x1 >. 0.0) 2.0 5.0 * x1"
  show deltas
    @?= "ShareG 100000005 (ScaleG (AstRaw {unAstRaw = AstShare (AstVarId 100000002) (AstCond (AstRel GtOp (AstVar (FTKR []) (AstVarId 100000001)) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [2.0])) (AstConst (rfromListLinear [] [5.0])))}) (InputG (FTKR []) (InputId 0)))"

overleaf :: forall r target. (BaseTensor target, GoodScalar r)
         => target (TKR r 1) -> target (TKR r 0)
overleaf v = let wrap i = i `remF` fromIntegral (rlength v)
             in rsum (rbuild @target @r @1 [50] (\[i] -> rindex v [wrap i]))

testOverleaf :: Assertion
testOverleaf =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @1 [28] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @0 overleaf (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafInt64n :: Assertion
testOverleafInt64n =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [0 :: Double,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))
    (crev @_ @(TKR Int64 0)
          overleaf (ringestData [28] [0 .. 27]))

testOverleafCIntn :: Assertion
testOverleafCIntn =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [0 :: Double,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))
    (rev @_ @(TKR CInt 0)
         overleaf (ringestData [28] [0 .. 27]))

testOverleafCIntToFloatn :: Assertion
testOverleafCIntToFloatn =
  assertEqualUpToEpsilon 1e-10
    (rfromList0N [28] (replicate 28 (rscalar 0.0)))
    (rev @_ @(TKR Float 0)
         (rfromIntegral . overleaf @CInt . rfloor) (ringestData @_ @Float [28] [0 .. 27]))

testOverleafInt64p :: Assertion
testOverleafInt64p =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Int64 [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @Int64 @0 overleaf (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafCIntp :: Assertion
testOverleafCIntp =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @CInt [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @CInt @0 overleaf (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafCIntToFloatp :: Assertion
testOverleafCIntToFloatp =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Float @1 [28] (replicate 28 0.0))
    (let f :: forall f. ADReady f => f (TKR Float 1) -> f (TKR Float 0)
         f = rfromIntegral . overleaf @CInt . rfloor
     in rev' @Float @0 f (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafPP :: Assertion
testOverleafPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v"), (2, "i")]
      fT :: AstTensor AstMethodLet FullSpan (TKR Double 1)
         -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = overleaf
      (var3, ast3) = funToAst (FTKR [28]) $ fT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v -> rsum (rgather [50] v (\\[i] -> [remF i 28]))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True fT (ringestData [28] [0 .. 27])
  printArtifactPretty renames artifactRev
    @?= "\\x4 x1 -> rscatter [28] (rreplicate 50 x4) (\\[i5] -> [remF i5 28])"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rgather [50] v1 (\\[i3] -> [remF i3 28]))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x4 x1 -> rscatter [28] (rreplicate 50 x4) (\\[i5] -> [remF i5 28])"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rgather [50] v1 (\\[i3] -> [remF i3 28]))"
  show deltas
    @?= "ShareG 100000002 (SumR (ShareG 100000001 (GatherR [50] (InputG (FTKR [28]) (InputId 0)) <function>)))"

foo :: RealFloatF a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

fooF :: RealFloatF a => (a, a, a) -> a
fooF (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

testFoo :: Assertion
testFoo = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (rev @_ @(TKR Double 0)
         foo (rscalar 1.1, rscalar 2.2, rscalar 3.3))

testFooS :: Assertion
testFooS = do
  assertEqualUpToEpsilon 1e-10
    (srepl 2.4396285219055063, srepl (-1.953374825727421), srepl 0.9654825811012627)
    (rev @_ @(TKS Double '[3, 534, 3])
         fooF (srepl 1.1, srepl 2.2, srepl 3.3))

testFooSToFloat :: Assertion
testFooSToFloat = do
  assertEqualUpToEpsilon 1e-10
    (srepl 2.4396285219055063, srepl (-1.953374825727421), srepl 0.9654825811012627)
    (rev @_ @(TKS Float '[3, 534, 3])
         (scast . fooF)
         (srepl 1.1 :: RepN (TKS Double '[3, 534, 3]), srepl 2.2, srepl 3.3))

testFooSBoth :: Assertion
testFooSBoth = do
  assertEqualUpToEpsilon 1e-10
    (srepl 2.439628436155373, srepl (-1.9533749), srepl 0.9654825479484146)
    (rev @_ @(TKS Float '[3, 534, 3])
         (scast . fooF . (\(d, f, d2) -> (d, scast f, d2)))
         ( srepl 1.1 :: RepN (TKS Double '[3, 534, 3])
         , srepl 2.2 :: RepN (TKS Float '[3, 534, 3])
         , srepl 3.3 ))

testFooBoth :: Assertion
testFooBoth = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.439628436155373, rscalar (-1.9533749), rscalar 0.9654825479484146)
    (rev @_ @(TKR Float 0)
         (rcast . foo . (\(d, f, d2) -> (d, rcast f, d2)))
         ( rscalar 1.1 :: RepN (TKR Double 0)
         , rscalar 2.2 :: RepN (TKR Float 0)
         , rscalar 3.3 ))

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      fooT = foo @(AstTensor AstMethodLet FullSpan (TKR Double 0))
      foo3 x = fooT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR) $ foo3
  "\\" ++ printAstVarName IM.empty var3
       ++ " -> " ++ printAstSimple IM.empty ast3
    @?= "\\x1 -> atan2F x1 (x1 * sin x1) + x1 * (x1 * sin x1)"
  resetVarCounter
  let (artifactRev, _) = revArtifactAdapt True fooT (4, 5, 6)
  printArtifactSimple renames artifactRev
    @?= "\\x7 x1 -> tlet (sin (tproject2 (tproject1 x1))) (\\x -> tlet (tproject1 (tproject1 x1) * x) (\\y -> tlet (recip (tproject2 x1 * tproject2 x1 + y * y)) (\\z -> tlet (sin (tproject2 (tproject1 x1))) (\\x5 -> tlet (tproject1 (tproject1 x1) * x5) (\\x6 -> tlet (tproject2 x1 * x7) (\\x8 -> tlet ((negate (tproject2 x1) * z) * x7) (\\x9 -> tpair (tpair (x * x9 + x5 * x8, cos (tproject2 (tproject1 x1)) * (tproject1 (tproject1 x1) * x9) + cos (tproject2 (tproject1 x1)) * (tproject1 (tproject1 x1) * x8)), (y * z) * x7 + x6 * x7))))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x1 -> tlet (sin (tproject2 (tproject1 x1))) (\\x -> tlet (tproject1 (tproject1 x1) * x) (\\y -> tlet (sin (tproject2 (tproject1 x1))) (\\x5 -> tlet (tproject1 (tproject1 x1) * x5) (\\x6 -> atan2F (tproject2 x1) y + tproject2 x1 * x6))))"

fooLet :: forall target r n.
          ( RealFloatF (target (TKR r n))
          , LetTensor target
          , KnownNat n, GoodScalar r )
       => (target (TKR r n), target (TKR r n), target (TKR r n)) -> target (TKR r n)
fooLet (x, y, z) =
  let w0 = x * sin y
  in tlet w0 $ \w ->
     atan2F z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (rev @_ @(TKR Double 0)
         fooLet (rscalar 1.1, rscalar 2.2, rscalar 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      renamesNull = IM.fromList [(1, "x1"), (2, "x2")]
      fooLetT = fooLet @(AstTensor AstMethodLet FullSpan) @Double
      fooLet3 x = fooLetT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR) $ fooLet3
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\x1 -> tlet (x1 * sin x1) (\\x2 -> atan2F x1 x2 + x1 * x2)"
  resetVarCounter
  let (artifactRev, _) = revArtifactAdapt True fooLetT (4, 5, 6)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x6 x1 -> let y = sin (tproject2 (tproject1 x1)) ; z = tproject1 (tproject1 x1) * y ; x5 = recip (tproject2 x1 * tproject2 x1 + z * z) ; x7 = (negate (tproject2 x1) * x5) * x6 + tproject2 x1 * x6 in tpair (tpair (y * x7, cos (tproject2 (tproject1 x1)) * (tproject1 (tproject1 x1) * x7)), (z * x5) * x6 + z * x6)"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let z = tproject1 (tproject1 x1) * sin (tproject2 (tproject1 x1)) in atan2F (tproject2 x1) z + tproject2 x1 * z"

_shapedListProd :: (BaseTensor target, GoodScalar r)
               => [target (TKS r '[])] -> target (TKS r '[])
_shapedListProd = foldl1' (*)

{- TODO: this requires a better AdaptableHVector instance for [a]
testListProdPP :: Assertion
testListProdPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKS Double '[])] -> AstTensor AstMethodLet FullSpan (TKS Double '[])
      fT = shapedListProd
  let (artifactRev, _deltas) = revArtifactAdapt True fT [srepl 1, srepl 2, srepl 3, srepl 4]
  printArtifactSimple renames artifactRev
    @?= "\\x17 x20 x21 x22 x23 -> tlet (x20 * x21) (\\x12 -> tlet (x12 * x22) (\\x15 -> tlet (x23 * x17) (\\x18 -> tlet (x22 * x18) (\\x19 -> dmkHVector (fromList [DynamicShaped (x21 * x19), DynamicShaped (x20 * x19), DynamicShaped (x12 * x18), DynamicShaped (x15 * x17)])))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x56 x57 x58 x59 -> tlet (x56 * x57) (\\x12 -> tlet (x12 * x58) (\\x15 -> x15 * x59))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x124 x125 x126 x127 -> let x12 = x124 * x125 ; x18 = x127 * x17 ; x19 = x126 * x18 in [x125 * x19, x124 * x19, x12 * x18, (x12 * x126) * x17]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x160 x161 x162 x163 -> ((x160 * x161) * x162) * x163"
-}

rankedListProdr :: (BaseTensor target, GoodScalar r)
                => [target (TKR r 0)] -> target (TKR r 0)
rankedListProdr = foldr1 (*)

testListProdrPP :: Assertion
testListProdrPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListProdr
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x52 x53 x54 x55 -> let x14 = x54 * x55 ; x18 = x52 * x17 ; x19 = x53 * x18 in [(x53 * x14) * x17, x14 * x18, x55 * x19, x54 * x19]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x88 x89 x90 x91 -> x88 * (x89 * (x90 * x91))"

testListProdrLongPP :: Assertion
testListProdrLongPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListProdr
  let (artifactRev, _) =
        revArtifactAdapt True fT [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  printArtifactSimple renames artifactRev
    @?= "\\x53 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 -> tlet (x76 * x77) (\\x32 -> tlet (x75 * x32) (\\x34 -> tlet (x74 * x34) (\\x36 -> tlet (x73 * x36) (\\x38 -> tlet (x72 * x38) (\\x40 -> tlet (x71 * x40) (\\x42 -> tlet (x70 * x42) (\\x44 -> tlet (x69 * x44) (\\x46 -> tlet (x68 * x46) (\\x48 -> tlet (x67 * x48) (\\x50 -> tlet (x66 * x50) (\\x52 -> tlet (x65 * x53) (\\x54 -> tlet (x66 * x54) (\\x55 -> tlet (x67 * x55) (\\x56 -> tlet (x68 * x56) (\\x57 -> tlet (x69 * x57) (\\x58 -> tlet (x70 * x58) (\\x59 -> tlet (x71 * x59) (\\x60 -> tlet (x72 * x60) (\\x61 -> tlet (x73 * x61) (\\x62 -> tlet (x74 * x62) (\\x63 -> tlet (x75 * x63) (\\x64 -> dmkHVector (fromList [DynamicRanked (x52 * x53), DynamicRanked (x50 * x54), DynamicRanked (x48 * x55), DynamicRanked (x46 * x56), DynamicRanked (x44 * x57), DynamicRanked (x42 * x58), DynamicRanked (x40 * x59), DynamicRanked (x38 * x60), DynamicRanked (x36 * x61), DynamicRanked (x34 * x62), DynamicRanked (x32 * x63), DynamicRanked (x77 * x64), DynamicRanked (x76 * x64)])))))))))))))))))))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x416 x417 x418 x419 x420 x421 x422 x423 x424 x425 x426 x427 x428 -> tlet (x427 * x428) (\\x32 -> tlet (x426 * x32) (\\x34 -> tlet (x425 * x34) (\\x36 -> tlet (x424 * x36) (\\x38 -> tlet (x423 * x38) (\\x40 -> tlet (x422 * x40) (\\x42 -> tlet (x421 * x42) (\\x44 -> tlet (x420 * x44) (\\x46 -> tlet (x419 * x46) (\\x48 -> tlet (x418 * x48) (\\x50 -> tlet (x417 * x50) (\\x52 -> x416 * x52)))))))))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x53 x1105 x1106 x1107 x1108 x1109 x1110 x1111 x1112 x1113 x1114 x1115 x1116 x1117 -> let x32 = x1116 * x1117 ; x34 = x1115 * x32 ; x36 = x1114 * x34 ; x38 = x1113 * x36 ; x40 = x1112 * x38 ; x42 = x1111 * x40 ; x44 = x1110 * x42 ; x46 = x1109 * x44 ; x48 = x1108 * x46 ; x50 = x1107 * x48 ; x54 = x1105 * x53 ; x55 = x1106 * x54 ; x56 = x1107 * x55 ; x57 = x1108 * x56 ; x58 = x1109 * x57 ; x59 = x1110 * x58 ; x60 = x1111 * x59 ; x61 = x1112 * x60 ; x62 = x1113 * x61 ; x63 = x1114 * x62 ; x64 = x1115 * x63 in [(x1106 * x50) * x53, x50 * x54, x48 * x55, x46 * x56, x44 * x57, x42 * x58, x40 * x59, x38 * x60, x36 * x61, x34 * x62, x32 * x63, x1117 * x64, x1116 * x64]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1456 x1457 x1458 x1459 x1460 x1461 x1462 x1463 x1464 x1465 x1466 x1467 x1468 -> x1456 * (x1457 * (x1458 * (x1459 * (x1460 * (x1461 * (x1462 * (x1463 * (x1464 * (x1465 * (x1466 * (x1467 * x1468)))))))))))"

{- TODO: this requires a better AdaptableHVector instance for [a]
testListProd :: Assertion
testListProd = do
  assertEqualUpToEpsilon 1e-10
    [srepl 24, srepl 12, srepl 8, srepl 6]
    (rev @_ @(TKS Double '[])
         shapedListProd [srepl 1, srepl 2, srepl 3, srepl 4])
-}

testListProdr :: Assertion
testListProdr = do
  assertEqualUpToEpsilon 1e-10
    [24, 12, 8, 6]
    (rev @_ @(TKR Double 0)
         rankedListProdr [1, 2, 3, 4])

rankedListSumr :: (BaseTensor target, GoodScalar r)
                => [target (TKR r 0)] -> target (TKR r 0)
rankedListSumr = foldr1 (+)

testListSumrPP :: Assertion
testListSumrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSumr
  let (artifactRev, deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x11 x28 x29 x30 x31 -> [x11, x11, x11, x11]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x48 x49 x50 x51 -> x48 + x49 + x50 + x51"
  show deltas
    @?= "ShareG 100000003 (AddG (InputG (FTKR []) (InputId 0)) (ShareG 100000002 (AddG (InputG (FTKR []) (InputId 1)) (ShareG 100000001 (AddG (InputG (FTKR []) (InputId 2)) (InputG (FTKR []) (InputId 3)))))))"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum2r :: (BaseTensor target, GoodScalar r)
                => [target (TKR r 0)] -> target (TKR r 0)
rankedListSum2r = foldr1 (\x y -> x + 2 * y)

testListSum2rPP :: Assertion
testListSum2rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSum2r
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x14 x33 x34 x35 x36 -> let x15 = 2.0 * x14 ; x16 = 2.0 * x15 in [x14, x15, x16, 2.0 * x16]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x53 x54 x55 x56 -> x53 + 2.0 * (x54 + 2.0 * (x55 + 2.0 * x56))"

rankedListSum22r :: (BaseTensor target, GoodScalar r)
                 => [target (TKR r 0)] -> target (TKR r 0)
rankedListSum22r = foldr1 (\x y -> 2 * x + 2 * y)

testListSum22rPP :: Assertion
testListSum22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSum22r
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x36 x37 x38 x39 -> let x18 = 2.0 * x17 ; x19 = 2.0 * x18 in [2.0 * x17, 2.0 * x18, 2.0 * x19, 2.0 * x19]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x56 x57 x58 x59 -> 2.0 * x56 + 2.0 * (2.0 * x57 + 2.0 * (2.0 * x58 + 2.0 * x59))"

-- Note how this tlet did not change anything, in particular the sharing.
rankedListSumk22r :: ( BaseTensor target, LetTensor target
                     , GoodScalar r )
                 => [target (TKR r 0)] -> target (TKR r 0)
rankedListSumk22r = foldr1 (\x y -> tlet 2 (\k -> k * x + k * y))

testListSumk22rPP :: Assertion
testListSumk22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSumk22r
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x36 x37 x38 x39 -> let x18 = 2.0 * x17 ; x19 = 2.0 * x18 in [2.0 * x17, 2.0 * x18, 2.0 * x19, 2.0 * x19]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x56 x57 x58 x59 -> 2.0 * x56 + 2.0 * (2.0 * x57 + 2.0 * (2.0 * x58 + 2.0 * x59))"

rankedListSum2xpyr :: (BaseTensor target, GoodScalar r)
                   => [target (TKR r 0)] -> target (TKR r 0)
rankedListSum2xpyr = foldr1 (\x y -> 2 * (x + y))

testListSum2xpyrPP :: Assertion
testListSum2xpyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSum2xpyr
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x14 x34 x35 x36 x37 -> let x15 = 2.0 * x14 ; x16 = 2.0 * x15 ; x17 = 2.0 * x16 in [x15, x16, x17, x17]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x54 x55 x56 x57 -> 2.0 * (x54 + 2.0 * (x55 + 2.0 * (x56 + x57)))"

rankedListSum2xyr :: (BaseTensor target, GoodScalar r)
                  => [target (TKR r 0)] -> target (TKR r 0)
rankedListSum2xyr = foldr1 (\x y -> 2 * (x * y))

testListSum2xyrPP :: Assertion
testListSum2xyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSum2xyr
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x20 x56 x57 x58 x59 -> let x15 = 2.0 * (x58 * x59) ; x21 = 2.0 * x20 ; x22 = 2.0 * (x56 * x21) ; x23 = 2.0 * (x57 * x22) in [(2.0 * (x57 * x15)) * x21, x15 * x22, x59 * x23, x58 * x23]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x92 x93 x94 x95 -> 2.0 * (x92 * (2.0 * (x93 * (2.0 * (x94 * x95)))))"

ranked2xy :: (BaseTensor target, GoodScalar r)
          => (target (TKR r 0), target (TKR r 0)) -> target (TKR r 0)
ranked2xy = \(x, y) -> rscalar 2 * x * y

test2xyPP :: Assertion
test2xyPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstTensor AstMethodLet FullSpan (TKR Double 0), AstTensor AstMethodLet FullSpan (TKR Double 0))
         -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = ranked2xy
  let (artifactRev, _deltas) = revArtifactAdapt True fT (4, 5)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x3 x1 -> tpair (2.0 * (tproject2 x1 * x3), (2.0 * tproject1 x1) * x3)"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> (2.0 * tproject1 x1) * tproject2 x1"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum23r :: (BaseTensor target, GoodScalar r)
                 => [target (TKR r 0)] -> target (TKR r 0)
rankedListSum23r = foldr1 (\x y -> rscalar 2 * x + rscalar 3 * y)

testListSum23rPP :: Assertion
testListSum23rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstTensor AstMethodLet FullSpan (TKR Double 0)] -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = rankedListSum23r
  let (artifactRev, _deltas) = revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x36 x37 x38 x39 -> let x18 = 3.0 * x17 ; x19 = 3.0 * x18 in [2.0 * x17, 2.0 * x18, 2.0 * x19, 3.0 * x19]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x56 x57 x58 x59 -> 2.0 * x56 + 3.0 * (2.0 * x57 + 3.0 * (2.0 * x58 + 3.0 * x59))"

ranked23 :: (BaseTensor target, GoodScalar r)
         => (target (TKR r 0), target (TKR r 0)) -> target (TKR r 0)
ranked23 = \(x, y) -> rscalar 2 * x + rscalar 3 * y

test23PP :: Assertion
test23PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstTensor AstMethodLet FullSpan (TKR Double 0), AstTensor AstMethodLet FullSpan (TKR Double 0))
         -> AstTensor AstMethodLet FullSpan (TKR Double 0)
      fT = ranked23
  let (artifactRev, _deltas) = revArtifactAdapt True fT (4, 5)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x2 x1 -> tpair (2.0 * x2, 3.0 * x2)"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> 2.0 * tproject1 x1 + 3.0 * tproject2 x1"

reluPrimal
  :: forall target n r.
     (ADReady target, GoodScalar r, KnownNat n, Differentiable r)
  => target (TKR r n) -> target (TKR r n)
reluPrimal v =
  let oneIfGtZero = rmap0N (\x -> ifF (x <=. 0) (rscalar 0.0) (rscalar 1.0))
                           (rprimalPart v)
  in scale oneIfGtZero v

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstTensor AstMethodLet FullSpan (TKR Double 2) -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT = reluPrimal
      (var3, ast3) = funToAst (FTKR [3, 4]) $ reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m8 x1 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) * m8"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) * m1"
  show deltas
    @?= "ShareG 100000003 (ScaleG (AstRaw {unAstRaw = AstShare (AstVarId 100000007) (AstGather [3,4] (AstConst (rfromListLinear [2] [0.0,1.0])) ([AstVarId 100000005,AstVarId 100000006],[AstCond (AstRel LeqOp (AstIndex (AstVar (FTKR [3,4]) (AstVarId 100000001)) [AstVar (FTKR []) (AstVarId 100000005),AstVar (FTKR []) (AstVarId 100000006)]) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [0])) (AstConst (rfromListLinear [] [1]))]))}) (InputG (FTKR [3,4]) (InputId 0)))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 1), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 1)
      reluT2 (t, r) = reluPrimal (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rconstant (rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i2] -> [ifF (rprimalPart v1 ! [i2] * 7.0 <=. 0.0) 0 1])) * (v1 * rconstant (rreplicate 5 7.0))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> let v8 = rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifF (tproject1 v1 ! [i3] * tproject2 v1 <=. 0.0) 0 1]) * v7 in tpair (rreplicate 5 (tproject2 v1) * v8, rsum (tproject1 v1 * v8))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifF (tproject1 v1 ! [i3] * tproject2 v1 <=. 0.0) 0 1]) * (tproject1 v1 * rreplicate 5 (tproject2 v1))"

testReluSimpler :: Assertion
testReluSimpler = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 relu (FlipR $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluSimplerPP :: Assertion
testReluSimplerPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstTensor AstMethodLet FullSpan (TKR Double 2) -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT = relu
      (var3, ast3) = funToAst (FTKR [3, 4]) $ reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m8 x1 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) * m8"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifF (m1 ! [i5, i6] <=. 0.0) 0 1]) * m1"
  show deltas
    @?= "ShareG 100000003 (ScaleG (AstRaw {unAstRaw = AstShare (AstVarId 100000007) (AstGather [3,4] (AstConst (rfromListLinear [2] [0.0,1.0])) ([AstVarId 100000005,AstVarId 100000006],[AstCond (AstRel LeqOp (AstIndex (AstVar (FTKR [3,4]) (AstVarId 100000001)) [AstVar (FTKR []) (AstVarId 100000005),AstVar (FTKR []) (AstVarId 100000006)]) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [0])) (AstConst (rfromListLinear [] [1]))]))}) (InputG (FTKR [3,4]) (InputId 0)))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 1), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 1)
      reluT2 (t, r) = relu (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tlet (v1 * rconstant (rreplicate 5 7.0)) (\\i2 -> rconstant (rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifF (rprimalPart i2 ! [i3] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v7 x1 -> let v8 = rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifF (tproject1 v1 ! [i5] * tproject2 v1 <=. 0.0) 0 1]) * v7 in tpair (rreplicate 5 (tproject2 v1) * v8, rsum (tproject1 v1 * v8))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let v4 = tproject1 v1 * rreplicate 5 (tproject2 v1) in rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifF (v4 ! [i5] <=. 0.0) 0 1]) * v4"

testReluSimplerPP3 :: Assertion
testReluSimplerPP3 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 2), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
      (var3, ast3) = funToAst (FTKR [3, 4]) (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tlet (v1 * rconstant (rreplicate 3 (rreplicate 4 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [3, 4] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m10 x1 -> let m11 = rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifF (tproject1 m1 ! [i7, i8] * tproject2 m1 <=. 0.0) 0 1]) * m10 in tpair (rreplicate 3 (rreplicate 4 (tproject2 m1)) * m11, rsum (rsum (tproject1 m1 * m11)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let m6 = tproject1 m1 * rreplicate 3 (rreplicate 4 (tproject2 m1)) in rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifF (m6 ! [i7, i8] <=. 0.0) 0 1]) * m6"

testReluSimpler3 :: Assertion
testReluSimpler3 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 2), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (rev reluT2 (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testReluSimplerPP4 :: Assertion
testReluSimplerPP4 = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 2), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
      (var3, ast3) = funToAst (FTKR [3, 4]) (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tlet (v1 * rconstant (rreshape [3,4] (rreplicate 12 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [3, 4] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m11 x1 -> let m12 = rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (tproject1 m1 ! [i8, i9] * tproject2 m1 <=. 0.0) 0 1]) * m11 in tpair (rreplicate 3 (rreplicate 4 (tproject2 m1)) * m12, rsum (rreshape [12] (tproject1 m1) * rreshape [12] m12))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let m7 = tproject1 m1 * rreplicate 3 (rreplicate 4 (tproject2 m1)) in rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i8, i9] -> [ifF (m7 ! [i8, i9] <=. 0.0) 0 1]) * m7"

testReluSimpler4 :: Assertion
testReluSimpler4 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 2), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (rev reluT2 (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testReluSimplerPP4S :: Assertion
testReluSimplerPP4S = do
  resetVarCounter
  let renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKS Float '[3, 4]), AstTensor AstMethodLet FullSpan (TKS Float '[]))
             -> AstTensor AstMethodLet FullSpan (TKS Float '[3, 4])
      reluT2 (t, r) = reluS (t * sreplicate0N r)
      (var3, ast3) = funToAst (FTKS knownShS) (\t -> reluT2 (t, srepl 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> tlet (v1 * sconstant (sreshape (sreplicate 7.0))) (\\i2 -> sconstant (sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i5, i4] -> [i5, ifF (sprimalPart i2 !$ [i5, i4] <=. 0.0) 0 1])) * i2)"

testReluSimplerPP4S2 :: Assertion
testReluSimplerPP4S2 = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKS Double '[3, 4]), AstTensor AstMethodLet FullSpan (TKS Double '[]))
             -> AstTensor AstMethodLet FullSpan (TKS Double '[3, 4])
      -- This is tweaked compared to above to avoid test artifacts coming
      -- from counter resets, which are inherently unsafe (cse, etc.).
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (srepl 128, srepl 42)
  printArtifactPretty renames artifactRev
    @?= "\\m11 x1 -> let m5 = sreshape (sreplicate (tproject2 m1)) ; m6 = tproject1 m1 * m5 ; m10 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i7, i8] -> [i7, ifF (m6 !$ [i7, i8] <=. 0.0) 0 1]) ; m12 = m10 * m11 in tpair (m5 * m12, ssum (sreshape (tproject1 m1 * m12)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let m5 = sreshape (sreplicate (tproject2 m1)) ; m6 = tproject1 m1 * m5 ; m10 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i7, i8] -> [i7, ifF (m6 !$ [i7, i8] <=. 0.0) 0 1]) in m10 * m6"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m11 x1 -> let m5 = sreshape (sreplicate (tproject2 m1)) ; m12 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i7, i8] -> [i7, ifF (tproject1 m1 !$ [i7, i8] * m5 !$ [i7, i8] <=. 0.0) 0 1]) * m11 in tpair (m5 * m12, ssum (sreshape (tproject1 m1) * sreshape m12))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> let m6 = tproject1 m1 * sreshape (sreplicate (tproject2 m1)) in sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i7, i8] -> [i7, ifF (m6 !$ [i7, i8] <=. 0.0) 0 1]) * m6"

testReluSimpler4S :: Assertion
testReluSimpler4S = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKS Double '[3, 4]), AstTensor AstMethodLet FullSpan (TKS Double '[]))
             -> AstTensor AstMethodLet FullSpan (TKS Double '[3, 4])
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  assertEqualUpToEpsilon 1e-10
    ( sconst
      $ Nested.sfromListPrimLinear @_ @'[3, 4] knownShS [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , srepl 57.1 )
    (rev reluT2 (sconst $ Nested.sfromListPrimLinear @_ @'[3, 4] knownShS [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], srepl 7))

reluMax :: forall target n r. (ADReady target, GoodScalar r, KnownNat n)
        => target (TKR r n) -> target (TKR r n)
reluMax = rmap0N (maxF (rscalar 0))

testReluMax :: Assertion
testReluMax = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 reluMax (FlipR $ OR.fromList [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluMaxPP :: Assertion
testReluMaxPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstTensor AstMethodLet FullSpan (TKR Double 2) -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT = reluMax
      (var3, ast3) = funToAst (FTKR [3, 4]) $ reluT
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\m1 -> rgather [3,4] (rfromVector (fromList [rconstant (rreplicate 3 (rreplicate 4 0.0)), m1])) (\\[i5, i4] -> [ifF (0.0 >=. rprimalPart m1 ! [i5, i4]) 0 1, i5, i4])"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m8 x1 -> rscatter [2,3,4] m8 (\\[i9, i10] -> [ifF (0.0 >=. m1 ! [i9, i10]) 0 1, i9, i10]) ! [1]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rgather [3,4] (rfromVector (fromList [rreplicate 3 (rreplicate 4 0.0), m1])) (\\[i6, i7] -> [ifF (0.0 >=. m1 ! [i6, i7]) 0 1, i6, i7])"
  show deltas
    @?= "ShareG 100000005 (GatherR [3,4] (ShareG 100000003 (FromVectorR [ZeroG (FTKR [3,4]),InputG (FTKR [3,4]) (InputId 0)])) <function>)"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 1), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 1)
      reluT2 (t, r) = reluMax (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> reluT2 (t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull ast3
    @?= "\\v1 -> rgather [5] (rfromVector (fromList [rconstant (rreplicate 5 0.0), v1 * rconstant (rreplicate 5 7.0)])) (\\[i3] -> [ifF (0.0 >=. rprimalPart v1 ! [i3] * 7.0) 0 1, i3])"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames artifactRev
    @?= "\\v6 x1 -> let m9 = rscatter [2,5] v6 (\\[i7] -> [let x8 = tproject1 v1 ! [i7] in ifF (0.0 >=. x8 * tproject2 v1) 0 1, i7]) ; v10 = m9 ! [1] in tpair (rreplicate 5 (tproject2 v1) * v10, rsum (tproject1 v1 * v10))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rgather [5] (rfromVector (fromList [rreplicate 5 0.0, tproject1 v1 * rreplicate 5 (tproject2 v1)])) (\\[i4] -> [let x5 = tproject1 v1 ! [i4] in ifF (0.0 >=. x5 * tproject2 v1) 0 1, i4])"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v6 x1 -> let v10 = rscatter [2,5] v6 (\\[i7] -> [ifF (0.0 >=. tproject1 v1 ! [i7] * tproject2 v1) 0 1, i7]) ! [1] in tpair (rreplicate 5 (tproject2 v1) * v10, rsum (tproject1 v1 * v10))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rgather [5] (rfromVector (fromList [rreplicate 5 0.0, tproject1 v1 * rreplicate 5 (tproject2 v1)])) (\\[i4] -> [ifF (0.0 >=. tproject1 v1 ! [i4] * tproject2 v1) 0 1, i4])"

testReluMax3 :: Assertion
testReluMax3 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR Double 2), AstTensor AstMethodLet FullSpan (TKR Double 0))
             -> AstTensor AstMethodLet FullSpan (TKR Double 2)
      reluT2 (t, r) = reluMax (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (rev reluT2 (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testDot1PP :: Assertion
testDot1PP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt True (uncurry (rdot0 @(AstTensor AstMethodLet FullSpan) @Double @1))
                 ( ringestData [3] [1 .. 3]
                 , ringestData [3] [4 .. 6] )
  printArtifactPretty renames artifactRev
    @?= "\\x2 x1 -> tpair (tproject2 v1 * rreshape [3] (rreplicate 3 x2), tproject1 v1 * rreshape [3] (rreplicate 3 x2))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rreshape [3] (tproject1 v1 * tproject2 v1))"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      (artifactRev, deltas) =
        revArtifactAdapt True (uncurry (rdot0 @(AstTensor AstMethodLet FullSpan) @Double @2))
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [2,3] [7 .. 12] )
  printArtifactPretty renames artifactRev
    @?= "\\x4 x1 -> let v2 = rreshape [6] (tproject1 m1) ; v3 = rreshape [6] (tproject2 m1) in tpair (rreshape [2,3] (v3 * rreshape [6] (rreplicate 6 x4)), rreshape [2,3] (v2 * rreshape [6] (rreplicate 6 x4)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> let v2 = rreshape [6] (tproject1 m1) ; v3 = rreshape [6] (tproject2 m1) in rsum (rreshape [6] (v2 * v3))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x4 x1 -> tpair (tproject2 m1 * rreplicate 2 (rreplicate 3 x4), tproject1 m1 * rreplicate 2 (rreplicate 3 x4))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rreshape [6] (tproject1 m1) * rreshape [6] (tproject2 m1))"
  show deltas
    @?= "ShareG 100000003 (AddG (Dot0R (AstRaw {unAstRaw = AstShare (AstVarId 100000003) (AstReshape [6] (AstProject2 (AstVar (FTKProduct (FTKR [2,3]) (FTKR [2,3])) (AstVarId 100000001))))}) (ShareG 100000001 (ReshapeR [6] (InputG (FTKR [2,3]) (InputId 0))))) (Dot0R (AstRaw {unAstRaw = AstShare (AstVarId 100000002) (AstReshape [6] (AstProject1 (AstVar (FTKProduct (FTKR [2,3]) (FTKR [2,3])) (AstVarId 100000001))))}) (ShareG 100000002 (ReshapeR [6] (InputG (FTKR [2,3]) (InputId 1))))))"

testMatvecmulPP :: Assertion
testMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatvecmul)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3] [7 .. 9] )
  printArtifactPretty @_ @(TKR Double 1) renames artifactRev
    @?= "\\v3 x1 -> tpair (rtranspose [1,0] (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rreplicate 3 v3), rsum (rtranspose [1,0] (rtranspose [1,0] (tproject1 m1) * rreplicate 3 v3)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rtranspose [1,0] (tproject1 m1))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v3 x1 -> tpair (rreplicate 2 (tproject2 m1) * rtranspose [1,0] (rreplicate 3 v3), rsum (tproject1 m1 * rtranspose [1,0] (rreplicate 3 v3)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rtranspose [1,0] (tproject1 m1))"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatmul2)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3,4] [7 .. 18] )
  printArtifactPretty @_ @(TKR Double 2) renames artifactRev
    @?= "\\m2 x1 -> tpair (rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rreplicate 3 m2)), rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rreplicate 3 m2)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rtranspose [1,0] (rreplicate 2 (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m2 x1 -> tpair (rsum (rtranspose [2,0,1] (rreplicate 2 (tproject2 m1)) * rtranspose [2,1,0] (rreplicate 3 m2)), rsum (rtranspose [1,2,0] (rreplicate 4 (tproject1 m1)) * rtranspose [1,0] (rreplicate 3 m2)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rsum (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rtranspose [1,0] (rreplicate 2 (tproject2 m1)))"

testMatmul2FromMatvecmulPP :: Assertion
testMatmul2FromMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2F :: (BaseTensor target, GoodScalar r)
                => target (TKR r 2) -> target (TKR r 2) -> target (TKR r 2)
      rmatmul2F m1 m2 =
        rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatmul2F)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3,4] [7 .. 18] )
  printArtifactPretty @_ @(TKR Double 2) renames artifactRev
    @?= "\\m7 x1 -> tpair (rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rreplicate 3 m7)), rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rreplicate 3 m7)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rtranspose [1,0] (rreplicate 2 (tproject2 m1)))"

testMatmul2PaperPP :: Assertion
testMatmul2PaperPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2P :: (BaseTensor target, GoodScalar r)
                => target (TKR r 2) -> target (TKR r 2) -> target (TKR r 2)
      rmatmul2P a b =
        let k :$: m :$: _ = rshape a
            _ :$: n :$: _ = rshape b
        in rbuild1 k (\i ->
             rbuild1 n (\j ->
               rsum (rbuild1 m (\p -> a ! [i, p] * b ! [p, j]))))
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatmul2P)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3,4] [7 .. 18] )
  printArtifactPretty @_ @(TKR Double 2) renames artifactRev
    @?= "\\m6 x1 -> tpair (rsum (rtranspose [2,1,0] (rtranspose [1,0] (rreplicate 2 (tproject2 m1)) * rreplicate 3 m6)), rsum (rtranspose [1,0] (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rreplicate 3 m6)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> rsum (rtranspose [2,1,0] (rreplicate 4 (tproject1 m1)) * rtranspose [1,0] (rreplicate 2 (tproject2 m1)))"

testMatmul2PPS :: Assertion
testMatmul2PPS = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry smatmul2)
                 ( sconst $ Nested.sfromListPrimLinear @_ @'[2,3] knownShS [1 :: Double .. 6]
                 , sconst $ Nested.sfromListPrimLinear @_ @'[3,4] knownShS [7 .. 18] )
  printArtifactPretty renames artifactRev
    @?= "\\m2 x1 -> tpair (ssum (stranspose (stranspose (sreplicate (tproject2 m1)) * sreplicate m2)), ssum (stranspose (stranspose (sreplicate (tproject1 m1)) * sreplicate m2)))"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x1 -> ssum (stranspose (sreplicate (tproject1 m1)) * stranspose (sreplicate (tproject2 m1)))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m2 x1 -> tpair (ssum (stranspose (sreplicate (tproject2 m1)) * stranspose (sreplicate m2)), ssum (stranspose (sreplicate (tproject1 m1)) * stranspose (sreplicate m2)))"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> ssum (stranspose (sreplicate (tproject1 m1)) * stranspose (sreplicate (tproject2 m1)))"

testAddSpeedBig :: Assertion
testAddSpeedBig =
  let m1 :: RepN (TKR Double 2)
      m1 = ringestData [1000,1000] [1 .. 1000000]
      m2 = m1 + m1
  in assertEqualUpToEpsilon 1e-10 m2 m2

testMatmul2SpeedBig :: Assertion
testMatmul2SpeedBig =
  let m1 :: RepN (TKR Double 2)
      m1 = ringestData [1000,1000] [1 .. 1000000]
      m2 = rmatmul2 m1 m1
  in assertEqualUpToEpsilon 1e-10 m2 m2

bar :: forall a. RealFloatF a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2F x w + y * w

barF :: forall a. RealFloatF a => (a, a) -> a
barF (x, y) =
  let w = fooF (x, y, x) * sin y
  in atan2F x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (rscalar 3.1435239435581166,rscalar (-1.1053869545195814))
    (crev (bar @(ADVal RepN (TKR Double 0))) (rscalar 1.1, rscalar 2.2))

testBarS :: Assertion
testBarS =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (crev (barF @(ADVal RepN (TKS Double '[]))) (srepl 1.1, srepl 2.2))

testBar2S :: Assertion
testBar2S =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (rev (barF @(AstTensor AstMethodLet FullSpan (TKS Double '[52, 2, 2, 1, 1, 3]))) (srepl 1.1, srepl 2.2))

testBarCFwd :: Assertion
testBarCFwd =
  assertEqualUpToEpsilon 1e-9
    (rscalar 9.327500345189534e-2)
    (cfwd (bar @(ADVal RepN (TKR Double 0))) (rscalar 1.1, rscalar 2.2) (rscalar 0.1, rscalar 0.2))

testBarFwd :: Assertion
testBarFwd =
  assertEqualUpToEpsilon 1e-9
    (rscalar 9.327500345189534e-2)
    (fwd @_ @(TKR Double 0)
         bar (rscalar 1.1, rscalar 2.2) (rscalar 0.1, rscalar 0.2))

barADVal2 :: forall a. RealFloatF a
          => (a, a, a) -> a
barADVal2 (x,y,z) =
  let w = foo (x,y,z) * sin y
  in atan2F z w + z * w

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
baz :: ( ADVal RepN (TKR Double 0)
       , ADVal RepN (TKR Double 0)
       , ADVal RepN (TKR Double 0) )
    -> ADVal RepN (TKR Double 0)
baz (_x,y,z) =
  let w = fooConstant * barADVal2 (y,y,z) * sin y
  in atan2F z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal RepN (TKR Double 0)
fooConstant = foo (rscalar 7, rscalar 8, rscalar 9)

testBaz :: Assertion
testBaz =
  assertEqualUpToEpsilon 1e-9
    (rscalar 0, rscalar (-5219.20995030263), rscalar 2782.276274462047)
    (crev baz (rscalar 1.1, rscalar 2.2, rscalar 3.3))

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
    (rscalar 0, rscalar (-5219.20995030263), rscalar 2783.276274462047)
    (crev (\(x,y,z) -> z + baz (x,y,z)) (rscalar 1.1, rscalar 2.2, rscalar 3.3))

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r. r ~ Double
     => [ADVal RepN (TKR r 0)] -> ADVal RepN (TKR r 0)
fooD [x, y, z] =
  let w = x * sin y
  in atan2F z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627]
    (crev fooD [rscalar 1.1, rscalar 2.2, rscalar 3.3])

fooBuild1 :: (ADReady target, GoodScalar r, Differentiable r)
          => target (TKR r 1) -> target (TKR r 1)
fooBuild1 v =
  let r = rsum0 v
      v' = rminimum v
  in rbuild1 3 $ \ix ->
       r * foo ( rscalar 3
               , rscalar 5 * r
               , r * rminimum v * v')
       + bar (r, rindex v [ix + 1])

testFooBuildDt :: Assertion
testFooBuildDt =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [4] [-189890.46351219364,-233886.08744601303,-222532.22669716467,-206108.68889329425])
    (revDt @_ @(TKR Double 1)
           fooBuild1 (ringestData1 [1.1, 2.2, 3.3, 4]) (rreplicate0N [3] (rscalar 42)))

testFooBuildCFwd :: Assertion
testFooBuildCFwd =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (cfwd @_ @(TKR Double 1)
          fooBuild1 (ringestData1 [1.1, 2.2, 3.3, 4]) (rreplicate0N [4] (rscalar 42)))

testFooBuildFwd :: Assertion
testFooBuildFwd =
  assertEqualUpToEpsilon1 1e-5
    (OR.fromList [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (fwd @_ @(TKR Double 1)
         fooBuild1 (ringestData1 [1.1, 2.2, 3.3, 4]) (rreplicate0N [4] (rscalar 42)))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @Double @1 fooBuild1 (FlipR $ OR.fromList [4] [1.1, 2.2, 3.3, 4]))

fooMap1 :: (ADReady target, GoodScalar r, Differentiable r)
        => target (TKR r 0) -> target (TKR r 1)
fooMap1 r =
  let v = fooBuild1 $ rreplicate0N [130] r
  in rmap0N (\x -> x * r + rscalar 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-3
    4.438131773975095e7
    (rev' @Double @1 fooMap1 1.1)

barAst :: (GoodScalar r, Differentiable r)
       => (AstTensor AstMethodLet PrimalSpan (TKR r 0), AstTensor AstMethodLet PrimalSpan (TKR r 0)) -> AstTensor AstMethodLet PrimalSpan (TKR r 0)
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2F x w + y * w

fooNoGoAst :: forall r. (GoodScalar r, Differentiable r)
           => AstTensor AstMethodLet PrimalSpan (TKR r 1) -> AstTensor AstMethodLet PrimalSpan (TKR r 1)
fooNoGoAst v =
  let r = rsum0 v
  in rbuild1 3 (\ix ->
       barAst (rscalar 3.14, bar (rscalar 3.14, rindex v [(ix + (rprimalPart . rfloor) r) `minF` 2 `maxF` 0]))
       + ifF ( (&&*)
                    (rindex v (ix * 2 :.: ZIR) <=. rscalar 0)
                        -- @1 not required thanks to :.:; see below for @ and []
                    (rscalar 6 >. abs ix) )
                 r (rscalar 5 * r))
     / rslice 1 3 (rmap0N (\x -> ifF (x >. r) r x) v)
     * rbuild1 3 (const (rscalar 1))

testFooNoGoAst :: Assertion
testFooNoGoAst =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal RepN (TKR r 1) -> ADVal RepN (TKR r 1)
      f x = interpretAst (extendEnv @_ @_ @(TKR r 1)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (fooNoGoAst (AstVar (FTKR [5]) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (crev @_ @(TKR Double 1)
             f
             (ringestData1 [1.1, 2.2, 3.3, 4, 5]))

fooNoGo :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
        => target (TKR r 1) -> target (TKR r 1)
fooNoGo v =
  let r = rsum0 v
  in rbuild1 3 (\ix ->
       bar (rscalar 3.14, bar (rscalar 3.14, rindex v [(ix + (rprimalPart . rfloor) r) `minF` 2 `maxF` 0]))
       + ifF ((&&*) (rindex @target @r @1 v [ix * 2] <=. rscalar 0)
                    (rscalar 6 >. abs ix))
               r (rscalar 5 * r))
     / rslice 1 3 (rmap0N (\x -> ifF (x >. r) r x) v)
     * rbuild1 3 (const (rscalar 1))

testFooNoGo0 :: Assertion
testFooNoGo0 =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
   (rev' @Double @1 fooNoGo
         (FlipR $ OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall target r.
                  (ADReady target, GoodScalar r, Differentiable r)
               => target (TKR r 0) -> target (TKR r 1)
nestedBuildMap r =
  let w = rreplicate0N @target [4]
      v0' = rreplicate0N [177] r :: target (TKR r 1)
  in tlet v0' $ \v' ->
    let nestedMap x0 = tlet x0 $ \x -> rmap0N (x /) (w x)
        variableLengthBuild iy = rbuild1 7 (\ix -> rindex v' (ix + iy :.: ZIR))
        doublyBuild = rbuild1 5 (rminimum . variableLengthBuild)
    in rmap0N (\x0 -> tlet x0 $ \x -> x * rsum0
                           (rbuild1 3 (\ix -> bar (x, rindex v' [ix]))
                            + (tlet (nestedMap x) $ \x3 -> fooBuild1 x3)
                            / (tlet x $ \x4 -> fooMap1 x4))
              ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @Double @1 nestedBuildMap 1.1)

nestedSumBuild :: (ADReady target, GoodScalar r, Differentiable r)
               => target (TKR r 1) -> target (TKR r 1)
nestedSumBuild v0 = tlet v0 $ \v ->
 tlet (rsum (rbuild1 9 rfromIndex0)) (\tbtf ->
  (rbuild1 13 (\ix ->
    rsum (rbuild1 4 (\ix2 ->
      flip rindex [ix2]
        (tlet (rsum v) $ \tsumv -> rbuild1 5 (const tsumv)
         * rfromList
             [ rfromIndex0 ix
             , tbtf
             , rsum (rbuild1 6 (\_ -> rsum v))
             , rindex v [ix2]
             , rsum (rbuild1 3 (\ix7 ->
                 rsum (rreplicate 5 (rfromIndex0 ix7))))
             ]))))))
 + tlet (nestedBuildMap (rsum0 v)) (\nbmt -> (rbuild1 13 (\ix ->
     nbmt `rindex` [minF ix 4])))

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @Double @1 nestedSumBuild (FlipR $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall target r. (ADReady target, GoodScalar r)
                 => target (TKR r 1) -> target (TKR r 1)
nestedBuildIndex v =
  rbuild1 2 $ \ix2 -> rindex (rbuild1 3 $ \ix3 -> rindex (rbuild1 4 $ \ix4 -> rindex v (ix4 :.: ZIR)) [ix3]) (ix2 :.: ZIR)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @Double @1 nestedBuildIndex (FlipR $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( ADReady target, GoodScalar r, KnownNat n, Differentiable r )
  => target (TKR r n) -> target (TKR r n)
barRelu x = relu $ bar (x, relu x)

testBarReluDt :: Assertion
testBarReluDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @_ @(TKR Double 0)
           barRelu (rscalar 1.1) (rscalar 42.2))

testBarRelu :: Assertion
testBarRelu =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barRelu (FlipR $ OR.fromList [] [1.1]))

testBarRelu3 :: Assertion
testBarRelu3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barRelu (FlipR $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluMax0
  :: ( ADReady target, GoodScalar r, KnownNat n, RealFloatF (target (TKR r n)) )
  => target (TKR r n) -> target (TKR r n)
barReluMax0 x = reluMax $ bar (x, x)

barReluMax
  :: ( ADReady target, GoodScalar r, KnownNat n, RealFloatF (target (TKR r n)) )
  => target (TKR r n) -> target (TKR r n)
barReluMax x = reluMax $ bar (x, reluMax x)

testBarReluMaxDt :: Assertion
testBarReluMaxDt =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @_ @(TKR Double 0)
           barReluMax (rfromList0N [] [rscalar 1.1]) (rscalar 42.2))

testBarReluMax :: Assertion
testBarReluMax =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev' @Double @0 barReluMax (FlipR $ OR.fromList [] [1.1]))

testBarReluMax30 :: Assertion
testBarReluMax30 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [4.5309153191767395])
    (rev' @Double @1 barReluMax0 (FlipR $ OR.fromList [1] [1.1]))

testBarReluMax31 :: Assertion
testBarReluMax31 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barReluMax (FlipR $ OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

testBarReluMax3CFwd :: Assertion
testBarReluMax3CFwd =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (cfwd @_ @(TKR Double 3)
          barReluMax
                     (rconst $ Nested.rfromListPrimLinear (fromList [2, 1, 2]) [1.1, 2, 3, 4.2])
                     (ringestData [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

reluMaxS :: forall target sh r.
            (ADReady target, GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => target (TKS r sh) -> target (TKS r sh)
reluMaxS = smap0N (maxF (srepl 0))

barReluMaxS
  :: ( ADReady target, GoodScalar r, KnownShS sh, KnownNat (Rank sh)
     , RealFloatF (target (TKS r sh)) )
  => target (TKS r sh) -> target (TKS r sh)
barReluMaxS x = reluMaxS $ barF (x, reluMaxS x)

-- Previously the shape of FromListR[ZeroG] couldn't be determined
-- in buildDerivative, so this was needed. See below that it now works fine.
testBarReluMax3FwdS :: Assertion
testBarReluMax3FwdS =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @_ @(TKS Double '[2, 1, 2])
         barReluMaxS
         (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdFrom :: Assertion
testBarReluMax3FwdFrom =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @_ @(TKS Double '[2, 1, 2])
         (sfromR . barReluMax . rfromS)
         (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconst $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdR :: Assertion
testBarReluMax3FwdR =
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @_ @(TKR Double 3)
         barReluMax
         (ringestData [2, 1, 2] [1.1, 2, 3, 4.2])
         (ringestData [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

barReluAst
  :: forall n r.
     ( KnownNat n, ADReady (AstTensor AstMethodLet PrimalSpan), GoodScalar r
     , Differentiable r )
  => AstTensor AstMethodLet PrimalSpan (TKR r n) -> AstTensor AstMethodLet PrimalSpan (TKR r n)
barReluAst x = relu $ bar (x, relu x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal RepN (TKR r 0) -> ADVal RepN (TKR r 0)
      f x = interpretAst (extendEnv @_ @_ @(TKR r 0)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (barReluAst (AstVar (FTKR []) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @_ @(TKR Double 0)
               f (rscalar 1.1) (rscalar 42.2))

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal RepN (TKR r 1) -> ADVal RepN (TKR r 1)
      f x = interpretAst (extendEnv @_ @_ @(TKR r 1)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (barReluAst (AstVar (FTKR [5]) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @_ @(TKR Double 1)
             f (rfromList0N [5] [rscalar 1.1, rscalar 2.2, rscalar 3.3, rscalar 4, rscalar 5]))

konstReluAst
  :: forall r.
     (ADReady (AstTensor AstMethodLet PrimalSpan), GoodScalar r, Differentiable r)
  => AstTensor AstMethodLet PrimalSpan (TKR r 0) -> AstTensor AstMethodLet PrimalSpan (TKR r 0)
konstReluAst x = rsum0 $ relu $ rreplicate0N (7 :$: ZSR) x

testReplicateReluAst :: Assertion
testReplicateReluAst =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal RepN (TKR r 0) -> ADVal RepN (TKR r 0)
      f x = interpretAst (extendEnv @_ @_ @(TKR r 0)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (konstReluAst (AstVar (FTKR []) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [295.4])
       (crevDt @_ @(TKR Double 0)
               f (rscalar 1.1) (rscalar 42.2))

f1 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 0)
f1 = \arg -> rsum0 (rbuild1 10 (\i -> arg * rfromIndex0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    (rscalar 45.0)
    (rev @_ @(TKR Double 0) f1 (rscalar 1.1))

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    45.0
    (rev' @Double @0 f1 1.1)

f2 :: forall target r. (ADReady target, GoodScalar r)
   => target (TKR r 0) -> target (TKR r 0)
f2 = \arg ->
  let fun1 i = arg * rfromIndex0 i
      v1a = rsum0 (rbuild1 10 fun1)
      v1b = rsum0 (rbuild1 20 fun1)
      fun2 y i = y * rfromIndex0 @r i
      v2a = rsum0 (rbuild1 10 (fun2 arg))
      v2b = rsum0 (rbuild1 20 (fun2 (arg + rscalar 1)))
  in v1a + v1b + v2a + v2b

testF2 :: Assertion
testF2 =
  assertEqualUpToEpsilon 1e-10
    (rscalar 470)
    (rev @_ @(TKR Double 0) f2 (rscalar 1.1))

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    470
    (rev' @Double @0 f2 1.1)

testF2CFwd :: Assertion
testF2CFwd =
  assertEqualUpToEpsilon 1e-10
    (rscalar 47)
    (cfwd @_ @(TKR Double 0)
          f2 (rscalar 1.1) (rscalar 0.1))

testF2Fwd :: Assertion
testF2Fwd =
  assertEqualUpToEpsilon 1e-10
    (rscalar 47)
    (fwd @_ @(TKR Double 0)
         f2 (rscalar 1.1) (rscalar 0.1))

braidedBuilds :: forall target r.
                 (ADReady target, GoodScalar r, Differentiable r)
              => target (TKR r 0) -> target (TKR r 2)
braidedBuilds r =
  rbuild1 3 (\ix1 ->
    rbuild1 4 (\ix2 -> rindex (rfromList0N [4]
      [rfromIndex0 ix2, rscalar 7, r, rscalar (-0.2)]) (ix1 :.: ZIR)))

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @Double @2 braidedBuilds 3.4)

recycled :: (ADReady target, GoodScalar r, Differentiable r)
         => target (TKR r 0) -> target (TKR r 5)
recycled r =
  tlet (nestedSumBuild (rreplicate0N [7] r)) $ \nsb ->
    rbuild1 2 $ \_ -> rbuild1 4 $ \_ -> rbuild1 2 $ \_ -> rbuild1 3 $ const nsb

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilonShort 1e-6
    348356.9278600814
    (rev' @Double @5 recycled 0.0000001)

concatBuild :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 2)
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

concatBuild2 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild2 r =
  tlet (rfromList [r, 1, 2, 3, 4]) $ \a ->
    rbuild1 10 (\i -> ifF (i <. 5) (rindex a [i]) (rindex a [i - 5]))

testConcatBuild2 :: Assertion
testConcatBuild2 =
  assertEqualUpToEpsilon' 1e-10
    2.0
    (rev' @Double @1 concatBuild2 3.4)

concatBuild3 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild3 r =
  tlet (rfromList [r, 1, 2, 3, 4]) $ \a ->
    rbuild1 10 (\i -> ifF (i <. 5) (rindex a [i]) (rindex a [i - 5 + (1 `quotF` maxF 1 (i - 5))]))

testConcatBuild3 :: Assertion
testConcatBuild3 =
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' @Double @1 concatBuild3 3.4)

concatBuild4 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild4 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (4 + i)) :.: ZIR)) $ \a ->
    rappend a a

testConcatBuild4 :: Assertion
testConcatBuild4 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 concatBuild4 3.4)

concatBuild5 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild5 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (5 + i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotF` (5 + i)) :.: ZIR)))

testConcatBuild5 :: Assertion
testConcatBuild5 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 concatBuild5 3.4)

concatBuild6 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 2)
concatBuild6 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (4 + i)) :.: ZIR)) $ \a ->
    (rappend (rgather1 5 (rreplicate 1 r)
                         (\i -> (1 `quotF` (100 * maxF 1 (i - j))) :.: ZIR)) a))
                     (rreplicate 1 (rfromIndex0 j)))
            (rbuild1 13 (const r)))

testConcatBuild6 :: Assertion
testConcatBuild6 =
  assertEqualUpToEpsilon' 1e-10
    161
    (rev' @Double @2 concatBuild6 3.4)

concatBuild7 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild7 r =
  rbuild1 10 $ \j ->
    (rappend (rreplicate 5 r) (rgather1 5 (rreplicate 1 r)
                                 (\i -> (1 `quotF` maxF 1 (j - i)) :.: ZIR)))
     ! (j :.: ZIR)

testConcatBuild7 :: Assertion
testConcatBuild7 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 concatBuild7 3.4)

-- These tests show that term rewriting changes the value
-- of out-of-bounds indexing, e.g., of gather(replicate)
-- that reduces to a non-gather. Vectorization is not needed for that.
_concatBuild8 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
_concatBuild8 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (5 - i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotF` (5 - i)) :.: ZIR)))

_testConcatBuild8 :: Assertion
_testConcatBuild8 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 _concatBuild8 3.4)

_concatBuild9 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 2)
_concatBuild9 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (4 - i)) :.: ZIR)) $ \a ->
    (rappend (rgather1 5 (rreplicate 1 r)
                         (\i -> (1 `quotF` (100 * maxF 0 (i - j))) :.: ZIR)) a))
                     (rreplicate 1 (rfromIndex0 j)))
            (rbuild1 13 (const r)))

_testConcatBuild9 :: Assertion
_testConcatBuild9 =
  assertEqualUpToEpsilon' 1e-10
    161
    (rev' @Double @2 _concatBuild9 3.4)

concatBuild10 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 2)
concatBuild10 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (tlet (rgather1 5 (rreplicate 1 r)
                   (\_i -> 10000 :.: ZIR)) $ \a ->
    (rappend (rgather1 5 (rreplicate 1 r)
                         (\_i -> (-1) :.: ZIR)) a))
                     (rreplicate 1 (rfromIndex0 j)))
            (rbuild1 13 (const r)))

testConcatBuild10 :: Assertion
testConcatBuild10 =
  assertEqualUpToEpsilon' 1e-10
    91
    (rev' @Double @2 concatBuild10 3.4)

concatBuild11 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 1)
concatBuild11 r =
  rgather1 5 (rreplicate 1 r) (\_i -> (-1) :.: ZIR)

testConcatBuild11 :: Assertion
testConcatBuild11 =
  assertEqualUpToEpsilon' 1e-10
    0
    (rev' @Double @1 concatBuild11 3.4)

concatBuild12 :: (ADReady target, GoodScalar r) => target (TKR r 0) -> target (TKR r 0)
concatBuild12 r =
  rindex (rreplicate 1 r) ((-1) :.: ZIR)

testConcatBuild12 :: Assertion
testConcatBuild12 =
  assertEqualUpToEpsilon' 1e-10
    0
    (rev' @Double @0 concatBuild12 3.4)

emptyArgs :: forall target r. (ADReady target, GoodScalar r) -- , Differentiable r)
          => target (TKR r 1) -> target (TKR r 1)
emptyArgs _t =
  emptyTensor
--  - rfromList0N (rshape @target @r emptyTensor) []
  - rreshape @target @r @1 [0] emptyTensor
--  - rgather1 0 emptyTensor (:.: ZIR)
--  - rsum (rgather1 0 emptyTensor (const ZIR))
--  - rsum (rgather @target @r @2 (0 :$: 0 :$: ZSR) emptyTensor (const (0 :.: ZIR)))
--  - rsum (rgather @target @r @2 @0 @1 [0, 0] emptyTensor (const [0]))
  - rsum (rreshape @target @r @1 [0, 0] emptyTensor)
--  - rindex (rfromList0N (0 :$: 0 :$: ZSR) []) (42 :.: ZIR)
--  - rindex (rfromList0N (0 :$: rshape @target @r emptyTensor) []) (42 :.: ZIR)
--  - rsum (rfromList0N (0 :$: rshape @target @r emptyTensor) [])
--  * rsum (rfromList [rsum (rfromList0N (0 :$: rshape @target @r emptyTensor) [])])
--  * rflatten (rtr (rgather1 0 t (const ZIR)))
--  + rbuild1 0 (\i -> t ! [fromIntegral (rrank t) `quotF` i] / rfromIndex0 i)
  -- - rsum (rbuild @target @r @2 (0 :$: 0 :$: ZSR) (const 73))
  -- - rsum (rbuild @target @r @1 (0 :$: 0 :$: ZSR) (const $ rfromList []))
       -- these two fail and rightly so; TODO: make them fail earlier
 where
  emptyTensor :: target (TKR r 1)
  emptyTensor = rconst $ Nested.rfromListPrimLinear (fromList [0]) []

testEmptyArgs0 :: Assertion
testEmptyArgs0 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [0] [])
    (rev' @Double @1 emptyArgs (FlipR $ OR.fromList [0] []))

testEmptyArgs1 :: Assertion
testEmptyArgs1 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @Double @1 emptyArgs (FlipR $ OR.fromList [1] [0.24]))

testEmptyArgs4 :: Assertion
testEmptyArgs4 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1] [0])
    (rev' @Double @1
          (\t -> rbuild [2, 5, 11, 0] (const $ emptyArgs t))
          (FlipR $ OR.fromList [1] [0.24]))

filterPositiveFail :: ADReady target
                   => target (TKR Double 1) -> target (TKR Double 1)
filterPositiveFail v =
  let l = runravelToList v
      -- l2 = filter (\x -> x >= 0) l
      -- Could not deduce ‘Ord (target Double 0)’
      -- l2 = filter (\x -> x >=. 0) l
      -- Could not deduce ‘BoolOf target ~ Bool’
      l2 = take 3 l  -- the most I can do
  in rfromList $ NonEmpty.fromList l2

testFilterPositiveFail :: Assertion
testFilterPositiveFail =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5] [1.0,1.0,1.0,0.0,0.0])
    (rev' @Double @1
          filterPositiveFail
          (FlipR $ OR.fromList [5] [0.24, 52, -0.5, 0.33, 0.1]))

-- Catastrophic loss of sharing prevented.
fblowup :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
        => Int -> target (TKR r 1) -> target (TKR r 0)
fblowup k inputs =
  let blowup :: Int -> target (TKR r 0) -> target (TKR r 0)
      blowup 0 y = y - rfromIndex0 0
      blowup n y =
        let ysum = y + y - rfromIndex0 0
            yscaled = rscalar 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

fblowupLet :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
           => IntOf target -> Int -> target (TKR r 1) -> target (TKR r 0)
fblowupLet i k inputs =
  let blowup :: Int -> target (TKR r 0) -> target (TKR r 0)
      blowup 0 y = y - rfromIndex0 i
      blowup n y1 = tlet y1 $ \y ->
        let ysum = y + y - rfromIndex0 i
            yscaled = rscalar 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

-- Catastrophic loss of sharing prevented also with non-trivial multiplication.
fblowupMult :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
            => Int -> target (TKR r 1) -> target (TKR r 0)
fblowupMult k inputs =
  let blowup :: Int -> target (TKR r 0) -> target (TKR r 0)
      blowup 0 y = y
      blowup n y =
        let ysum = y + y * y / (y - rscalar 0.000000001)
            yscaled = sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 0
      y0 = (inputs ! [0 `remF` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall target r.
                  (ADReady target, GoodScalar r, Differentiable r)
               => IntOf target -> Int -> target (TKR r 1) -> target (TKR r 0)
fblowupMultLet i k inputs =
  let blowup :: Int -> target (TKR r 0) -> target (TKR r 0)
      blowup 0 y = y
      blowup n y1 = tlet y1 $ \y ->
        let ysum0 = y + y * y / (y - rscalar 0.000001)
            yscaled = tlet ysum0 $ \ysum ->
                        sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 i
      y0 = (inputs ! [i `remF` 2]) * (inputs ! [1])
  in blowup k y0

fblowupPP :: Assertion
fblowupPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupT = fblowup @(AstTensor AstMethodLet FullSpan) @Double 1
  let (artifactRev, _) = revArtifactAdapt True fblowupT (rreplicate0N [4] (rscalar 4))
  printArtifactSimple renames artifactRev
    @?= "\\x7 x1 -> tlet (v1 ! [0]) (\\x2 -> tlet (v1 ! [1]) (\\x3 -> tlet (v1 ! [0]) (\\x4 -> tlet (v1 ! [1]) (\\x5 -> tlet (0.499999985 * x7) (\\x8 -> rscatter [4] (recip x3 * x8) (\\[] -> [0]) + rscatter [4] ((negate x2 / (x3 * x3)) * x8) (\\[] -> [1]) + rscatter [4] (recip x5 * x8) (\\[] -> [0]) + rscatter [4] ((negate x4 / (x5 * x5)) * x8) (\\[] -> [1]))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x1 -> tlet (v1 ! [0]) (\\x2 -> tlet (v1 ! [1]) (\\x3 -> tlet (v1 ! [0]) (\\x4 -> tlet (v1 ! [1]) (\\x5 -> tlet ((x2 / x3 + x4 / x5) - 0.0) (\\x6 -> 0.499999985 * x6 - 0.0)))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupLetT = fblowupLet @(AstTensor AstMethodLet FullSpan) @Double 0 1
  let (artifactRev, _) = revArtifactAdapt True fblowupLetT (rreplicate0N [4] (rscalar 4))
  printArtifactSimple renames artifactRev
    @?= "\\x7 x1 -> tlet (v1 ! [0]) (\\x3 -> tlet (v1 ! [1]) (\\x4 -> tlet (0.499999985 * x7) (\\x8 -> tlet (x8 + x8) (\\x9 -> rscatter [4] (recip x4 * x9) (\\[] -> [0]) + rscatter [4] ((negate x3 / (x4 * x4)) * x9) (\\[] -> [1])))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x1 -> tlet (v1 ! [0]) (\\x3 -> tlet (v1 ! [1]) (\\x4 -> tlet (x3 / x4) (\\x5 -> tlet ((x5 + x5) - 0.0) (\\x6 -> 0.499999985 * x6 - 0.0))))"

-- TODO: should do 1000000 in a few seconds
blowupTests :: TestTree
blowupTests = testGroup "Catastrophic blowup avoidance tests"
  [ testCase "blowup 7" $ do
      assertEqualUpToEpsilon' 1e-5
        (OR.fromList [2] [0.3333332333333467,-0.22222215555556446])
        (rev' @Double @0 (fblowup 7) (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet 15" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333331833333646,-0.22222212222224305])
        (rev' @Double @0 (fblowupLet 0 15) (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet 1000" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [0.3333233334831686,-0.22221555565544573])
        (rev' @Double @0 (fblowupLet 0 1000) (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (OR.fromList [2] [33.332333348316844,-22.221555565544556])
        (rev' @Double @1
              (\intputs -> rbuild1 100 (\i -> fblowupLet i 1000 intputs))
              (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupMult 3" $ do
      assertEqualUpToEpsilon' 1e-5
        (OR.fromList [2] [2.999999730000007,1.9999998200000046])
        (rev' @Double @0 (fblowupMult 3) (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 5" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.9999995500000267,1.9999997000000178])
        (rev' @Double @0 (fblowupMultLet 0 5)
                                   (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet 50" $ do
      assertEqualUpToEpsilon' 1e-10
        (OR.fromList [2] [2.999995500001215,1.99999700000081])
        (rev' @Double @0 (fblowupMultLet 0 50)
                                   (FlipR $ OR.fromList [2] [2, 3]))
  , testCase "blowupMultLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (OR.fromList [2] [14.9999773958889,39.9999398380561])
        (rev' @Double @1
              (\intputs -> rbuild1 100 (\i -> fblowupMultLet i 50 intputs))
              (FlipR $ OR.fromList [2] [0.2, 0.3]))
  ]

concatBuild33 :: (ADReady target, GoodScalar r)
             => target (TKR r 1) -> target (TKR r 2)
concatBuild33 _r =
  rbuild1 5 (\i ->
    rbuild1 2 (\j -> rfromIndex0 (maxF j (i `quotF` (j + 1)))))

testConcatBuild3PP :: Assertion
testConcatBuild3PP = do
  resetVarCounter
  let renames = IM.empty
      t = concatBuild33 @(AstTensor AstMethodLet FullSpan) @Float
      (var3, ast3) = funToAst (FTKR [3]) $ t
  "\\" ++ printAstVarName renames var3
       ++ " -> " ++ printAstSimple renames ast3
    @?= "\\v1 -> rconstant (rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rslice 0 2 riota), quotF (rtranspose [1,0] (rreplicate 2 (rslice 0 5 riota))) (rreplicate 5 (rreplicate 2 1 + rslice 0 2 riota))])) (\\[i5, i4] -> [ifF (i4 >=. quotF i5 (1 + i4)) 0 1, i5, i4])))"

testConcatBuild3PP2 :: Assertion
testConcatBuild3PP2 = do
  resetVarCounter
  let renames = IM.empty
      t = concatBuild33 @(AstTensor AstMethodLet FullSpan) @Double
  let (artifactRev, _) =
        revArtifactAdapt True t (RepN $ FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [3] [0.651,0.14,0.3414])
  printArtifactSimple renames artifactRev
    @?= "\\m8 x1 -> rreshape [3] (rreplicate 3 0.0)"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x1 -> rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rconst (rfromListLinear [2] [0,1])), quotF (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [5] [0,1,2,3,4])))) (rreplicate 5 (rconst (rfromListLinear [2] [0,1]) + rreplicate 2 1))])) (\\[i6, i7] -> [ifF (i7 >=. quotF i6 (1 + i7)) 0 1, i6, i7]))"
  printArtifactPrimalSimple renames (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rconst (rfromListLinear [2] [0,1])), quotF (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [5] [0,1,2,3,4])))) (rreplicate 5 (rconst (rfromListLinear [2] [0,1]) + rreplicate 2 1))])) (\\[i6, i7] -> [ifF (i7 >=. quotF i6 (1 + i7)) 0 1, i6, i7]))"
