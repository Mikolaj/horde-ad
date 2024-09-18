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

import Data.Array.Mixed.Shape qualified as X
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAst, resetVarCounter)
import HordeAd.Core.IsPrimal (resetIdCounter)
import HordeAd.Core.TensorAst
import HordeAd.Internal.BackendOX (ORArray, OSArray)
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
  , testCase "2overleafInt64n" testOverleafInt64
  , testCase "2overleafCIntn" testOverleafCInt
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
    (rev' @Double @0 (let f :: forall f. ADReady f => f Double 0 -> f Double 0
                          f = const 3
                      in f) 42)

testZeroS :: Assertion
testZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (crev (let f :: ADVal OSArray Double '[0, 2, 4, 0, 1]
                 -> ADVal OSArray Double '[0, 2, 4, 0, 1]
               f = const (srepl 3)
           in f) (srepl 42))

testCFwdZeroS :: Assertion
testCFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f :: ADVal OSArray Double '[0, 2, 4, 0, 1]
                 -> ADVal OSArray Double '[0, 2, 4, 0, 1]
               f = const (srepl 3)
           in f) 42 41)

testFwdZeroS :: Assertion
testFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd (let f :: AstShaped FullSpan Double '[0, 2, 4, 0, 1]
                -> AstShaped FullSpan Double '[0, 2, 4, 0, 1]
              f = const (srepl 3)
          in f) (srepl 42) (srepl 41))

testZero2S :: Assertion
testZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[] knownShS [1])
    (crev @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42))

testCFwdZero2S :: Assertion
testCFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[] knownShS [41])
    (cfwd @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testFwdZero2S :: Assertion
testFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[] knownShS [41])
    (fwd @_ @(TKS Double '[])
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testZero3S :: Assertion
testZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.6174114266850617))
    (crev (\x -> barF @(ADVal OSArray Double '[33, 2]) (x, x)) (srepl 1))

testCFwdZero3S :: Assertion
testCFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (cfwd (\x -> barF @(ADVal OSArray Double '[33, 2]) (x, x)) (srepl 1) (srepl 1.1))

testFwdZero3S :: Assertion
testFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (fwd (\x -> barF @(AstShaped FullSpan Double '[33, 2]) (x, x)) (srepl 1) (srepl 1.1))

testZero4S :: Assertion
testZero4S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[] knownShS [0])
    (rev @(AstShaped FullSpan Double '[]) @(TKS Double '[])
         (let f = const (srepl 3)
          in f) (srepl 42))

testZero5S :: Assertion
testZero5S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[44] knownShS (replicate 44 1))
    (rev (let f :: a -> a
              f = id
          in f @(AstShaped FullSpan Double '[44])) (srepl 42))

testZero6S :: Assertion
testZero6S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] knownShS (replicate (product ([2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] :: [Int])) 3.6174114266850617))
    (rev @_ @(TKS Double '[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2])
         (\x -> barF (x, x)) (srepl 1))

testZero7S :: Assertion
testZero7S =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[] knownShS [0])
    (rev (const 3 :: AstShaped FullSpan Double '[] -> AstRanked FullSpan Double 0) (srepl 42))

testZero8 :: Assertion
testZero8 =
  assertEqualUpToEpsilon 1e-10
    (rfromList0N [] [0])
    (rev (const (sscalar 3) :: AstRanked FullSpan Double 0 -> AstShaped FullSpan Double '[]) 42)

testZero9S :: Assertion
testZero9S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (crev (let f :: ADVal ORArray Double 5
                 -> ADVal OSArray Double '[0, 2, 4, 0, 1]
               f = const (srepl 3)
           in f)
          (rreplicate0N [0, 2, 4, 0, 1] 42))

testCFwdZero9S :: Assertion
testCFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f :: ADVal ORArray Double 5
                 -> ADVal OSArray Double '[0, 2, 4, 0, 1]
               f = const (srepl 3)
           in f)
          (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testFwdZero9S :: Assertion
testFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd (let f :: AstRanked FullSpan Double 5
                -> AstShaped FullSpan Double '[0, 2, 4, 0, 1]
              f = const (srepl 3)
          in f)
         (rreplicate0N [0, 2, 4, 0, 1] 42) (rreplicate0N [0, 2, 4, 0, 1] 41))

testZero10S :: Assertion
testZero10S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (crev (let f = const (srepl 3) . snd
           in f :: ( ADVal ORArray Double 5
                   , ADVal OSArray Double '[0, 2, 4, 0, 1] )
                   -> ADVal OSArray Double '[0, 2, 4, 0, 1])
          (rreplicate0N [0, 2, 4, 0, 1] 42, srepl 21))

testCFwdZero10S :: Assertion
testCFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cfwd (let f = const (srepl 3) . snd
           in f :: ( ADVal ORArray Double 5
                   , ADVal OSArray Double '[0, 2, 4, 0, 1] )
                   -> ADVal OSArray Double '[0, 2, 4, 0, 1])
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero10S :: Assertion
testFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (fwd  (let f = const (srepl 3) . snd
           in f :: ( AstRanked FullSpan Double 5
                   , AstShaped FullSpan Double '[0, 2, 4, 0, 1] )
                   -> AstShaped FullSpan Double '[0, 2, 4, 0, 1])
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testZero11S :: Assertion
testZero11S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (crev (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal ORArray Double 5
                   , ADVal OSArray Double '[0, 2, 4, 0, 1] )
                   -> ADVal ORArray Double 5)
          (rreplicate0N [0, 2, 4, 0, 1] 42, srepl 21))

testCFwdZero11S :: Assertion
testCFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (cfwd (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( ADVal ORArray Double 5
                   , ADVal OSArray Double '[0, 2, 4, 0, 1] )
                   -> ADVal ORArray Double 5)
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero11S :: Assertion
testFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (fwd  (let f = const (rreplicate0N [0, 2, 4, 0, 1] 3) . snd
           in f :: ( AstRanked FullSpan Double 5
                   , AstShaped FullSpan Double '[0, 2, 4, 0, 1] )
                   -> AstRanked FullSpan Double 5)
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testPiecewiseLinearPP :: Assertion
testPiecewiseLinearPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: AstRanked FullSpan Double 0
         -> AstRanked FullSpan Double 0
      fT x = ifF (x >. 0) (2 * x) (5 * x)
      (artifactRev, _deltas) = revArtifactAdapt True fT 42
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x3 x5 -> let v4 = rscatter [2] x3 (\\[] -> [ifF (x5 >. 0.0) 0 1]) in [2.0 * v4 ! [0] + 5.0 * v4 ! [1]]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x6 -> rfromVector (fromList [2.0 * x6, 5.0 * x6]) ! [ifF (x6 >. 0.0) 0 1]"

testPiecewiseLinear2PP :: Assertion
testPiecewiseLinear2PP = do
  resetVarCounter
  let renames = IM.empty
      fT :: AstRanked FullSpan Double 0
         -> AstRanked FullSpan Double 0
      fT x = ifF (x >. 0) 2 5 * x
      (artifactRev, deltas) = revArtifactAdapt True fT 42
  printArtifactPretty renames artifactRev
    @?= "\\x4 x5 -> let x3 = ifF (x5 >. 0.0) 2.0 5.0 in [x3 * x4]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\x6 -> let x3 = ifF (x6 >. 0.0) 2.0 5.0 in x3 * x6"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x4 x7 -> [ifF (x7 >. 0.0) 2.0 5.0 * x4]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x8 -> ifF (x8 >. 0.0) 2.0 5.0 * x8"
  show deltas
    @?= "ShareR 100000005 (ScaleR (AstRaw {unAstRaw = AstShare (AstVarId 100000003) (AstCond (AstRel GtOp (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 0) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [2.0])) (AstConst (rfromListLinear [] [5.0])))}) (InputG (FTKR []) (InputId 0)))"

overleaf :: forall r ranked. (RankedTensor ranked, GoodScalar r)
         => ranked r 1 -> ranked r 0
overleaf v = let wrap i = i `remF` fromIntegral (rlength v)
             in rsum (rbuild @ranked @r @1 [50] (\[i] -> rindex v [wrap i]))

testOverleaf :: Assertion
testOverleaf =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList @Double @1 [28] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @0 overleaf (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafInt64 :: Assertion
testOverleafInt64 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (crev @_ @(TKR Int64 0)
          overleaf (ringestData [28] [0 .. 27]))

testOverleafCInt :: Assertion
testOverleafCInt =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
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
    (let f :: forall f. ADReady f => f Float 1 -> f Float 0
         f = rfromIntegral . overleaf @CInt . rfloor
     in rev' @Float @0 f (FlipR $ OR.fromList [28] [0 .. 27]))

testOverleafPP :: Assertion
testOverleafPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v"), (2, "i")]
      fT :: AstRanked FullSpan Double 1
         -> AstRanked FullSpan Double 0
      fT = overleaf
      (var3, ast3) = funToAst (FTKR [28]) $ unAstRanked . fT . AstRanked
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v -> rsum (rgather [50] v (\\[i] -> [remF i 28]))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True fT (ringestData [28] [0 .. 27])
  printArtifactPretty renames artifactRev
    @?= "\\x5 v7 -> [rscatter [28] (rreplicate 50 x5) (\\[i6] -> [remF i6 28])]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v8 -> rsum (rgather [50] v8 (\\[i4] -> [remF i4 28]))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x5 v9 -> [rscatter [28] (rreplicate 50 x5) (\\[i6] -> [remF i6 28])]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v10 -> rsum (rgather [50] v10 (\\[i4] -> [remF i4 28]))"
  show deltas
    @?= "ShareR 100000002 (SumR (ShareR 100000001 (GatherR [50] (InputG (FTKR [28]) (InputId 0)) <function>)))"

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
         (srepl 1.1 :: OSArray Double '[3, 534, 3], srepl 2.2, srepl 3.3))

testFooSBoth :: Assertion
testFooSBoth = do
  assertEqualUpToEpsilon 1e-10
    (srepl 2.439628436155373, srepl (-1.9533749), srepl 0.9654825479484146)
    (rev @_ @(TKS Float '[3, 534, 3])
         (scast . fooF . (\(d, f, d2) -> (d, scast f, d2)))
         ( srepl 1.1 :: OSArray Double '[3, 534, 3]
         , srepl 2.2 :: OSArray Float '[3, 534, 3]
         , srepl 3.3 ))

testFooBoth :: Assertion
testFooBoth = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.439628436155373, rscalar (-1.9533749), rscalar 0.9654825479484146)
    (rev @_ @(TKR Float 0)
         (rcast . foo . (\(d, f, d2) -> (d, rcast f, d2)))
         ( rscalar 1.1 :: ORArray Double 0
         , rscalar 2.2 :: ORArray Float 0
         , rscalar 3.3 ))

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let renames = IM.fromList [(2, "x"), (3, "y"), (4, "z")]
      fooT = foo @(AstRanked FullSpan Double 0)
      foo3 x = fooT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR) $ unAstRanked . foo3 . AstRanked
  "\\" ++ printAstVarName IM.empty var3
       ++ " -> " ++ printAstSimple IM.empty (AstRanked ast3)
    @?= "\\x1 -> atan2F x1 (x1 * sin x1) + x1 * (x1 * sin x1)"
  resetVarCounter
  let (artifactRev, _) = revArtifactAdapt True fooT (4, 5, 6)
  printArtifactSimple renames artifactRev
    @?= "\\x22 x25 x26 x27 -> dlet (sin x26) (\\x10 -> dlet (x25 * x10) (\\x12 -> dlet (recip (x27 * x27 + x12 * x12)) (\\x13 -> dlet (sin x26) (\\x19 -> dlet (x25 * x19) (\\x21 -> dlet (x27 * x22) (\\x23 -> dlet ((negate x27 * x13) * x22) (\\x24 -> dmkHVector (fromList [DynamicRanked (x10 * x24 + x19 * x23), DynamicRanked (cos x26 * (x25 * x24) + cos x26 * (x25 * x23)), DynamicRanked ((x12 * x13) * x22 + x21 * x22)]))))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x64 x65 x66 -> rlet (sin x65) (\\x10 -> rlet (x64 * x10) (\\x12 -> rlet (sin x65) (\\x19 -> rlet (x64 * x19) (\\x21 -> atan2F x66 x12 + x66 * x21))))"

fooLet :: forall ranked r n.
          ( RealFloatF (ranked r n)
          , LetTensor ranked (ShapedOf ranked)
          , KnownNat n, GoodScalar r )
       => (ranked r n, ranked r n, ranked r n) -> ranked r n
fooLet (x, y, z) =
  let w0 = x * sin y
  in rlet w0 $ \w ->
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
      fooLetT = fooLet @(AstRanked FullSpan) @Double
      fooLet3 x = fooLetT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR) $ unAstRanked . fooLet3 . AstRanked
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\x1 -> rlet (x1 * sin x1) (\\x2 -> atan2F x1 x2 + x1 * x2)"
  resetVarCounter
  let (artifactRev, _)= revArtifactAdapt True fooLetT (4, 5, 6)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x17 x43 x44 x45 -> let x10 = sin x44 ; x11 = x43 * x10 ; x14 = recip (x45 * x45 + x11 * x11) ; x18 = (negate x45 * x14) * x17 + x45 * x17 in [x10 * x18, cos x44 * (x43 * x18), (x11 * x14) * x17 + x11 * x17]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x70 x71 x72 -> let x11 = x70 * sin x71 in atan2F x72 x11 + x72 * x11"

shapedListProd :: (ShapedTensor shaped, GoodScalar r)
               => [shaped r '[]] -> shaped r '[]
shapedListProd = foldl1' (*)

testListProdPP :: Assertion
testListProdPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstShaped FullSpan Double '[]] -> AstShaped FullSpan Double '[]
      fT = shapedListProd
  let (artifactRev, _deltas)= revArtifactAdapt True fT [srepl 1, srepl 2, srepl 3, srepl 4]
  printArtifactSimple renames artifactRev
    @?= "\\x16 x19 x20 x21 x22 -> dlet (x19 * x20) (\\x11 -> dlet (x11 * x21) (\\x14 -> dlet (x22 * x16) (\\x17 -> dlet (x21 * x17) (\\x18 -> dmkHVector (fromList [DynamicShaped (x20 * x18), DynamicShaped (x19 * x18), DynamicShaped (x11 * x17), DynamicShaped (x14 * x16)])))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x55 x56 x57 x58 -> slet (x55 * x56) (\\x11 -> slet (x11 * x57) (\\x14 -> x14 * x58))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x16 x123 x124 x125 x126 -> let x11 = x123 * x124 ; x17 = x126 * x16 ; x18 = x125 * x17 in [x124 * x18, x123 * x18, x11 * x17, (x11 * x125) * x16]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x159 x160 x161 x162 -> ((x159 * x160) * x161) * x162"

rankedListProdr :: (RankedTensor ranked, GoodScalar r)
                => [ranked r 0] -> ranked r 0
rankedListProdr = foldr1 (*)

testListProdrPP :: Assertion
testListProdrPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListProdr
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x16 x51 x52 x53 x54 -> let x13 = x53 * x54 ; x17 = x51 * x16 ; x18 = x52 * x17 in [(x52 * x13) * x16, x13 * x17, x54 * x18, x53 * x18]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x87 x88 x89 x90 -> x87 * (x88 * (x89 * x90))"

testListProdrLongPP :: Assertion
testListProdrLongPP = do
  resetVarCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListProdr
  let (artifactRev, _)=
        revArtifactAdapt True fT [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  printArtifactSimple renames artifactRev
    @?= "\\x52 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 -> dlet (x75 * x76) (\\x31 -> dlet (x74 * x31) (\\x33 -> dlet (x73 * x33) (\\x35 -> dlet (x72 * x35) (\\x37 -> dlet (x71 * x37) (\\x39 -> dlet (x70 * x39) (\\x41 -> dlet (x69 * x41) (\\x43 -> dlet (x68 * x43) (\\x45 -> dlet (x67 * x45) (\\x47 -> dlet (x66 * x47) (\\x49 -> dlet (x65 * x49) (\\x51 -> dlet (x64 * x52) (\\x53 -> dlet (x65 * x53) (\\x54 -> dlet (x66 * x54) (\\x55 -> dlet (x67 * x55) (\\x56 -> dlet (x68 * x56) (\\x57 -> dlet (x69 * x57) (\\x58 -> dlet (x70 * x58) (\\x59 -> dlet (x71 * x59) (\\x60 -> dlet (x72 * x60) (\\x61 -> dlet (x73 * x61) (\\x62 -> dlet (x74 * x62) (\\x63 -> dmkHVector (fromList [DynamicRanked (x51 * x52), DynamicRanked (x49 * x53), DynamicRanked (x47 * x54), DynamicRanked (x45 * x55), DynamicRanked (x43 * x56), DynamicRanked (x41 * x57), DynamicRanked (x39 * x58), DynamicRanked (x37 * x59), DynamicRanked (x35 * x60), DynamicRanked (x33 * x61), DynamicRanked (x31 * x62), DynamicRanked (x76 * x63), DynamicRanked (x75 * x63)])))))))))))))))))))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\x415 x416 x417 x418 x419 x420 x421 x422 x423 x424 x425 x426 x427 -> rlet (x426 * x427) (\\x31 -> rlet (x425 * x31) (\\x33 -> rlet (x424 * x33) (\\x35 -> rlet (x423 * x35) (\\x37 -> rlet (x422 * x37) (\\x39 -> rlet (x421 * x39) (\\x41 -> rlet (x420 * x41) (\\x43 -> rlet (x419 * x43) (\\x45 -> rlet (x418 * x45) (\\x47 -> rlet (x417 * x47) (\\x49 -> rlet (x416 * x49) (\\x51 -> x415 * x51)))))))))))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x52 x1104 x1105 x1106 x1107 x1108 x1109 x1110 x1111 x1112 x1113 x1114 x1115 x1116 -> let x31 = x1115 * x1116 ; x33 = x1114 * x31 ; x35 = x1113 * x33 ; x37 = x1112 * x35 ; x39 = x1111 * x37 ; x41 = x1110 * x39 ; x43 = x1109 * x41 ; x45 = x1108 * x43 ; x47 = x1107 * x45 ; x49 = x1106 * x47 ; x53 = x1104 * x52 ; x54 = x1105 * x53 ; x55 = x1106 * x54 ; x56 = x1107 * x55 ; x57 = x1108 * x56 ; x58 = x1109 * x57 ; x59 = x1110 * x58 ; x60 = x1111 * x59 ; x61 = x1112 * x60 ; x62 = x1113 * x61 ; x63 = x1114 * x62 in [(x1105 * x49) * x52, x49 * x53, x47 * x54, x45 * x55, x43 * x56, x41 * x57, x39 * x58, x37 * x59, x35 * x60, x33 * x61, x31 * x62, x1116 * x63, x1115 * x63]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x1455 x1456 x1457 x1458 x1459 x1460 x1461 x1462 x1463 x1464 x1465 x1466 x1467 -> x1455 * (x1456 * (x1457 * (x1458 * (x1459 * (x1460 * (x1461 * (x1462 * (x1463 * (x1464 * (x1465 * (x1466 * x1467)))))))))))"

testListProd :: Assertion
testListProd = do
  assertEqualUpToEpsilon 1e-10
    [srepl 24, srepl 12, srepl 8, srepl 6]
    (rev @_ @(TKS Double '[])
         shapedListProd [srepl 1, srepl 2, srepl 3, srepl 4])

testListProdr :: Assertion
testListProdr = do
  assertEqualUpToEpsilon 1e-10
    [24, 12, 8, 6]
    (rev @_ @(TKR Double 0)
         rankedListProdr [1, 2, 3, 4])

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
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x10 x27 x28 x29 x30 -> [x10, x10, x10, x10]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x47 x48 x49 x50 -> x47 + x48 + x49 + x50"
  show deltas
    @?= "ShareR 100000003 (AddR (InputG (FTKR []) (InputId 0)) (ShareR 100000002 (AddR (InputG (FTKR []) (InputId 1)) (ShareR 100000001 (AddR (InputG (FTKR []) (InputId 2)) (InputG (FTKR []) (InputId 3)))))))"

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
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x13 x32 x33 x34 x35 -> let x14 = 2.0 * x13 ; x15 = 2.0 * x14 in [x13, x14, x15, 2.0 * x15]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x52 x53 x54 x55 -> x52 + 2.0 * (x53 + 2.0 * (x54 + 2.0 * x55))"

rankedListSum22r :: (RankedTensor ranked, GoodScalar r)
                 => [ranked r 0] -> ranked r 0
rankedListSum22r = foldr1 (\x y -> 2 * x + 2 * y)

testListSum22rPP :: Assertion
testListSum22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum22r
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x16 x35 x36 x37 x38 -> let x17 = 2.0 * x16 ; x18 = 2.0 * x17 in [2.0 * x16, 2.0 * x17, 2.0 * x18, 2.0 * x18]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x55 x56 x57 x58 -> 2.0 * x55 + 2.0 * (2.0 * x56 + 2.0 * (2.0 * x57 + 2.0 * x58))"

-- Note how this rlet did not change anything, in particular the sharing.
rankedListSumk22r :: ( RankedTensor ranked, LetTensor ranked (ShapedOf ranked)
                     , GoodScalar r )
                 => [ranked r 0] -> ranked r 0
rankedListSumk22r = foldr1 (\x y -> rlet 2 (\k -> k * x + k * y))

testListSumk22rPP :: Assertion
testListSumk22rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSumk22r
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x16 x35 x36 x37 x38 -> let x17 = 2.0 * x16 ; x18 = 2.0 * x17 in [2.0 * x16, 2.0 * x17, 2.0 * x18, 2.0 * x18]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x55 x56 x57 x58 -> 2.0 * x55 + 2.0 * (2.0 * x56 + 2.0 * (2.0 * x57 + 2.0 * x58))"

rankedListSum2xpyr :: (RankedTensor ranked, GoodScalar r)
                   => [ranked r 0] -> ranked r 0
rankedListSum2xpyr = foldr1 (\x y -> 2 * (x + y))

testListSum2xpyrPP :: Assertion
testListSum2xpyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum2xpyr
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x13 x33 x34 x35 x36 -> let x14 = 2.0 * x13 ; x15 = 2.0 * x14 ; x16 = 2.0 * x15 in [x14, x15, x16, x16]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x53 x54 x55 x56 -> 2.0 * (x53 + 2.0 * (x54 + 2.0 * (x55 + x56)))"

rankedListSum2xyr :: (RankedTensor ranked, GoodScalar r)
                  => [ranked r 0] -> ranked r 0
rankedListSum2xyr = foldr1 (\x y -> 2 * (x * y))

testListSum2xyrPP :: Assertion
testListSum2xyrPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum2xyr
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x19 x55 x56 x57 x58 -> let x14 = 2.0 * (x57 * x58) ; x20 = 2.0 * x19 ; x21 = 2.0 * (x55 * x20) ; x22 = 2.0 * (x56 * x21) in [(2.0 * (x56 * x14)) * x20, x14 * x21, x58 * x22, x57 * x22]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x91 x92 x93 x94 -> 2.0 * (x91 * (2.0 * (x92 * (2.0 * (x93 * x94)))))"

ranked2xy :: (RankedTensor ranked, GoodScalar r)
          => (ranked r 0, ranked r 0) -> ranked r 0
ranked2xy = \(x, y) -> rscalar 2 * x * y

test2xyPP :: Assertion
test2xyPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstRanked FullSpan Double 0, AstRanked FullSpan Double 0)
         -> AstRanked FullSpan Double 0
      fT = ranked2xy
  let (artifactRev, _deltas)= revArtifactAdapt True fT (4, 5)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x9 x18 x19 -> [2.0 * (x19 * x9), (2.0 * x18) * x9]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x28 x29 -> (2.0 * x28) * x29"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum23r :: (RankedTensor ranked, GoodScalar r)
                 => [ranked r 0] -> ranked r 0
rankedListSum23r = foldr1 (\x y -> rscalar 2 * x + rscalar 3 * y)

testListSum23rPP :: Assertion
testListSum23rPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: [AstRanked FullSpan Double 0] -> AstRanked FullSpan Double 0
      fT = rankedListSum23r
  let (artifactRev, _deltas)= revArtifactAdapt True fT [1, 2, 3, 4]
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x16 x35 x36 x37 x38 -> let x17 = 3.0 * x16 ; x18 = 3.0 * x17 in [2.0 * x16, 2.0 * x17, 2.0 * x18, 3.0 * x18]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x55 x56 x57 x58 -> 2.0 * x55 + 3.0 * (2.0 * x56 + 3.0 * (2.0 * x57 + 3.0 * x58))"

ranked23 :: (RankedTensor ranked, GoodScalar r)
         => (ranked r 0, ranked r 0) -> ranked r 0
ranked23 = \(x, y) -> rscalar 2 * x + rscalar 3 * y

test23PP :: Assertion
test23PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      fT :: (AstRanked FullSpan Double 0, AstRanked FullSpan Double 0)
         -> AstRanked FullSpan Double 0
      fT = ranked23
  let (artifactRev, _deltas)= revArtifactAdapt True fT (4, 5)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x8 x13 x14 -> [2.0 * x8, 3.0 * x8]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\x19 x20 -> 2.0 * x19 + 3.0 * x20"

reluPrimal
  :: forall ranked n r.
     (ADReady ranked, GoodScalar r, KnownNat n, Differentiable r)
  => ranked r n -> ranked r n
reluPrimal v =
  let oneIfGtZero = rmap0N (\x -> ifF (x <=. 0) (rscalar 0.0) (rscalar 1.0))
                           (rprimalPart v)
  in scale oneIfGtZero v

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "m1"), (2, "i2")]
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = reluPrimal
      (var3, ast3) = funToAst (FTKR [3, 4]) $ unAstRanked . reluT . AstRanked
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m9 m10 -> [rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i6, i7] -> [ifF (m10 ! [i6, i7] <=. 0.0) 0 1]) * m9]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m11 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i6, i7] -> [ifF (m11 ! [i6, i7] <=. 0.0) 0 1]) * m11"
  show deltas
    @?= "ShareR 100000003 (ScaleR (AstRaw {unAstRaw = AstShare (AstVarId 100000008) (AstGather [3,4] (AstConst (rfromListLinear [2] [0.0,1.0])) ([AstVarId 100000006,AstVarId 100000007],[AstCond (AstRel LeqOp (AstIndex (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 0) [AstVar (FTKR []) (AstVarId 100000006),AstVar (FTKR []) (AstVarId 100000007)]) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [0])) (AstConst (rfromListLinear [] [1]))]))}) (InputG (FTKR [3,4]) (InputId 0)))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = reluPrimal (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> unAstRanked $ reluT2 (AstRanked t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v1 -> rconstant (rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i2] -> [ifF (rprimalPart v1 ! [i2] * 7.0 <=. 0.0) 0 1])) * (v1 * rconstant (rreplicate 5 7.0))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v16 v34 x35 -> let v17 = rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifF (v34 ! [i5] * x35 <=. 0.0) 0 1]) * v16 in [rreplicate 5 x35 * v17, rsum (v34 * v17)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v52 x53 -> rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifF (v52 ! [i5] * x53 <=. 0.0) 0 1]) * (v52 * rreplicate 5 x53)"

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
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = relu
      (var3, ast3) = funToAst (FTKR [3, 4]) $ unAstRanked . reluT . AstRanked
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\m1 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifF (rprimalPart m1 ! [i4, i3] <=. 0.0) 0 1])) * m1"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m9 m10 -> [rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i6, i7] -> [ifF (m10 ! [i6, i7] <=. 0.0) 0 1]) * m9]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m11 -> rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i6, i7] -> [ifF (m11 ! [i6, i7] <=. 0.0) 0 1]) * m11"
  show deltas
    @?= "ShareR 100000003 (ScaleR (AstRaw {unAstRaw = AstShare (AstVarId 100000008) (AstGather [3,4] (AstConst (rfromListLinear [2] [0.0,1.0])) ([AstVarId 100000006,AstVarId 100000007],[AstCond (AstRel LeqOp (AstIndex (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 0) [AstVar (FTKR []) (AstVarId 100000006),AstVar (FTKR []) (AstVarId 100000007)]) (AstConst (rfromListLinear [] [0.0]))) (AstConst (rfromListLinear [] [0])) (AstConst (rfromListLinear [] [1]))]))}) (InputG (FTKR [3,4]) (InputId 0)))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = relu (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> unAstRanked $ reluT2 (AstRanked t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v1 -> rlet (v1 * rconstant (rreplicate 5 7.0)) (\\i2 -> rconstant (rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifF (rprimalPart i2 ! [i3] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v13 v23 x24 -> let v14 = rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i11] -> [ifF (v23 ! [i11] * x24 <=. 0.0) 0 1]) * v13 in [rreplicate 5 x24 * v14, rsum (v23 * v14)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v33 x34 -> let v10 = v33 * rreplicate 5 x34 in rgather [5] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i11] -> [ifF (v10 ! [i11] <=. 0.0) 0 1]) * v10"

testReluSimplerPP3 :: Assertion
testReluSimplerPP3 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
      (var3, ast3) = funToAst (FTKR [3, 4]) (\t -> unAstRanked $ reluT2 (AstRanked t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v1 -> rlet (v1 * rconstant (rreplicate 3 (rreplicate 4 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [3, 4] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m16 m26 x27 -> let m17 = rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i13, i14] -> [ifF (m26 ! [i13, i14] * x27 <=. 0.0) 0 1]) * m16 in [rreplicate 3 (rreplicate 4 x27) * m17, rsum (rsum (m26 * m17))]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m36 x37 -> let m12 = m36 * rreplicate 3 (rreplicate 4 x37) in rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i13, i14] -> [ifF (m12 ! [i13, i14] <=. 0.0) 0 1]) * m12"

testReluSimpler3 :: Assertion
testReluSimpler3 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
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
      reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
      (var3, ast3) = funToAst (FTKR [3, 4]) (\t -> unAstRanked $ reluT2 (AstRanked t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v1 -> rlet (v1 * rconstant (rreshape [3,4] (rreplicate 12 7.0))) (\\i2 -> rconstant (rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifF (rprimalPart i2 ! [i5, i4] <=. 0.0) 0 1])) * i2)"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [3, 4] 128, 42)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m16 m30 x31 -> let m17 = rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i13, i14] -> [ifF (m30 ! [i13, i14] * x31 <=. 0.0) 0 1]) * m16 in [rreplicate 3 (rreplicate 4 x31) * m17, rsum (rreshape [12] m30 * rreshape [12] m17)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m44 x45 -> let m12 = m44 * rreplicate 3 (rreplicate 4 x45) in rgather [3,4] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i13, i14] -> [ifF (m12 ! [i13, i14] <=. 0.0) 0 1]) * m12"

testReluSimpler4 :: Assertion
testReluSimpler4 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (rev reluT2 (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testReluSimplerPP4S :: Assertion
testReluSimplerPP4S = do
  resetVarCounter
  let renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstShaped FullSpan Float '[3, 4], AstShaped FullSpan Float '[])
             -> AstShaped FullSpan Float '[3, 4]
      reluT2 (t, r) = reluS (t * sreplicate0N r)
      (var3, ast3) = funToAst FTKS (\t -> unAstShaped $ reluT2 (AstShaped t, srepl 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimpleS renamesNull (AstShaped ast3)
    @?= "\\v1 -> slet (v1 * sconstant (sreshape (sreplicate 7.0))) (\\i2 -> sconstant (sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i5, i4] -> [i5, ifF (sprimalPart i2 !$ [i5, i4] <=. 0.0) 0 1])) * i2)"

testReluSimplerPP4S2 :: Assertion
testReluSimplerPP4S2 = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      reluT2 :: (AstShaped FullSpan Double '[3, 4], AstShaped FullSpan Double '[])
             -> AstShaped FullSpan Double '[3, 4]
      -- This is tweaked compared to above to avoid test artifacts coming
      -- from counter resets, which are inherently unsafe (cse, etc.).
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (srepl 128, srepl 42)
  printArtifactPretty renames artifactRev
    @?= "\\m16 m18 x19 -> let m11 = sreshape (sreplicate x19) ; m12 = m18 * m11 ; m15 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i13, i14] -> [i13, ifF (m12 !$ [i13, i14] <=. 0.0) 0 1]) ; m17 = m15 * m16 in [m11 * m17, ssum (sreshape m18 * sreshape m17)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m28 x29 -> let m11 = sreshape (sreplicate x29) ; m12 = m28 * m11 ; m15 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i13, i14] -> [i13, ifF (m12 !$ [i13, i14] <=. 0.0) 0 1]) in m15 * m12"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m16 m46 x47 -> let m11 = sreshape (sreplicate x47) ; m17 = sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i13, i14] -> [i13, ifF (m46 !$ [i13, i14] * m11 !$ [i13, i14] <=. 0.0) 0 1]) * m16 in [m11 * m17, ssum (sreshape m46 * sreshape m17)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m56 x57 -> let m12 = m56 * sreshape (sreplicate x57) in sgather (sreplicate (sconst @[2] (sfromListLinear [2] [0.0,1.0]))) (\\[i13, i14] -> [i13, ifF (m12 !$ [i13, i14] <=. 0.0) 0 1]) * m12"

testReluSimpler4S :: Assertion
testReluSimpler4S = do
  let reluT2 :: (AstShaped FullSpan Double '[3, 4], AstShaped FullSpan Double '[])
             -> AstShaped FullSpan Double '[3, 4]
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  assertEqualUpToEpsilon 1e-10
    ( sconst
      $ Nested.Internal.sfromListPrimLinear @_ @'[3, 4] knownShS [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , srepl 57.1 )
    (rev reluT2 (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[3, 4] knownShS [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], srepl 7))

reluMax :: forall ranked n r. (ADReady ranked, GoodScalar r, KnownNat n)
        => ranked r n -> ranked r n
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
      reluT :: AstRanked FullSpan Double 2 -> AstRanked FullSpan Double 2
      reluT = reluMax
      (var3, ast3) = funToAst (FTKR [3, 4]) $ unAstRanked . reluT . AstRanked
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\m1 -> rgather [3,4] (rfromVector (fromList [rconstant (rreplicate 3 (rreplicate 4 0.0)), m1])) (\\[i5, i4] -> [ifF (0.0 >=. rprimalPart m1 ! [i5, i4]) 0 1, i5, i4])"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactAdapt True reluT (rreplicate0N [3, 4] 4)
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m9 m13 -> [rscatter [2,3,4] m9 (\\[i10, i11] -> [ifF (0.0 >=. m13 ! [i10, i11]) 0 1, i10, i11]) ! [1]]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m14 -> rgather [3,4] (rfromVector (fromList [rreplicate 3 (rreplicate 4 0.0), m14])) (\\[i7, i8] -> [ifF (0.0 >=. m14 ! [i7, i8]) 0 1, i7, i8])"
  show deltas
    @?= "ShareR 100000005 (GatherR [3,4] (ShareR 100000003 (FromVectorR [ZeroR [3,4],InputG (FTKR [3,4]) (InputId 0)])) <function>)"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let renames = IM.empty
      renamesNull = IM.fromList [(1, "v1"), (2, "i2")]
      reluT2 :: (AstRanked FullSpan Double 1, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 1
      reluT2 (t, r) = reluMax (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5]) (\t -> unAstRanked $ reluT2 (AstRanked t, 7))
  "\\" ++ printAstVarName renamesNull var3
       ++ " -> " ++ printAstSimple renamesNull (AstRanked ast3)
    @?= "\\v1 -> rgather [5] (rfromVector (fromList [rconstant (rreplicate 5 0.0), v1 * rconstant (rreplicate 5 7.0)])) (\\[i3] -> [ifF (0.0 >=. rprimalPart v1 ! [i3] * 7.0) 0 1, i3])"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactAdapt True reluT2 (rreplicate0N [5] 128, 42)
  printArtifactPretty renames artifactRev
    @?= "\\v15 v23 x24 -> let m21 = rscatter [2,5] v15 (\\[i16] -> [let x19 = v23 ! [i16] in ifF (0.0 >=. x19 * x24) 0 1, i16]) ; v22 = m21 ! [1] in [rreplicate 5 x24 * v22, rsum (v23 * v22)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v41 x42 -> rgather [5] (rfromVector (fromList [rreplicate 5 0.0, v41 * rreplicate 5 x42])) (\\[i10] -> [let x13 = v41 ! [i10] in ifF (0.0 >=. x13 * x42) 0 1, i10])"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v15 v75 x76 -> let v22 = rscatter [2,5] v15 (\\[i16] -> [ifF (0.0 >=. v75 ! [i16] * x76) 0 1, i16]) ! [1] in [rreplicate 5 x76 * v22, rsum (v75 * v22)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\v93 x94 -> rgather [5] (rfromVector (fromList [rreplicate 5 0.0, v93 * rreplicate 5 x94])) (\\[i10] -> [ifF (0.0 >=. v93 ! [i10] * x94) 0 1, i10])"

testReluMax3 :: Assertion
testReluMax3 = do
  let reluT2 :: (AstRanked FullSpan Double 2, AstRanked FullSpan Double 0)
             -> AstRanked FullSpan Double 2
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
        revArtifactAdapt True (uncurry (rdot0 @(AstRanked FullSpan) @Double @1))
                 ( ringestData [3] [1 .. 3]
                 , ringestData [3] [4 .. 6] )
  printArtifactPretty renames artifactRev
    @?= "\\x8 v9 v10 -> [v10 * rreshape [3] (rreplicate 3 x8), v9 * rreshape [3] (rreplicate 3 x8)]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\v19 v20 -> rsum (v19 * v20)"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter >> resetIdCounter
  let renames = IM.empty
      (artifactRev, deltas) =
        revArtifactAdapt True (uncurry (rdot0 @(AstRanked FullSpan) @Double @2))
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [2,3] [7 .. 12] )
  printArtifactPretty renames artifactRev
    @?= "\\x8 m9 m10 -> let v6 = rreshape [6] m9 ; v7 = rreshape [6] m10 in [rreshape [2,3] (v7 * rreshape [6] (rreplicate 6 x8)), rreshape [2,3] (v6 * rreshape [6] (rreplicate 6 x8))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m19 m20 -> let v6 = rreshape [6] m19 ; v7 = rreshape [6] m20 in rsum (rreshape [6] (v6 * v7))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\x8 m41 m42 -> [m42 * rreplicate 2 (rreplicate 3 x8), m41 * rreplicate 2 (rreplicate 3 x8)]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m55 m56 -> rsum (rreshape [6] m55 * rreshape [6] m56)"
  show deltas
    @?= "ShareR 100000003 (AddR (Dot0R (AstRaw {unAstRaw = AstShare (AstVarId 100000007) (AstReshape [6] (AstProjectR (AstShare (AstVarId 100000005) (AstMkHVector [DynamicRanked (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy,DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 0),DynamicRanked (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy,DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 1)])) 1))}) (ShareR 100000001 (ReshapeR [6] (InputG (FTKR [2,3]) (InputId 0))))) (Dot0R (AstRaw {unAstRaw = AstShare (AstVarId 100000006) (AstReshape [6] (AstProjectR (AstShare (AstVarId 100000004) (AstMkHVector [DynamicRanked (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy,DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 0),DynamicRanked (AstProjectR (AstVar (FTKUntyped [DynamicRankedDummy Proxy Proxy,DynamicRankedDummy Proxy Proxy]) (AstVarId 100000001)) 1)])) 0))}) (ShareR 100000002 (ReshapeR [6] (InputG (FTKR [2,3]) (InputId 1))))))"

testMatvecmulPP :: Assertion
testMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatvecmul)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3] [7 .. 9] )
  printArtifactPretty @(TKR Double 1) renames artifactRev
    @?= "\\v9 m10 v11 -> [rreplicate 2 v11 * rtranspose [1,0] (rreplicate 3 v9), rsum (m10 * rtranspose [1,0] (rreplicate 3 v9))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m20 v21 -> rsum (rtranspose [1,0] (rreplicate 2 v21) * rtranspose [1,0] m20)"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\v9 m38 v39 -> [rreplicate 2 v39 * rtranspose [1,0] (rreplicate 3 v9), rsum (m38 * rtranspose [1,0] (rreplicate 3 v9))]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m48 v49 -> rsum (rtranspose [1,0] (rreplicate 2 v49) * rtranspose [1,0] m48)"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatmul2)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3,4] [7 .. 18] )
  printArtifactPretty @(TKR Double 2) renames artifactRev
    @?= "\\m8 m9 m10 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m10) * rtranspose [2,1,0] (rreplicate 3 m8)), rsum (rtranspose [1,2,0] (rreplicate 4 m9) * rtranspose [1,0] (rreplicate 3 m8))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m19 m20 -> rsum (rtranspose [2,1,0] (rreplicate 4 m19) * rtranspose [1,0] (rreplicate 2 m20))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m8 m37 m38 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m38) * rtranspose [2,1,0] (rreplicate 3 m8)), rsum (rtranspose [1,2,0] (rreplicate 4 m37) * rtranspose [1,0] (rreplicate 3 m8))]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m47 m48 -> rsum (rtranspose [2,1,0] (rreplicate 4 m47) * rtranspose [1,0] (rreplicate 2 m48))"

testMatmul2FromMatvecmulPP :: Assertion
testMatmul2FromMatvecmulPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2F :: (RankedTensor ranked, GoodScalar r)
                => ranked r 2 -> ranked r 2 -> ranked r 2
      rmatmul2F m1 m2 =
        rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry rmatmul2F)
                 ( ringestData [2,3] [1 .. 6]
                 , ringestData [3,4] [7 .. 18] )
  printArtifactPretty @(TKR Double 2) renames artifactRev
    @?= "\\m13 m14 m15 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m15) * rtranspose [2,1,0] (rreplicate 3 m13)), rsum (rtranspose [1,2,0] (rreplicate 4 m14) * rtranspose [1,0] (rreplicate 3 m13))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m24 m25 -> rsum (rtranspose [2,1,0] (rreplicate 4 m24) * rtranspose [1,0] (rreplicate 2 m25))"

testMatmul2PaperPP :: Assertion
testMatmul2PaperPP = do
  resetVarCounter
  let renames = IM.empty
      rmatmul2P :: (RankedTensor ranked, GoodScalar r)
                => ranked r 2 -> ranked r 2 -> ranked r 2
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
  printArtifactPretty @(TKR Double 2) renames artifactRev
    @?= "\\m12 m13 m14 -> [rsum (rtranspose [2,0,1] (rreplicate 2 m14) * rtranspose [2,1,0] (rreplicate 3 m12)), rsum (rtranspose [1,2,0] (rreplicate 4 m13) * rtranspose [1,0] (rreplicate 3 m12))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m23 m24 -> rsum (rtranspose [2,1,0] (rreplicate 4 m23) * rtranspose [1,0] (rreplicate 2 m24))"

testMatmul2PPS :: Assertion
testMatmul2PPS = do
  resetVarCounter
  let renames = IM.empty
      (artifactRev, _) =
        revArtifactAdapt
                 True (uncurry smatmul2)
                 ( sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2,3] knownShS [1 :: Double .. 6]
                 , sconst $ Nested.Internal.sfromListPrimLinear @_ @'[3,4] knownShS [7 .. 18] )
  printArtifactPretty renames artifactRev
    @?= "\\m8 m9 m10 -> [ssum (stranspose (sreplicate m10) * stranspose (sreplicate m8)), ssum (stranspose (sreplicate m9) * stranspose (sreplicate m8))]"
  printArtifactPrimalPretty renames artifactRev
    @?= "\\m19 m20 -> ssum (stranspose (sreplicate m19) * stranspose (sreplicate m20))"
  printArtifactPretty renames (simplifyArtifact artifactRev)
    @?= "\\m8 m37 m38 -> [ssum (stranspose (sreplicate m38) * stranspose (sreplicate m8)), ssum (stranspose (sreplicate m37) * stranspose (sreplicate m8))]"
  printArtifactPrimalPretty renames (simplifyArtifact artifactRev)
    @?= "\\m47 m48 -> ssum (stranspose (sreplicate m47) * stranspose (sreplicate m48))"

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
    (crev (bar @(ADVal ORArray Double 0)) (rscalar 1.1, rscalar 2.2))

testBarS :: Assertion
testBarS =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (crev (barF @(ADVal OSArray Double '[])) (srepl 1.1, srepl 2.2))

testBar2S :: Assertion
testBar2S =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (rev (barF @(AstShaped FullSpan Double '[52, 2, 2, 1, 1, 3])) (srepl 1.1, srepl 2.2))

testBarCFwd :: Assertion
testBarCFwd =
  assertEqualUpToEpsilon 1e-9
    (rscalar 9.327500345189534e-2)
    (cfwd (bar @(ADVal ORArray Double 0)) (rscalar 1.1, rscalar 2.2) (rscalar 0.1, rscalar 0.2))

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
baz :: ( ADVal ORArray Double 0
       , ADVal ORArray Double 0
       , ADVal ORArray Double 0 )
    -> ADVal ORArray Double 0
baz (_x,y,z) =
  let w = fooConstant * barADVal2 (y,y,z) * sin y
  in atan2F z w + z * w

-- An "old term", computed once, stored at top level.
fooConstant :: ADVal ORArray Double 0
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
     => [ADVal ORArray r 0] -> ADVal ORArray r 0
fooD [x, y, z] =
  let w = x * sin y
  in atan2F z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627]
    (crev fooD [rscalar 1.1, rscalar 2.2, rscalar 3.3])

fooBuild1 :: (ADReady ranked, GoodScalar r, Differentiable r)
          => ranked r 1 -> ranked r 1
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

fooMap1 :: (ADReady ranked, GoodScalar r, Differentiable r)
        => ranked r 0 -> ranked r 1
fooMap1 r =
  let v = fooBuild1 $ rreplicate0N [130] r
  in rmap0N (\x -> x * r + rscalar 5) v

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-3
    4.438131773975095e7
    (rev' @Double @1 fooMap1 1.1)

barAst :: (GoodScalar r, Differentiable r)
       => (AstRanked PrimalSpan r 0, AstRanked PrimalSpan r 0) -> AstRanked PrimalSpan r 0
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2F x w + y * w

fooNoGoAst :: forall r. (GoodScalar r, Differentiable r)
           => AstRanked PrimalSpan r 1 -> AstRanked PrimalSpan r 1
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
        => ADVal ORArray r 1 -> ADVal ORArray r 1
      f x = interpretAst (extendEnv @_ @_ @(TKR r 1)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (unAstRanked $ fooNoGoAst (AstRanked $ AstVar (FTKR [5]) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-6
       (OR.fromList [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
       (crev @_ @(TKR Double 1)
             f
             (ringestData1 [1.1, 2.2, 3.3, 4, 5]))

fooNoGo :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
        => ranked r 1 -> ranked r 1
fooNoGo v =
  let r = rsum0 v
  in rbuild1 3 (\ix ->
       bar (rscalar 3.14, bar (rscalar 3.14, rindex v [(ix + (rprimalPart . rfloor) r) `minF` 2 `maxF` 0]))
       + ifF ((&&*) (rindex @ranked @r @1 v [ix * 2] <=. rscalar 0)
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

nestedBuildMap :: forall ranked r.
                  (ADReady ranked, GoodScalar r, Differentiable r)
               => ranked r 0 -> ranked r 1
nestedBuildMap r =
  let w = rreplicate0N @ranked [4]
      v0' = rreplicate0N [177] r :: ranked r 1
  in rlet v0' $ \v' ->
    let nestedMap x0 = rlet x0 $ \x -> rmap0N (x /) (w x)
        variableLengthBuild iy = rbuild1 7 (\ix -> rindex v' (ix + iy :.: ZIR))
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
    (rev' @Double @1 nestedSumBuild (FlipR $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall ranked r. (ADReady ranked, GoodScalar r)
                 => ranked r 1 -> ranked r 1
nestedBuildIndex v =
  rbuild1 2 $ \ix2 -> rindex (rbuild1 3 $ \ix3 -> rindex (rbuild1 4 $ \ix4 -> rindex v (ix4 :.: ZIR)) [ix3]) (ix2 :.: ZIR)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @Double @1 nestedBuildIndex (FlipR $ OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( ADReady ranked, GoodScalar r, KnownNat n, Differentiable r )
  => ranked r n -> ranked r n
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
  :: ( ADReady ranked, GoodScalar r, KnownNat n, RealFloatF (ranked r n) )
  => ranked r n -> ranked r n
barReluMax0 x = reluMax $ bar (x, x)

barReluMax
  :: ( ADReady ranked, GoodScalar r, KnownNat n, RealFloatF (ranked r n) )
  => ranked r n -> ranked r n
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
                     (rconst $ Nested.Internal.rfromListPrimLinear (fromList [2, 1, 2]) [1.1, 2, 3, 4.2])
                     (ringestData [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

reluMaxS :: forall shaped sh r.
            (ADReadyS shaped, GoodScalar r, KnownShS sh, KnownNat (X.Rank sh))
         => shaped r sh -> shaped r sh
reluMaxS = smap0N (maxF (srepl 0))

barReluMaxS
  :: ( ADReadyS shaped, GoodScalar r, KnownShS sh, KnownNat (X.Rank sh)
     , RealFloatF (shaped r sh) )
  => shaped r sh -> shaped r sh
barReluMaxS x = reluMaxS $ barF (x, reluMaxS x)

-- Previously the shape of FromListR[ZeroR] couldn't be determined
-- in buildDerivative, so this was needed. See below that it now works fine.
testBarReluMax3FwdS :: Assertion
testBarReluMax3FwdS =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @_ @(TKS Double '[2, 1, 2])
         barReluMaxS
         (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdFrom :: Assertion
testBarReluMax3FwdFrom =
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (fwd @_ @(TKS Double '[2, 1, 2])
         (sfromR . barReluMax . rfromS)
         (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

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
     ( KnownNat n, ADReady (AstRanked PrimalSpan), GoodScalar r
     , Differentiable r )
  => AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
barReluAst x = relu $ bar (x, relu x)

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal ORArray r 0 -> ADVal ORArray r 0
      f x = interpretAst (extendEnv @_ @_ @(TKR r 0)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (unAstRanked $ barReluAst (AstRanked $ AstVar (FTKR []) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [191.20462646925841])
       (crevDt @_ @(TKR Double 0)
               f (rscalar 1.1) (rscalar 42.2))

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal ORArray r 1 -> ADVal ORArray r 1
      f x = interpretAst (extendEnv @_ @_ @(TKR r 1)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (unAstRanked $ barReluAst (AstRanked $ AstVar (FTKR [5]) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (crev @_ @(TKR Double 1)
             f (rfromList0N [5] [rscalar 1.1, rscalar 2.2, rscalar 3.3, rscalar 4, rscalar 5]))

konstReluAst
  :: forall r.
     (ADReady (AstRanked PrimalSpan), GoodScalar r, Differentiable r)
  => AstRanked PrimalSpan r 0 -> AstRanked PrimalSpan r 0
konstReluAst x = rsum0 $ relu $ rreplicate0N (7 :$: ZSR) x

testReplicateReluAst :: Assertion
testReplicateReluAst =
  let f :: forall r. (GoodScalar r, Differentiable r)
        => ADVal ORArray r 0 -> ADVal ORArray r 0
      f x = interpretAst (extendEnv @_ @_ @(TKR r 0)
                            (mkAstVarName $ intToAstVarId 100000000)
                            x emptyEnv)
                         (unAstRanked $ konstReluAst (AstRanked $ AstVar (FTKR []) (mkAstVarName . intToAstVarId $ 100000000)))
  in assertEqualUpToEpsilon1 1e-10
       (OR.fromList [] [295.4])
       (crevDt @_ @(TKR Double 0)
               f (rscalar 1.1) (rscalar 42.2))

f1 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 0
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

f2 :: forall ranked r. (ADReady ranked, GoodScalar r)
   => ranked r 0 -> ranked r 0
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

braidedBuilds :: forall ranked r.
                 (ADReady ranked, GoodScalar r, Differentiable r)
              => ranked r 0 -> ranked r 2
braidedBuilds r =
  rbuild1 3 (\ix1 ->
    rbuild1 4 (\ix2 -> rindex (rfromList0N [4]
      [rfromIndex0 ix2, rscalar 7, r, rscalar (-0.2)]) (ix1 :.: ZIR)))

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

concatBuild2 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
concatBuild2 r =
  rlet (rfromList [r, 1, 2, 3, 4]) $ \a ->
    rbuild1 10 (\i -> ifF (i <. 5) (rindex a [i]) (rindex a [i - 5]))

testConcatBuild2 :: Assertion
testConcatBuild2 =
  assertEqualUpToEpsilon' 1e-10
    2.0
    (rev' @Double @1 concatBuild2 3.4)

concatBuild3 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
concatBuild3 r =
  rlet (rfromList [r, 1, 2, 3, 4]) $ \a ->
    rbuild1 10 (\i -> ifF (i <. 5) (rindex a [i]) (rindex a [i - 5 + (1 `quotF` maxF 1 (i - 5))]))

testConcatBuild3 :: Assertion
testConcatBuild3 =
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' @Double @1 concatBuild3 3.4)

concatBuild4 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
concatBuild4 r =
  rlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (4 + i)) :.: ZIR)) $ \a ->
    rappend a a

testConcatBuild4 :: Assertion
testConcatBuild4 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 concatBuild4 3.4)

concatBuild5 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
concatBuild5 r =
  rlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (5 + i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotF` (5 + i)) :.: ZIR)))

testConcatBuild5 :: Assertion
testConcatBuild5 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 concatBuild5 3.4)

concatBuild6 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 2
concatBuild6 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (rlet (rgather1 5 (rreplicate 1 r)
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

concatBuild7 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
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
_concatBuild8 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
_concatBuild8 r =
  rlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotF` (5 - i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotF` (5 - i)) :.: ZIR)))

_testConcatBuild8 :: Assertion
_testConcatBuild8 =
  assertEqualUpToEpsilon' 1e-10
    10
    (rev' @Double @1 _concatBuild8 3.4)

_concatBuild9 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 2
_concatBuild9 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (rlet (rgather1 5 (rreplicate 1 r)
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

concatBuild10 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 2
concatBuild10 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (rlet (rgather1 5 (rreplicate 1 r)
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

concatBuild11 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 1
concatBuild11 r =
  rgather1 5 (rreplicate 1 r) (\_i -> (-1) :.: ZIR)

testConcatBuild11 :: Assertion
testConcatBuild11 =
  assertEqualUpToEpsilon' 1e-10
    0
    (rev' @Double @1 concatBuild11 3.4)

concatBuild12 :: (ADReady ranked, GoodScalar r) => ranked r 0 -> ranked r 0
concatBuild12 r =
  rindex (rreplicate 1 r) ((-1) :.: ZIR)

testConcatBuild12 :: Assertion
testConcatBuild12 =
  assertEqualUpToEpsilon' 1e-10
    0
    (rev' @Double @0 concatBuild12 3.4)

emptyArgs :: forall ranked r. (ADReady ranked, GoodScalar r) -- , Differentiable r)
          => ranked r 1 -> ranked r 1
emptyArgs _t =
  emptyTensor
--  - rfromList0N (rshape @ranked @r emptyTensor) []
  - rreshape @ranked @r @1 [0] emptyTensor
--  - rgather1 0 emptyTensor (:.: ZIR)
--  - rsum (rgather1 0 emptyTensor (const ZIR))
--  - rsum (rgather @ranked @r @2 (0 :$: 0 :$: ZSR) emptyTensor (const (0 :.: ZIR)))
--  - rsum (rgather @ranked @r @2 @0 @1 [0, 0] emptyTensor (const [0]))
  - rsum (rreshape @ranked @r @1 [0, 0] emptyTensor)
--  - rindex (rfromList0N (0 :$: 0 :$: ZSR) []) (42 :.: ZIR)
--  - rindex (rfromList0N (0 :$: rshape @ranked @r emptyTensor) []) (42 :.: ZIR)
--  - rsum (rfromList0N (0 :$: rshape @ranked @r emptyTensor) [])
--  * rsum (rfromList [rsum (rfromList0N (0 :$: rshape @ranked @r emptyTensor) [])])
--  * rflatten (rtr (rgather1 0 t (const ZIR)))
--  + rbuild1 0 (\i -> t ! [fromIntegral (rrank t) `quotF` i] / rfromIndex0 i)
  -- - rsum (rbuild @ranked @r @2 (0 :$: 0 :$: ZSR) (const 73))
  -- - rsum (rbuild @ranked @r @1 (0 :$: 0 :$: ZSR) (const $ rfromList []))
       -- these two fail and rightly so; TODO: make them fail earlier
 where
  emptyTensor :: ranked r 1
  emptyTensor = rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) []

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

filterPositiveFail :: ADReady ranked
                   => ranked Double 1 -> ranked Double 1
filterPositiveFail v =
  let l = runravelToList v
      -- l2 = filter (\x -> x >= 0) l
      -- Could not deduce ‘Ord (ranked Double 0)’
      -- l2 = filter (\x -> x >=. 0) l
      -- Could not deduce ‘BoolOf ranked ~ Bool’
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
fblowup :: forall ranked r. (ADReady ranked, GoodScalar r, Differentiable r)
        => Int -> ranked r 1 -> ranked r 0
fblowup k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y - rfromIndex0 0
      blowup n y =
        let ysum = y + y - rfromIndex0 0
            yscaled = rscalar 0.499999985 * ysum
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
            yscaled = rscalar 0.499999985 * ysum
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
        let ysum = y + y * y / (y - rscalar 0.000000001)
            yscaled = sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 0
      y0 = (inputs ! [0 `remF` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall ranked r.
                  (ADReady ranked, GoodScalar r, Differentiable r)
               => IntOf ranked -> Int -> ranked r 1 -> ranked r 0
fblowupMultLet i k inputs =
  let blowup :: Int -> ranked r 0 -> ranked r 0
      blowup 0 y = y
      blowup n y1 = rlet y1 $ \y ->
        let ysum0 = y + y * y / (y - rscalar 0.000001)
            yscaled = rlet ysum0 $ \ysum ->
                        sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 i
      y0 = (inputs ! [i `remF` 2]) * (inputs ! [1])
  in blowup k y0

fblowupPP :: Assertion
fblowupPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupT = fblowup @(AstRanked FullSpan) @Double 1
  let (artifactRev, _) = revArtifactAdapt True fblowupT (rreplicate0N [4] (rscalar 4))
  printArtifactSimple renames artifactRev
    @?= "\\x8 v10 -> dlet (v10 ! [0]) (\\x3 -> dlet (v10 ! [1]) (\\x4 -> dlet (v10 ! [0]) (\\x5 -> dlet (v10 ! [1]) (\\x6 -> dlet (0.499999985 * x8) (\\x9 -> dmkHVector (fromList [DynamicRanked (rscatter [4] (recip x4 * x9) (\\[] -> [0]) + rscatter [4] ((negate x3 / (x4 * x4)) * x9) (\\[] -> [1]) + rscatter [4] (recip x6 * x9) (\\[] -> [0]) + rscatter [4] ((negate x5 / (x6 * x6)) * x9) (\\[] -> [1]))]))))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\v11 -> rlet (v11 ! [0]) (\\x3 -> rlet (v11 ! [1]) (\\x4 -> rlet (v11 ! [0]) (\\x5 -> rlet (v11 ! [1]) (\\x6 -> rlet ((x3 / x4 + x5 / x6) - 0.0) (\\x7 -> 0.499999985 * x7 - 0.0)))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let renames = IM.empty
      fblowupLetT = fblowupLet @(AstRanked FullSpan) @Double 0 1
  let (artifactRev, _) = revArtifactAdapt True fblowupLetT (rreplicate0N [4] (rscalar 4))
  printArtifactSimple renames artifactRev
    @?= "\\x8 v11 -> dlet (v11 ! [0]) (\\x4 -> dlet (v11 ! [1]) (\\x5 -> dlet (0.499999985 * x8) (\\x9 -> dlet (x9 + x9) (\\x10 -> dmkHVector (fromList [DynamicRanked (rscatter [4] (recip x5 * x10) (\\[] -> [0]) + rscatter [4] ((negate x4 / (x5 * x5)) * x10) (\\[] -> [1]))])))))"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\v12 -> rlet (v12 ! [0]) (\\x4 -> rlet (v12 ! [1]) (\\x5 -> rlet (x4 / x5) (\\x6 -> rlet ((x6 + x6) - 0.0) (\\x7 -> 0.499999985 * x7 - 0.0))))"

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

concatBuild33 :: (ADReady ranked, GoodScalar r)
             => ranked r 1 -> ranked r 2
concatBuild33 _r =
  rbuild1 5 (\i ->
    rbuild1 2 (\j -> rfromIndex0 (maxF j (i `quotF` (j + 1)))))

testConcatBuild3PP :: Assertion
testConcatBuild3PP = do
  resetVarCounter
  let renames = IM.empty
      t = concatBuild33 @(AstRanked FullSpan) @Float
      (var3, ast3) = funToAst (FTKR [3]) $ unAstRanked . t . AstRanked
  "\\" ++ printAstVarName renames var3
       ++ " -> " ++ printAstSimple renames (AstRanked ast3)
    @?= "\\v1 -> rconstant (rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rslice 0 2 riota), quotF (rtranspose [1,0] (rreplicate 2 (rslice 0 5 riota))) (rreplicate 5 (rreplicate 2 1 + rslice 0 2 riota))])) (\\[i5, i4] -> [ifF (i4 >=. quotF i5 (1 + i4)) 0 1, i5, i4])))"

testConcatBuild3PP2 :: Assertion
testConcatBuild3PP2 = do
  resetVarCounter
  let renames = IM.empty
      t = concatBuild33 @(AstRanked FullSpan) @Double
  let (artifactRev, _) =
        revArtifactAdapt True t (FlipR $ Nested.rfromOrthotope SNat $ OR.fromList [3] [0.651,0.14,0.3414])
  printArtifactSimple renames artifactRev
    @?= "\\m9 v10 -> dmkHVector (fromList [DynamicRankedDummy])"
  printArtifactPrimalSimple renames artifactRev
    @?= "\\v11 -> rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rconst (rfromListLinear [2] [0,1])), quotF (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [5] [0,1,2,3,4])))) (rreplicate 5 (rconst (rfromListLinear [2] [0,1]) + rreplicate 2 1))])) (\\[i7, i8] -> [ifF (i8 >=. quotF i7 (1 + i8)) 0 1, i7, i8]))"
  printArtifactPrimalSimple renames (simplifyArtifact artifactRev)
    @?= "\\v12 -> rfromIntegral (rgather [5,2] (rfromVector (fromList [rreplicate 5 (rconst (rfromListLinear [2] [0,1])), quotF (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [5] [0,1,2,3,4])))) (rreplicate 5 (rconst (rfromListLinear [2] [0,1]) + rreplicate 2 1))])) (\\[i7, i8] -> [ifF (i8 >=. quotF i7 (1 + i8)) 0 1, i7, i8]))"
