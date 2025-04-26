{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fno-cse #-}
-- | Assorted rather low rank tensor tests.
module TestAdaptorSimplified
  ( testTrees
  ) where

import Prelude

import Data.Int (Int64)
import Data.Kind (Type)
import Data.List.NonEmpty qualified as NonEmpty
import Foreign.C (CInt)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Mixed.Shape
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId (funToAst, resetVarCounter)
import HordeAd.Core.AstInterpret
import HordeAd.Core.DeltaFreshId (resetIdCounter)

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
  , testCase "2zero4s" testZero4s
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
  , testCase "2piecewiseLinear" testPiecewiseLinear
  , testCase "2piecewiseLinearPP" testPiecewiseLinearPP
  , testCase "2piecewiseLinear2" testPiecewiseLinear2
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
  , testCase "2fooGradDouble" testGradFooDouble
  , testCase "2fooMatrix" testFooMatrix
  , testCase "2fooGradMatrix" testGradFooMatrix
  , testCase "2fooLetGradMatrixPP" testGradFooLetMatrixPP
  , testCase "2fooGradMatrixVjp" testGradFooMatrixVjp
  , testCase "2fooGradMatrixRev" testGradFooMatrixRev
  , testCase "2fooLetGradMatrixSimpPP" testGradFooLetMatrixSimpPP
  , testCase "2fooLetGradMatrixSimpRPP" testGradFooLetMatrixSimpRPP
  , testCase "2fooSumMatrix" testfooSumMatrix
  , testCase "2fooGradMatrix2" testGradFooMatrix2
  , testCase "2fooGradMatrixPP" testGradFooMatrixPP
  , testCase "2fooGradMatrixSimpPP" testGradFooMatrixSimpPP
  , testCase "2fooGradScalar" testGradFooScalar
  , testCase "2fooGradCScalar" testGradCFooScalar
  , testCase "2fooS" testFooS
  , testCase "2fooSToFloat" testFooSToFloat
  , testCase "2fooSBoth" testFooSBoth
  , testCase "2fooBoth" testFooBoth
  , testCase "2trustVstackConcatRepl10" testTrustVstackConcatRepl10
  , testCase "2trustVstackConcatIota10" testTrustVstackConcatIota10
  , testCase "2trustVstackConcatReplIota10" testTrustVstackConcatReplIota10
  , testCase "2vstackWarmup" testVstackWarmup
  , testCase "2vstackConcatConcrete" testVstackConcatConcrete
  , testCase "2vstackBuildConcrete" testVstackBuildConcrete
  , testCase "2vstackConcatAst" testVstackConcatAst
  , testCase "2vstackBuildAst" testVstackBuildAst
  , testCase "2vstackBuildAstSimp" testVstackBuildAstSimp
  , testCase "2vstackBuildAstPP" testVstackBuildAstPP
  , testCase "2vstackConcatConcrete2" testVstackConcatConcrete2
  , testCase "2vstackBuildConcrete2" testVstackBuildConcrete2
  , testCase "2vstackConcatAst2" testVstackConcatAst2
  , testCase "2vstackBuildAst2" testVstackBuildAst2
  , testCase "2vstackBuildAstSimp2" testVstackBuildAstSimp2
  , testCase "2vstackBuildAstPP2" testVstackBuildAstPP2
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
  , testCase "2reluSimplerPP4s" testReluSimplerPP4s
  , testCase "2reluSimplerPP4s2" testReluSimplerPP4s2
  , testCase "2reluSimpler4s" testReluSimpler4s
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
  , testCase "2baz old to force fooFromPrimal" testBaz
  , testCase "2baz if repetition breaks things" testBaz
  , testCase "2baz again with renumbered terms" testBazRenumbered
  , testCase "2fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "2fooBuildDt" testFooBuildDt
  , testCase "2fooBuildCFwd" testFooBuildCFwd
  , testCase "2fooBuildFwd" testFooBuildFwd
  , testCase "2fooBuild" testFooBuild
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
  , testCase "2blowup2LetPP" fblowupLetPP
  , testCase "2blowup2LetPP23" fblowupLetPP23
  , testCase "2blowup2LetPP10" fblowupLetPP10
  , blowupTests
  , testCase "22concatBuild3PP" testConcatBuild3PP
  , testCase "22concatBuild3PP2" testConcatBuild3PP2
  ]

testZeroZ :: Assertion
testZeroZ =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0)
    (rev' @Double @0 (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
                          f = const (rscalar 3)
                      in f) (rscalar 42))

testZeroS :: Assertion
testZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cgrad (kfromS . ssum0 .
            let f :: ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
                  -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
                f = const (srepl 3)
            in f) (srepl 42))

testCFwdZeroS :: Assertion
testCFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cjvp (let f :: ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
                 -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
               f = const (srepl 3)
           in f) 42 41)

testFwdZeroS :: Assertion
testFwdZeroS =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (jvp (let f :: AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double)
                -> AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double)
              f = const (srepl 3)
          in f) (srepl 42) (srepl 41))

testZero2S :: Assertion
testZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[] knownShS [1])
    (cgrad (kfromS @_ @Double .
           let f :: a -> a
               f = id
           in f) (srepl 42))

testCFwdZero2S :: Assertion
testCFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[] knownShS [41])
    (cjvp @_ @(TKS '[] Double)
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testFwdZero2S :: Assertion
testFwdZero2S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[] knownShS [41])
    (jvp @_ @(TKS '[] Double)
          (let f :: a -> a
               f = id
           in f) (srepl 42) (srepl 41))

testZero3S :: Assertion
testZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.6174114266850617))
    (cgrad (kfromS . ssum0 . (\x -> barF @(ADVal Concrete (TKS '[33, 2] Double)) (x, x))) (srepl 1))

testCFwdZero3S :: Assertion
testCFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (cjvp (\x -> barF @(ADVal Concrete (TKS '[33, 2] Double)) (x, x)) (srepl 1) (srepl 1.1))

testFwdZero3S :: Assertion
testFwdZero3S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[33, 2] knownShS (replicate 66 3.9791525693535674))
    (jvp (\x -> barF @(AstTensor AstMethodLet FullSpan (TKS '[33, 2] Double)) (x, x)) (srepl 1) (srepl 1.1))

testZero4s :: Assertion
testZero4s =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[] knownShS [0])
    (grad @(AstTensor AstMethodLet FullSpan (TKS '[] Double))
          (kfromS @_ @Double .
          let f = const (srepl 3)
          in f) (srepl 42))

testZero5S :: Assertion
testZero5S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[44] knownShS (replicate 44 1))
    (grad (kfromS . ssum0 .
           let f :: a -> a
               f = id
           in f @(AstTensor AstMethodLet FullSpan (TKS '[44] Double))) (srepl 42))

testZero6S :: Assertion
testZero6S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] knownShS (replicate (product ([2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] :: [Int])) 3.6174114266850617))
    (grad (kfromS . ssum0 @'[2, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 2, 2, 2, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,111,1,1,1,1, 2, 2, 2, 2] @(TKScalar Double) . (\x -> barF (x, x))) (srepl 1))

testZero7S :: Assertion
testZero7S =
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[] knownShS [0])
    (grad (kfromR . (const (rscalar 3) :: AstTensor AstMethodLet FullSpan (TKS '[] Double) -> AstTensor AstMethodLet FullSpan (TKR 0 Double))) (srepl 42))

testZero8 :: Assertion
testZero8 =
  assertEqualUpToEpsilon 1e-10
    (rfromList0N [] [rscalar 0])
    (grad (kfromS . (const (sscalar 3) :: AstTensor AstMethodLet FullSpan (TKR 0 Double) -> AstTensor AstMethodLet FullSpan (TKS '[] Double))) (rscalar 42))

testZero9S :: Assertion
testZero9S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (cgrad (kfromS . ssum0 .
            let f :: ADVal Concrete (TKR 5 Double)
                  -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
                f = const (srepl 3)
            in f)
           (rreplicate0N [0, 2, 4, 0, 1] (rscalar 42)))

testCFwdZero9S :: Assertion
testCFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cjvp (let f :: ADVal Concrete (TKR 5 Double)
                 -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double)
               f = const (srepl 3)
           in f)
          (rreplicate0N [0, 2, 4, 0, 1] (rscalar 42)) (rreplicate0N [0, 2, 4, 0, 1] (rscalar 41)))

testFwdZero9S :: Assertion
testFwdZero9S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (jvp (let f :: AstTensor AstMethodLet FullSpan (TKR 5 Double)
                -> AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double)
              f = const (srepl 3)
          in f)
         (rreplicate0N [0, 2, 4, 0, 1] (rscalar 42)) (rreplicate0N [0, 2, 4, 0, 1] (rscalar 41)))

testZero10S :: Assertion
testZero10S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (cgrad (kfromS . ssum0 .
            let f = const (srepl 3) . snd
            in f :: ( ADVal Concrete (TKR 5 Double)
                    , ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double) )
                 -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double))
          (rreplicate0N [0, 2, 4, 0, 1] (rscalar 42), srepl 21))

testCFwdZero10S :: Assertion
testCFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (cjvp (let f = const (srepl 3) . snd
           in f :: ( ADVal Concrete (TKR 5 Double)
                   , ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double) )
                   -> ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero10S :: Assertion
testFwdZero10S =
  assertEqualUpToEpsilon 1e-9
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [])
    (jvp  (let f = const (srepl 3) . snd
           in f :: ( AstTensor AstMethodLet FullSpan (TKR 5 Double)
                   , AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double) )
                   -> AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testZero11S :: Assertion
testZero11S =
  assertEqualUpToEpsilon 1e-9
    ( rfromList0N [0, 2, 4, 0, 1] []
    , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
    (cgrad (kfromR . rsum0 .
            let f = const (rreplicate0N [0, 2, 4, 0, 1] (rscalar 3)) . snd
            in f :: ( ADVal Concrete (TKR 5 Double)
                    , ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double) )
                 -> ADVal Concrete (TKR 5 Double))
          (rreplicate0N [0, 2, 4, 0, 1] (rscalar 42), srepl 21))

testCFwdZero11S :: Assertion
testCFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (cjvp (let f = const (rreplicate0N [0, 2, 4, 0, 1] (rscalar 3)) . snd
           in f :: ( ADVal Concrete (TKR 5 Double)
                   , ADVal Concrete (TKS '[0, 2, 4, 0, 1] Double) )
                   -> ADVal Concrete (TKR 5 Double))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testFwdZero11S :: Assertion
testFwdZero11S =
  assertEqualUpToEpsilon 1e-9
    (rfromList0N [0, 2, 4, 0, 1] [])
    (jvp  (let f = const (rreplicate0N [0, 2, 4, 0, 1] (rscalar 3)) . snd
           in f :: ( AstTensor AstMethodLet FullSpan (TKR 5 Double)
                   , AstTensor AstMethodLet FullSpan (TKS '[0, 2, 4, 0, 1] Double) )
                   -> AstTensor AstMethodLet FullSpan (TKR 5 Double))
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] )
          ( rfromList0N [0, 2, 4, 0, 1] []
          , sconcrete $ Nested.sfromListPrimLinear @_ @'[0, 2, 4, 0, 1] knownShS [] ))

testPiecewiseLinear :: Assertion
testPiecewiseLinear =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2)
    (let fT :: ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
         fT x = ifH (x >. rscalar 0) (rscalar 2 * x) (rscalar 5 * x)
     in rev' @Double @0 fT (rscalar 42))

testPiecewiseLinearPP :: Assertion
testPiecewiseLinearPP = do
  resetVarCounter
  let fT :: AstTensor AstMethodLet FullSpan (TKR 0 Double)
         -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT x = ifH (x >. rscalar 0) (rscalar 2 * x) (rscalar 5 * x)
      (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKR ZSR FTKScalar)
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> rfromS (let v3 = soneHot (sfromR dret) [ifH (sscalar -0.0 <=. negate (sfromR x1)) 0 1] in sscalar 2.0 * v3 !$ [1] + sscalar 5.0 * v3 !$ [0])"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (ifH (sscalar -0.0 <=. negate (sfromR x1)) (sscalar 5.0 * sfromR x1) (sscalar 2.0 * sfromR x1))"

testPiecewiseLinear2 :: Assertion
testPiecewiseLinear2 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 5)
    (let fT :: ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
         fT x = ifH (x >. rscalar 0) (rscalar 2) (rscalar 5) * x
     in rev' @Double @0 fT (rscalar (-42)))

testPiecewiseLinear2PP :: Assertion
testPiecewiseLinear2PP = do
  resetVarCounter
  let fT :: AstTensor AstMethodLet FullSpan (TKR 0 Double)
         -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT x = ifH (x >. rscalar 0) (rscalar 2) (rscalar 5) * x
      (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKR ZSR FTKScalar)
  printArtifactPretty artifactRev
    @?= "\\dret x1 -> let x2 = ifH (sscalar -0.0 <=. negate (sfromR x1)) (sscalar 5.0) (sscalar 2.0) in rfromS (x2 * sfromR dret)"
  printArtifactPrimalPretty artifactRev
    @?= "\\x1 -> let x2 = ifH (sscalar -0.0 <=. negate (sfromR x1)) (sscalar 5.0) (sscalar 2.0) in rfromS (x2 * sfromR x1)"

overleaf :: forall r target. (BaseTensor target, GoodScalar r)
         => target (TKR 1 r) -> target (TKR 0 r)
overleaf v = let wrap i = i `remH` fromIntegral (rwidth v)
             in rsum (rbuild @1 [50] (\[i] -> rindex v [wrap i]))

testOverleaf :: Assertion
testOverleaf =
  assertEqualUpToEpsilon' 1e-10
    (ringestData @_ @Double [28] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @Double @0 overleaf (ringestData [28] [0 .. 27]))

testOverleafInt64n :: Assertion
testOverleafInt64n =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [0 :: Double,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))
    (cgrad (kfromR @_ @Int64 . overleaf) (ringestData [28] [0 .. 27]))

testOverleafCIntn :: Assertion
testOverleafCIntn =
  assertEqualUpToEpsilon 1e-10
    (ringestData [28] (map round [0 :: Double,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))
    (grad (kfromR @_ @CInt . overleaf) (ringestData [28] [0 .. 27]))

testOverleafCIntToFloatn :: Assertion
testOverleafCIntToFloatn =
  assertEqualUpToEpsilon 1e-10
    (rfromList0N [28] (replicate 28 (rscalar 0.0)))
    (grad (kfromR @_ @CInt . rfromIntegral . overleaf @CInt . rfloor) (ringestData @_ @Float [28] [0 .. 27]))

testOverleafInt64p :: Assertion
testOverleafInt64p =
  assertEqualUpToEpsilon' 1e-10
    (ringestData @_ @Int64 [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @Int64 @0 overleaf (ringestData [28] [0 .. 27]))

testOverleafCIntp :: Assertion
testOverleafCIntp =
  assertEqualUpToEpsilon' 1e-10
    (ringestData @_ @CInt [28] (map round [2.0 :: Double,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,1.0,1.0,1.0,1.0,1.0,1.0]))
    (rev' @CInt @0 overleaf (ringestData [28] [0 .. 27]))

testOverleafCIntToFloatp :: Assertion
testOverleafCIntToFloatp =
  assertEqualUpToEpsilon' 1e-10
    (ringestData @1 @Float [28] (replicate 28 0.0))
    (let f :: forall f. ADReady f => f (TKR 1 Float) -> f (TKR 0 Float)
         f = rfromIntegral . overleaf @CInt . rfloor
     in rev' @Float @0 f (ringestData [28] [0 .. 27]))

testOverleafPP :: Assertion
testOverleafPP = do
  resetVarCounter >> resetIdCounter
  let fT :: AstTensor AstMethodLet FullSpan (TKR 1 Double)
         -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = overleaf
      (var3, ast3) = funToAst (FTKR [28] FTKScalar) Nothing fT
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\v1 -> rfromS (ssum @50 (sgather [] (sfromR v1) (\\[i2] -> [remH i2 28])))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactDelta UseIncomingCotangent fT (FTKR [28] FTKScalar)
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> rfromS (sscatter (sreplicate @50 (sfromR dret)) (\\[i5] -> [remH i5 28]))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (ssum0 (sgather (sfromR v1) (\\[i3] -> [remH i3 28])))"
  show deltas
    @?= "DeltaFromS (STKR (SNat @0) STKScalar) (DeltaShare 100000002 (DeltaSum (SNat @50) (STKS [] STKScalar) (DeltaShare 100000001 (DeltaGatherS [50] [] [28] (DeltaSFromR [28] (DeltaInput (InputId 0))) <function>))))"

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w  -- note that w appears twice

testFoo :: Assertion
testFoo = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (cgrad (kfromR @_ @Double . foo) (rscalar 1.1, rscalar 2.2, rscalar 3.3))

gradFooDouble :: (Double, Double, Double) -> (Double, Double, Double)
gradFooDouble = fromDValue . cgrad foo . fromValue

testGradFooDouble :: Assertion
testGradFooDouble =
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (gradFooDouble (1.1, 2.2, 3.3))

type Matrix2x2 :: Target -> Type -> Type
type Matrix2x2 f r = f (TKS '[2, 2] r)
type ThreeMatrices r = (Matrix2x2 Concrete r, Matrix2x2 Concrete r, Matrix2x2 Concrete r)
threeSimpleMatrices :: ThreeMatrices Double
threeSimpleMatrices = (srepl 1.1, srepl 2.2, srepl 3.3)
fooMatrixValue :: Matrix2x2 Concrete Double
fooMatrixValue = foo threeSimpleMatrices
gradSumFooMatrix :: ThreeMatrices Double -> ThreeMatrices Double
gradSumFooMatrix = cgrad (kfromS . ssum0 . foo)

testFooMatrix :: Assertion
testFooMatrix =
  assertEqualUpToEpsilon 1e-10
    (sfromListLinear [2,2] [4.242393641025528,4.242393641025528,4.242393641025528,4.242393641025528])
    fooMatrixValue

testGradFooMatrix :: Assertion
testGradFooMatrix =
  assertEqualUpToEpsilon 1e-10
    (sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
    (gradSumFooMatrix threeSimpleMatrices)

fooLet :: (RealFloatH (f r), ADReady f)
       => (f r, f r, f r) -> f r
fooLet (x, y, z) =
  tlet (x * sin y) $ \w ->
    atan2H z w + z * w  -- note that w still appears twice

artifact :: AstArtifactRev (X (ThreeMatrices Double)) (TKS '[2, 2] Double)
artifact = vjpArtifact fooLet threeSimpleMatrices

testGradFooLetMatrixPP :: Assertion
testGradFooLetMatrixPP = do
  resetVarCounter
  printArtifactPretty artifact
    @?= "\\dret m1 -> let m3 = sin (tproject2 (tproject1 m1)) ; m4 = tproject1 (tproject1 m1) * m3 ; m5 = recip (tproject2 m1 * tproject2 m1 + m4 * m4) ; m7 = (negate (tproject2 m1) * m5) * dret + tproject2 m1 * dret in tpair (tpair (m3 * m7) (cos (tproject2 (tproject1 m1)) * (tproject1 (tproject1 m1) * m7))) ((m4 * m5) * dret + m4 * dret)"

testGradFooMatrixVjp :: Assertion
testGradFooMatrixVjp =
  assertEqualUpToEpsilon 1e-10
    ((sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627]) :: ThreeMatrices Double)
    (vjpInterpretArtifact artifact (toTarget threeSimpleMatrices) (srepl 1))

testGradFooMatrixRev :: Assertion
testGradFooMatrixRev =
  assertEqualUpToEpsilon 1e-10
    (sfromListLinear [2,2] [2.4396285219055063,2.4396285219055063,2.4396285219055063,2.4396285219055063],sfromListLinear [2,2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421],sfromListLinear [2,2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
    (grad (kfromS . ssum0 . fooLet) threeSimpleMatrices)

testGradFooLetMatrixSimpPP :: Assertion
testGradFooLetMatrixSimpPP = do
  resetVarCounter
  (let ftk = FTKS @'[2, 2] [2, 2] (FTKScalar @Double)
   in printArtifactPretty
        (simplifyArtifact $ revArtifactAdapt UseIncomingCotangent fooLet (FTKProduct (FTKProduct ftk ftk) ftk)))
      @?= "\\dret m1 -> let m3 = sin (tproject2 (tproject1 m1)) ; m4 = tproject1 (tproject1 m1) * m3 ; m5 = recip (tproject2 m1 * tproject2 m1 + m4 * m4) ; m7 = (negate (tproject2 m1) * m5) * dret + tproject2 m1 * dret in tpair (tpair (m3 * m7) (cos (tproject2 (tproject1 m1)) * (tproject1 (tproject1 m1) * m7))) ((m4 * m5) * dret + m4 * dret)"

testGradFooLetMatrixSimpRPP :: Assertion
testGradFooLetMatrixSimpRPP = do
  resetVarCounter
  (let ftk = FTKR (2 :$: 2 :$: ZSR) (FTKScalar @Double)
    in printArtifactPretty (simplifyArtifact $ revArtifactAdapt UseIncomingCotangent fooLet (FTKProduct (FTKProduct ftk ftk) ftk)))
       @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @2) STKScalar)) (let m3 = sin (sfromR (tproject2 (tproject1 m1))) ; m4 = sfromR (tproject1 (tproject1 m1)) * m3 ; m5 = recip (sfromR (tproject2 m1) * sfromR (tproject2 m1) + m4 * m4) ; m7 = (negate (sfromR (tproject2 m1)) * m5) * sfromR dret + sfromR (tproject2 m1) * sfromR dret in tpair (tpair (m3 * m7) (cos (sfromR (tproject2 (tproject1 m1))) * (sfromR (tproject1 (tproject1 m1)) * m7))) ((m4 * m5) * sfromR dret + m4 * sfromR dret))"

sumFooMatrix :: (ADReady f, RealFloat (Matrix2x2 f r), GoodScalar r)
             => (Matrix2x2 f r, Matrix2x2 f r, Matrix2x2 f r) -> f (TKScalar r)
sumFooMatrix = kfromS . ssum0 . foo

testfooSumMatrix :: Assertion
testfooSumMatrix =
  assertEqualUpToEpsilon 1e-10
    16.96957456410211
    (sumFooMatrix threeSimpleMatrices)

foo2 :: RealFloatH a => (a, a, a) -> a
foo2 (x, y, z) =
  let w = x * sin y
  in atan2H z w + z * w

gradFooMatrix2 :: (Differentiable r, GoodScalar r)
               => (Concrete (TKR 2 r), Concrete (TKR 2 r), Concrete (TKR 2 r))
               -> (Concrete (TKR 2 r), Concrete (TKR 2 r), Concrete (TKR 2 r))
gradFooMatrix2 = grad (kfromR . rsum0 . foo2)

testGradFooMatrix2 :: Assertion
testGradFooMatrix2 =
  assertEqualUpToEpsilon 1e-10
    (ringestData [2, 2] [2.4396285219055063 :: Double,2.4396285219055063,2.4396285219055063,2.4396285219055063], ringestData [2, 2] [-1.953374825727421,-1.953374825727421,-1.953374825727421,-1.953374825727421], ringestData [2, 2] [0.9654825811012627,0.9654825811012627,0.9654825811012627,0.9654825811012627])
    (gradFooMatrix2 (rreplicate0N [2, 2] (rscalar 1.1), rreplicate0N [2, 2] (rscalar 2.2), rreplicate0N [2, 2] (rscalar 3.3)))

testGradFooMatrixPP :: Assertion
testGradFooMatrixPP = do
  resetVarCounter
  (let ftk = FTKR (2 :$: 2 :$: ZSR) (FTKScalar @Double)
    in printArtifactPretty (revArtifactAdapt UseIncomingCotangent foo2 (FTKProduct (FTKProduct ftk ftk) ftk)))
      @?= "\\dret m1 -> let m2 = sin (sfromR (tproject2 (tproject1 m1))) ; m3 = sfromR (tproject1 (tproject1 m1)) * m2 ; m4 = recip (sfromR (tproject2 m1) * sfromR (tproject2 m1) + m3 * m3) ; m5 = sin (sfromR (tproject2 (tproject1 m1))) ; m6 = sfromR (tproject1 (tproject1 m1)) * m5 ; m8 = sfromR (tproject2 m1) * sfromR dret ; m9 = (negate (sfromR (tproject2 m1)) * m4) * sfromR dret in tpair (tpair (rfromS (m2 * m9 + m5 * m8)) (rfromS (cos (sfromR (tproject2 (tproject1 m1))) * (sfromR (tproject1 (tproject1 m1)) * m9) + cos (sfromR (tproject2 (tproject1 m1))) * (sfromR (tproject1 (tproject1 m1)) * m8)))) (rfromS ((m3 * m4) * sfromR dret + m6 * sfromR dret))"

testGradFooMatrixSimpPP :: Assertion
testGradFooMatrixSimpPP = do
  resetVarCounter
  (let ftk = FTKR (2 :$: 2 :$: ZSR) (FTKScalar @Double)
    in printArtifactPretty (simplifyArtifact $ revArtifactAdapt UseIncomingCotangent foo2 (FTKProduct (FTKProduct ftk ftk) ftk)))
      @?= "\\dret m1 -> tfromS (STKProduct (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (STKR (SNat @2) STKScalar)) (let m2 = sin (sfromR (tproject2 (tproject1 m1))) ; m3 = sfromR (tproject1 (tproject1 m1)) * m2 ; m4 = recip (sfromR (tproject2 m1) * sfromR (tproject2 m1) + m3 * m3) ; m5 = sin (sfromR (tproject2 (tproject1 m1))) ; m8 = sfromR (tproject2 m1) * sfromR dret ; m9 = (negate (sfromR (tproject2 m1)) * m4) * sfromR dret in tpair (tpair (m2 * m9 + m5 * m8) (cos (sfromR (tproject2 (tproject1 m1))) * (sfromR (tproject1 (tproject1 m1)) * m9) + cos (sfromR (tproject2 (tproject1 m1))) * (sfromR (tproject1 (tproject1 m1)) * m8))) ((m3 * m4) * sfromR dret + (sfromR (tproject1 (tproject1 m1)) * m5) * sfromR dret))"

gradFooScalar :: forall r. r ~ Double
              => (r, r, r) -> (r, r, r)
gradFooScalar = fromDValue . grad foo2 . fromValue

testGradFooScalar :: Assertion
testGradFooScalar =
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (gradFooScalar (1.1, 2.2, 3.3))

gradCFooScalar :: forall r. r ~ Float
               => (r, r, r) -> (r, r, r)
gradCFooScalar = fromDValue . cgrad foo2 . fromValue

testGradCFooScalar :: Assertion
testGradCFooScalar =
  assertEqualUpToEpsilon 1e-10
    (2.4396284,-1.9533751,0.96548253)
    (gradCFooScalar (1.1, 2.2, 3.3))

testFooS :: Assertion
testFooS = do
  assertEqualUpToEpsilon 1e-10
    (srepl 2.4396285219055063, srepl (-1.953374825727421), srepl 0.9654825811012627)
    (grad (kfromS @_ @Double . ssum0 @'[3, 534, 3] @(TKScalar Double) . foo2) (srepl 1.1, srepl 2.2, srepl 3.3))

testFooSToFloat :: Assertion
testFooSToFloat = do
  assertEqualUpToEpsilon 1e-5
    (srepl 2.4396285219055063, srepl (-1.953374825727421), srepl 0.9654825811012627)
    (grad (kfromS @_ @Float . ssum0 . scast . foo2)
         (srepl 1.1 :: Concrete (TKS '[3, 534, 3] Double), srepl 2.2, srepl 3.3))

testFooSBoth :: Assertion
testFooSBoth = do
  assertEqualUpToEpsilon 1e-5
    (srepl 2.439628436155373, srepl (-1.9533749), srepl 0.9654825479484146)
    (grad (kfromS @_ @Float . ssum0 . scast . foo2 . (\(d, f, d2) -> (d, scast f, d2)))
         ( srepl 1.1 :: Concrete (TKS '[3, 534, 3] Double)
         , srepl 2.2 :: Concrete (TKS '[3, 534, 3] Float)
         , srepl 3.3 ))

testFooBoth :: Assertion
testFooBoth = do
  assertEqualUpToEpsilon 1e-5
    (rscalar 2.439628436155373, rscalar (-1.9533749), rscalar 0.9654825479484146)
    (grad (kfromR @_ @Float . rcast . foo2 . (\(d, f, d2) -> (d, rcast f, d2)))
         ( rscalar 1.1 :: Concrete (TKR 0 Double)
         , rscalar 2.2 :: Concrete (TKR 0 Float)
         , rscalar 3.3 ))

-- Add arrays a,b,c, but shifting b and c one to left/right
-- and then remove the first and last element.
--
-- In PyTorch
-- vstack( a[0] + b[1]
--       , a[1:N-1] + b[2:N] + c[:N-2]
--       , a[N-1] + c[N-2] )
vstackABC :: (ADReady target, GoodScalar r)
          => (target (TKR 1 r), target (TKR 1 r), target (TKR 1 r))
          -> target (TKR 1 r)
vstackABC (a, b, c) =
  let n = rwidth a
  in rconcat [ rreplicate 1 (a ! [0] + b ! [1])
             , rslice 1 (n - 2) a + rslice 2 (n - 2) b + rslice 0 (n - 2) c
             , rreplicate 1 (a ! [fromIntegral n - 1]
                             + c ! [fromIntegral n - 2]) ]

vstackBuild :: (ADReady target, GoodScalar r)
            => (target (TKR 1 r), target (TKR 1 r), target (TKR 1 r))
            -> target (TKR 1 r)
vstackBuild (a, b, c) =
  let n = rwidth a
  in rbuild1 n (\i ->
       ifH (i ==. 0)
           (a ! [0] + b ! [1])
           (ifH (i ==. fromIntegral n - 1)
                (a ! [fromIntegral n - 1] + c ! [fromIntegral n - 2])
                (a ! [i] + b ! [i + 1] + c ! [i - 1])))

testTrustVstackConcatRepl10 :: Assertion
testTrustVstackConcatRepl10 = do
  vstackABC @Concrete @Double (rrepl [10] 1, rrepl [10] 2, rrepl [10] 3)
  @?= rfromListLinear [10] [3.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,6.0,4.0]

testTrustVstackConcatIota10 :: Assertion
testTrustVstackConcatIota10 = do
  vstackABC @Concrete @Double (riota 10, riota 10, riota 10)
  @?= rfromListLinear [10] [1.0,3.0,6.0,9.0,12.0,15.0,18.0,21.0,24.0,17.0]

replIota :: (ADReady target, GoodScalar r)
         => Int -> (target (TKR 1 r), target (TKR 1 r), target (TKR 1 r))
replIota n =
  ( rconcrete (unConcrete $ rrepl [n] 1 * riota n)
  , rconcrete (unConcrete $ rrepl [n] 2 * riota n)
  , rconcrete (unConcrete $ rrepl [n] 3 * riota n) )

testTrustVstackConcatReplIota10 :: Assertion
testTrustVstackConcatReplIota10 = do
  vstackABC @Concrete @Double (replIota 10)
  @?= rfromListLinear [10] [2.0,5.0,11.0,17.0,23.0,29.0,35.0,41.0,47.0,33.0]

nN :: Int
nN = (round :: Double -> Int) 1e6  -- 1e6

trustedResult :: Concrete (TKR 1 Double)
trustedResult =
  rcast (vstackABC @Concrete @Float (replIota nN))
    -- the cast prevents computation sharing with the first test below

testVstackWarmup :: Assertion
testVstackWarmup = do
  trustedResult
  @?= trustedResult

testVstackConcatConcrete :: Assertion
testVstackConcatConcrete = do
  vstackABC @Concrete @Double (replIota nN)
  @?= trustedResult

testVstackBuildConcrete :: Assertion
testVstackBuildConcrete = do
  vstackBuild @Concrete @Double (replIota nN)
  @?= trustedResult

testVstackConcatAst :: Assertion
testVstackConcatAst = do
  interpretAstFull @Concrete
    emptyEnv
    (vstackABC @(AstTensor AstMethodLet FullSpan) @Double
               (replIota nN))
  @?= trustedResult

testVstackBuildAst :: Assertion
testVstackBuildAst = do
  interpretAstFull @Concrete
    emptyEnv
    (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                 (replIota nN))
  @?= trustedResult

testVstackBuildAstSimp :: Assertion
testVstackBuildAstSimp = do
  interpretAstFull @Concrete
    emptyEnv
      (simplifyInlineContract
         (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                      (replIota nN)))
  @?= trustedResult

testVstackBuildAstPP :: Assertion
testVstackBuildAstPP = do
  resetVarCounter
  let (var3, ast3) =
        funToAst (FTKProduct (FTKProduct (FTKR [10] FTKScalar) (FTKR [10] FTKScalar)) (FTKR [10] FTKScalar))
          Nothing (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double . fromTarget)
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstPretty ast3
    @?= "\\v1 -> rfromS (let v9 = sreplicate @10 (sfromR (tproject1 (tproject1 v1)) !$ [0] + sfromR (tproject2 (tproject1 v1)) !$ [1]) ; v10 = let v6 = sreplicate @10 (sfromR (tproject1 (tproject1 v1)) !$ [9] + sfromR (tproject2 v1) !$ [8]) ; v7 = (sfromR (tproject1 (tproject1 v1)) + sappend (sslice (SNat @1) (SNat @9) (sfromR (tproject2 (tproject1 v1)))) (sconcrete (sfromListLinear [1] [0.0]))) + sappend (sconcrete (sfromListLinear [1] [0.0])) (sslice (SNat @0) (SNat @9) (sfromR (tproject2 v1))) in sappend (sslice (SNat @0) (SNat @9) v7) (sreplicate @1 (v6 !$ [9])) in sappend (sreplicate @1 (v9 !$ [0])) (sslice (SNat @1) (SNat @9) v10))"
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstPretty (simplifyInlineContract ast3)
    @?= "\\v1 -> rfromS (sappend (sreplicate @1 (sfromR (tproject1 (tproject1 v1)) !$ [0] + sfromR (tproject2 (tproject1 v1)) !$ [1])) (sappend ((sslice (SNat @1) (SNat @8) (sfromR (tproject1 (tproject1 v1))) + sslice (SNat @2) (SNat @8) (sfromR (tproject2 (tproject1 v1)))) + sslice (SNat @0) (SNat @8) (sfromR (tproject2 v1))) (sreplicate @1 (sfromR (tproject1 (tproject1 v1)) !$ [9] + sfromR (tproject2 v1) !$ [8]))))"

{- The above is:
\v1 ->
  rfromS
    (sappend
       (sreplicate @1
          (sfromR (tproject1 (tproject1 v1)) !$ [0] +
           sfromR (tproject2 (tproject1 v1)) !$ [1]))
       (sappend
          ((sslice (SNat @1) (SNat @8) (sfromR (tproject1 (tproject1 v1))) +
            sslice (SNat @2) (SNat @8) (sfromR (tproject2 (tproject1 v1)))) +
           sslice (SNat @0) (SNat @8) (sfromR (tproject2 v1)))
          (sreplicate @1
             (sfromR (tproject1 (tproject1 v1)) !$ [9] +
              sfromR (tproject2 v1) !$ [8]))))
-}

replIota2 :: (ADReady target, GoodScalar r)
          => Int -> (target (TKR 1 r), target (TKR 1 r), target (TKR 1 r))
replIota2 n =
  (rrepl [n] 1 * riota n, rrepl [n] 2 * riota n, rrepl [n] 3 * riota n)

testVstackConcatConcrete2 :: Assertion
testVstackConcatConcrete2 = do
  vstackABC @Concrete @Double (replIota nN)
  @?= trustedResult

testVstackBuildConcrete2 :: Assertion
testVstackBuildConcrete2 = do
  vstackBuild @Concrete @Double (replIota2 nN)
  @?= trustedResult

testVstackConcatAst2 :: Assertion
testVstackConcatAst2 = do
  interpretAstFull @Concrete
    emptyEnv
    (vstackABC @(AstTensor AstMethodLet FullSpan) @Double
               (replIota2 nN))
  @?= trustedResult

testVstackBuildAst2 :: Assertion
testVstackBuildAst2 = do
  interpretAstFull @Concrete
    emptyEnv
    (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                 (replIota2 nN))
  @?= trustedResult

testVstackBuildAstSimp2 :: Assertion
testVstackBuildAstSimp2 = do
  interpretAstFull @Concrete
    emptyEnv
      (simplifyInlineContract
         (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                      (replIota2 nN)))
  @?= trustedResult

testVstackBuildAstPP2 :: Assertion
testVstackBuildAstPP2 = do
  resetVarCounter
  (printAstPretty
     (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                  (replIota2 10)))
    @?= "rfromS (let v8 = sreplicate @10 (sscalar 1.0 * sfromIntegral (sscalar 0) + sscalar 2.0 * sfromIntegral (sscalar 1)) ; v9 = let v5 = sreplicate @10 (sscalar 1.0 * sfromIntegral (sscalar 9) + sscalar 3.0 * sfromIntegral (sscalar 8)) ; v6 = (sconcrete (sreplicate [10] 1.0) * siota (SNat @10) + sconcrete (sfromListLinear [10] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,0.0]) * sfromIntegral (sreplicate @10 (sscalar 1) + siota (SNat @10))) + sconcrete (sfromListLinear [10] [0.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0,3.0]) * sfromIntegral (sreplicate @10 (sscalar (-1)) + siota (SNat @10)) in sappend (sslice (SNat @0) (SNat @9) v6) (sreplicate @1 (v5 !$ [9])) in sappend (sreplicate @1 (v8 !$ [0])) (sslice (SNat @1) (SNat @9) v9))"
  (printAstPretty
     (simplifyInlineContract
        (vstackBuild @(AstTensor AstMethodLet FullSpan) @Double
                     (replIota2 10))))
    @?= "rfromS (sconcrete (sfromListLinear [10] [2.0,5.0,11.0,17.0,23.0,29.0,35.0,41.0,47.0,33.0]))"

testFooPP :: Assertion
testFooPP = do
  resetVarCounter
  let fooT = foo2 @(AstTensor AstMethodLet FullSpan (TKR 0 Double))
      foo3 x = fooT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR FTKScalar) Nothing foo3
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\x1 -> rfromS (atan2H (sfromR x1) (sfromR x1 * sin (sfromR x1)) + sfromR x1 * (sfromR x1 * sin (sfromR x1)))"
  resetVarCounter
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fooT (FTKProduct (FTKProduct (FTKR ZSR FTKScalar) (FTKR ZSR FTKScalar)) (FTKR ZSR FTKScalar))
  printArtifactSimple artifactRev
    @?= "\\dret x1 -> tlet (sin (sfromR (tproject2 (tproject1 x1)))) (\\x2 -> tlet (sfromR (tproject1 (tproject1 x1)) * x2) (\\x3 -> tlet (recip (sfromR (tproject2 x1) * sfromR (tproject2 x1) + x3 * x3)) (\\x4 -> tlet (sin (sfromR (tproject2 (tproject1 x1)))) (\\x5 -> tlet (sfromR (tproject1 (tproject1 x1)) * x5) (\\x6 -> tlet (sfromR (tproject2 x1) * sfromR dret) (\\x8 -> tlet ((negate (sfromR (tproject2 x1)) * x4) * sfromR dret) (\\x9 -> tpair (tpair (rfromS (x2 * x9 + x5 * x8)) (rfromS (cos (sfromR (tproject2 (tproject1 x1))) * (sfromR (tproject1 (tproject1 x1)) * x9) + cos (sfromR (tproject2 (tproject1 x1))) * (sfromR (tproject1 (tproject1 x1)) * x8)))) (rfromS ((x3 * x4) * sfromR dret + x6 * sfromR dret)))))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\x1 -> tlet (sin (sfromR (tproject2 (tproject1 x1)))) (\\x2 -> tlet (sfromR (tproject1 (tproject1 x1)) * x2) (\\x3 -> tlet (sin (sfromR (tproject2 (tproject1 x1)))) (\\x5 -> tlet (sfromR (tproject1 (tproject1 x1)) * x5) (\\x6 -> rfromS (atan2H (sfromR (tproject2 x1)) x3 + sfromR (tproject2 x1) * x6)))))"

fooLetOld :: forall target r n.
          (RealFloatH (target (TKR n r)), LetTensor target)
       => (target (TKR n r), target (TKR n r), target (TKR n r)) -> target (TKR n r)
fooLetOld (x, y, z) =
  let w0 = x * sin y
  in tlet w0 $ \w ->
     atan2H z w + z * w

testFooLet :: Assertion
testFooLet = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (grad (kfromR @_ @Double . fooLetOld) (rscalar 1.1, rscalar 2.2, rscalar 3.3))

testFooLetPP :: Assertion
testFooLetPP = do
  resetVarCounter
  let fooLetT = fooLetOld @(AstTensor AstMethodLet FullSpan) @Double
      fooLet3 x = fooLetT (x, x, x)
      (var3, ast3) = funToAst (FTKR ZSR FTKScalar) Nothing fooLet3
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\x1 -> rfromS (tlet (sfromR x1 * sin (sfromR x1)) (\\x2 -> atan2H (sfromR x1) x2 + sfromR x1 * x2))"
  resetVarCounter
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fooLetT (FTKProduct (FTKProduct (FTKR ZSR FTKScalar) (FTKR ZSR FTKScalar)) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKProduct (STKR (SNat @0) STKScalar) (STKR (SNat @0) STKScalar)) (STKR (SNat @0) STKScalar)) (let x3 = sin (sfromR (tproject2 (tproject1 x1))) ; x4 = sfromR (tproject1 (tproject1 x1)) * x3 ; x5 = recip (sfromR (tproject2 x1) * sfromR (tproject2 x1) + x4 * x4) ; x7 = (negate (sfromR (tproject2 x1)) * x5) * sfromR dret + sfromR (tproject2 x1) * sfromR dret in tpair (tpair (x3 * x7) (cos (sfromR (tproject2 (tproject1 x1))) * (sfromR (tproject1 (tproject1 x1)) * x7))) ((x4 * x5) * sfromR dret + x4 * sfromR dret))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (let x4 = sfromR (tproject1 (tproject1 x1)) * sin (sfromR (tproject2 (tproject1 x1))) in atan2H (sfromR (tproject2 x1)) x4 + sfromR (tproject2 x1) * x4)"

shapedListProd :: forall k target r. (BaseTensor target, GoodScalar r)
               => ListR k (target (TKS '[] r)) -> target (TKS '[] r)
shapedListProd = foldr1 (*)

testListProdPP :: Assertion
testListProdPP = do
  resetVarCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKS '[] Double)) -> AstTensor AstMethodLet FullSpan (TKS '[] Double)
      fT = shapedListProd
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKS ZSS FTKScalar) (FTKProduct (FTKS ZSS FTKScalar) (FTKProduct (FTKS ZSS FTKScalar) (FTKProduct (FTKS ZSS FTKScalar) ftkUnit))))
  printArtifactSimple artifactRev
    @?= "\\dret x1 -> tlet (tproject1 (tproject2 (tproject2 x1)) * tproject1 (tproject2 (tproject2 (tproject2 x1)))) (\\x2 -> tlet (tproject1 (tproject2 x1) * x2) (\\x3 -> tlet (tproject1 x1 * dret) (\\x5 -> tlet (tproject1 (tproject2 x1) * x5) (\\x6 -> tpair (x3 * dret) (tpair (x2 * x5) (tpair (tproject1 (tproject2 (tproject2 (tproject2 x1))) * x6) (tpair (tproject1 (tproject2 (tproject2 x1)) * x6) Z0)))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\x1 -> tlet (tproject1 (tproject2 (tproject2 x1)) * tproject1 (tproject2 (tproject2 (tproject2 x1)))) (\\x2 -> tlet (tproject1 (tproject2 x1) * x2) (\\x3 -> tproject1 x1 * x3))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> let x2 = tproject1 (tproject2 (tproject2 x1)) * tproject1 (tproject2 (tproject2 (tproject2 x1))) ; x5 = tproject1 x1 * dret ; x6 = tproject1 (tproject2 x1) * x5 in tpair ((tproject1 (tproject2 x1) * x2) * dret) (tpair (x2 * x5) (tpair (tproject1 (tproject2 (tproject2 (tproject2 x1))) * x6) (tpair (tproject1 (tproject2 (tproject2 x1)) * x6) Z0)))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> tproject1 x1 * (tproject1 (tproject2 x1) * (tproject1 (tproject2 (tproject2 x1)) * tproject1 (tproject2 (tproject2 (tproject2 x1)))))"

rankedListProdr :: forall k target r. (BaseTensor target, GoodScalar r)
                => ListR k (target (TKR 0 r)) -> target (TKR 0 r)
rankedListProdr = foldr1 (*)

testListProdrPP :: Assertion
testListProdrPP = do
  resetVarCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListProdr
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x2 = sfromR (tproject1 (tproject2 (tproject2 x1))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) ; x5 = sfromR (tproject1 x1) * sfromR dret ; x6 = sfromR (tproject1 (tproject2 x1)) * x5 in tpair ((sfromR (tproject1 (tproject2 x1)) * x2) * sfromR dret) (tpair (x2 * x5) (tpair (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x6) (tpair (sfromR (tproject1 (tproject2 (tproject2 x1))) * x6) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sfromR (tproject1 x1) * (sfromR (tproject1 (tproject2 x1)) * (sfromR (tproject1 (tproject2 (tproject2 x1))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

testListProdrLongPP :: Assertion
testListProdrLongPP = do
  resetVarCounter
  let fT :: ListR 13 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListProdr
  let (artifactRev, _) =
        revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit)))))))))))))
  printArtifactSimple artifactRev
    @?= "\\dret x1 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))))) (\\x2 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * x2) (\\x3 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * x3) (\\x4 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * x4) (\\x5 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * x5) (\\x6 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * x6) (\\x7 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * x7) (\\x8 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * x8) (\\x9 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x9) (\\x10 -> tlet (sfromR (tproject1 (tproject2 (tproject2 x1))) * x10) (\\x11 -> tlet (sfromR (tproject1 (tproject2 x1)) * x11) (\\x12 -> tlet (sfromR (tproject1 x1) * sfromR dret) (\\x14 -> tlet (sfromR (tproject1 (tproject2 x1)) * x14) (\\x15 -> tlet (sfromR (tproject1 (tproject2 (tproject2 x1))) * x15) (\\x16 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x16) (\\x17 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * x17) (\\x18 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * x18) (\\x19 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * x19) (\\x20 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * x20) (\\x21 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * x21) (\\x22 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * x22) (\\x23 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * x23) (\\x24 -> tpair (rfromS (x12 * sfromR dret)) (tpair (rfromS (x11 * x14)) (tpair (rfromS (x10 * x15)) (tpair (rfromS (x9 * x16)) (tpair (rfromS (x8 * x17)) (tpair (rfromS (x7 * x18)) (tpair (rfromS (x6 * x19)) (tpair (rfromS (x5 * x20)) (tpair (rfromS (x4 * x21)) (tpair (rfromS (x3 * x22)) (tpair (rfromS (x2 * x23)) (tpair (rfromS (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))))) * x24)) (tpair (rfromS (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * x24)) Z0))))))))))))))))))))))))))))))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\x1 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))))) (\\x2 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * x2) (\\x3 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * x3) (\\x4 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * x4) (\\x5 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * x5) (\\x6 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * x6) (\\x7 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * x7) (\\x8 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * x8) (\\x9 -> tlet (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x9) (\\x10 -> tlet (sfromR (tproject1 (tproject2 (tproject2 x1))) * x10) (\\x11 -> tlet (sfromR (tproject1 (tproject2 x1)) * x11) (\\x12 -> rfromS (sfromR (tproject1 x1) * x12))))))))))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar))))))))))))) (let x2 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))))) ; x3 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * x2 ; x4 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * x3 ; x5 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * x4 ; x6 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * x5 ; x7 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * x6 ; x8 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * x7 ; x9 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * x8 ; x10 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x9 ; x11 = sfromR (tproject1 (tproject2 (tproject2 x1))) * x10 ; x14 = sfromR (tproject1 x1) * sfromR dret ; x15 = sfromR (tproject1 (tproject2 x1)) * x14 ; x16 = sfromR (tproject1 (tproject2 (tproject2 x1))) * x15 ; x17 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x16 ; x18 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * x17 ; x19 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * x18 ; x20 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * x19 ; x21 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * x20 ; x22 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * x21 ; x23 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * x22 ; x24 = sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * x23 in tpair ((sfromR (tproject1 (tproject2 x1)) * x11) * sfromR dret) (tpair (x11 * x14) (tpair (x10 * x15) (tpair (x9 * x16) (tpair (x8 * x17) (tpair (x7 * x18) (tpair (x6 * x19) (tpair (x5 * x20) (tpair (x4 * x21) (tpair (x3 * x22) (tpair (x2 * x23) (tpair (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))))) * x24) (tpair (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * x24) Z0)))))))))))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sfromR (tproject1 x1) * (sfromR (tproject1 (tproject2 x1)) * (sfromR (tproject1 (tproject2 (tproject2 x1))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 x1))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1))))))))))) * (sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x1)))))))))))))))))))))))))"

testListProd :: Assertion
testListProd = do
  assertEqualUpToEpsilon 1e-10
    [srepl 24, srepl 12, srepl 8, srepl 6]
    (grad (kfromS @_ @Double . shapedListProd @4) [srepl 1, srepl 2, srepl 3, srepl 4])

testListProdr :: Assertion
testListProdr = do
  assertEqualUpToEpsilon 1e-10
    [rscalar 24, rscalar 12, rscalar 8, rscalar 6]
    (grad (kfromR @_ @Double . rankedListProdr @4) [rscalar 1, rscalar 2, rscalar 3, rscalar 4])

rankedListSumr :: (BaseTensor target, GoodScalar r)
               => ListR 4 (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSumr = foldr1 (+)

testListSumrPP :: Assertion
testListSumrPP = do
  resetVarCounter >> resetIdCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSumr
  let (artifactRev, deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tpair dret (tpair dret (tpair dret (tpair dret Z0)))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sfromR (tproject1 x1) + (sfromR (tproject1 (tproject2 x1)) + (sfromR (tproject1 (tproject2 (tproject2 x1))) + sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"
  show deltas
    @?= "DeltaFromS (STKR (SNat @0) STKScalar) (DeltaShare 100000003 (DeltaAdd (DeltaSFromR [] (DeltaInput (InputId 0))) (DeltaShare 100000002 (DeltaAdd (DeltaSFromR [] (DeltaInput (InputId 1))) (DeltaShare 100000001 (DeltaAdd (DeltaSFromR [] (DeltaInput (InputId 2))) (DeltaSFromR [] (DeltaInput (InputId 3)))))))))"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum2r :: (BaseTensor target, GoodScalar r)
                => ListR 4 (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSum2r = foldr1 (\x y -> x + rscalar 2 * y)

testListSum2rPP :: Assertion
testListSum2rPP = do
  resetVarCounter
  let fT ::  ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSum2r
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x5 = sscalar 2.0 * sfromR dret ; x6 = sscalar 2.0 * x5 in tpair dret (tpair x5 (tpair x6 (tpair (sscalar 2.0 * x6) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sfromR (tproject1 x1) + (sscalar 2.0 * sfromR (tproject1 (tproject2 x1)) + (sscalar 4.0 * sfromR (tproject1 (tproject2 (tproject2 x1))) + sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

rankedListSum22r :: (BaseTensor target, GoodScalar r)
                 => ListR 4 (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSum22r = foldr1 (\x y -> rscalar 2 * x + rscalar 2 * y)

testListSum22rPP :: Assertion
testListSum22rPP = do
  resetVarCounter
  let fT ::  ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSum22r
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x5 = sscalar 2.0 * sfromR dret ; x6 = sscalar 2.0 * x5 in tpair (sscalar 2.0 * sfromR dret) (tpair (sscalar 2.0 * x5) (tpair (sscalar 2.0 * x6) (tpair (sscalar 2.0 * x6) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * sfromR (tproject1 x1) + (sscalar 4.0 * sfromR (tproject1 (tproject2 x1)) + (sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 x1))) + sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

-- Note how this tlet did not change anything, in particular the sharing.
rankedListSumk22r :: ( BaseTensor target, LetTensor target
                     , GoodScalar r )
                 =>  ListR k (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSumk22r = foldr1 (\x y -> tlet (rscalar 2) (\k -> k * x + k * y))

testListSumk22rPP :: Assertion
testListSumk22rPP = do
  resetVarCounter
  let fT ::  ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSumk22r
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x5 = sscalar 2.0 * sfromR dret ; x6 = sscalar 2.0 * x5 in tpair (sscalar 2.0 * sfromR dret) (tpair (sscalar 2.0 * x5) (tpair (sscalar 2.0 * x6) (tpair (sscalar 2.0 * x6) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * sfromR (tproject1 x1) + (sscalar 4.0 * sfromR (tproject1 (tproject2 x1)) + (sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 x1))) + sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

rankedListSum2xpyr :: (BaseTensor target, GoodScalar r)
                   =>  ListR 4 (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSum2xpyr = foldr1 (\x y -> rscalar 2 * (x + y))

testListSum2xpyrPP :: Assertion
testListSum2xpyrPP = do
  resetVarCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSum2xpyr
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x6 = sscalar 2.0 * sfromR dret ; x7 = sscalar 2.0 * x6 ; x8 = sscalar 2.0 * x7 in tpair x6 (tpair x7 (tpair x8 (tpair x8 Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * sfromR (tproject1 x1) + (sscalar 4.0 * sfromR (tproject1 (tproject2 x1)) + (sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 x1))) + sscalar 8.0 * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

rankedListSum2xyr :: (BaseTensor target, GoodScalar r)
                  => ListR 4 (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSum2xyr = foldr1 (\x y -> rscalar 2 * (x * y))

testListSum2xyrPP :: Assertion
testListSum2xyrPP = do
  resetVarCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSum2xyr
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x3 = sscalar 2.0 * (sfromR (tproject1 (tproject2 (tproject2 x1))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1))))) ; x8 = sscalar 2.0 * sfromR dret ; x9 = sscalar 2.0 * (sfromR (tproject1 x1) * x8) ; x10 = sscalar 2.0 * (sfromR (tproject1 (tproject2 x1)) * x9) in tpair (sscalar 2.0 * ((sfromR (tproject1 (tproject2 x1)) * x3) * x8)) (tpair (x3 * x9) (tpair (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))) * x10) (tpair (sfromR (tproject1 (tproject2 (tproject2 x1))) * x10) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 8.0 * (sfromR (tproject1 x1) * (sfromR (tproject1 (tproject2 x1)) * (sfromR (tproject1 (tproject2 (tproject2 x1))) * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1))))))))"

ranked2xy :: (BaseTensor target, GoodScalar r)
          => (target (TKR 0 r), target (TKR 0 r)) -> target (TKR 0 r)
ranked2xy = \(x, y) -> rscalar 2 * x * y

test2xyPP :: Assertion
test2xyPP = do
  resetVarCounter
  let fT :: (AstTensor AstMethodLet FullSpan (TKR 0 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
         -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = ranked2xy
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKR (SNat @0) STKScalar)) (tpair (sscalar 2.0 * (sfromR (tproject2 x1) * sfromR dret)) (sscalar 2.0 * (sfromR (tproject1 x1) * sfromR dret)))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * (sfromR (tproject1 x1) * sfromR (tproject2 x1)))"

-- Note that the function is not associative, so foldr vs foldl matters.
rankedListSum23r :: forall k target r. (BaseTensor target, GoodScalar r)
                 => ListR k (target (TKR 0 r)) -> target (TKR 0 r)
rankedListSum23r = foldr1 (\x y -> rscalar 2 * x + rscalar 3 * y)

testListSum23rPP :: Assertion
testListSum23rPP = do
  resetVarCounter
  let fT :: ListR 4 (AstTensor AstMethodLet FullSpan (TKR 0 Double)) -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = rankedListSum23r
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) (FTKProduct (FTKR ZSR FTKScalar) ftkUnit))))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) (STKProduct (STKR (SNat @0) STKScalar) STKScalar)))) (let x5 = sscalar 3.0 * sfromR dret ; x6 = sscalar 3.0 * x5 in tpair (sscalar 2.0 * sfromR dret) (tpair (sscalar 2.0 * x5) (tpair (sscalar 2.0 * x6) (tpair (sscalar 3.0 * x6) Z0))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * sfromR (tproject1 x1) + (sscalar 6.0 * sfromR (tproject1 (tproject2 x1)) + (sscalar 18.0 * sfromR (tproject1 (tproject2 (tproject2 x1))) + sscalar 27.0 * sfromR (tproject1 (tproject2 (tproject2 (tproject2 x1)))))))"

ranked23 :: (BaseTensor target, GoodScalar r)
         => (target (TKR 0 r), target (TKR 0 r)) -> target (TKR 0 r)
ranked23 = \(x, y) -> rscalar 2 * x + rscalar 3 * y

test23PP :: Assertion
test23PP = do
  resetVarCounter
  let fT :: (AstTensor AstMethodLet FullSpan (TKR 0 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
         -> AstTensor AstMethodLet FullSpan (TKR 0 Double)
      fT = ranked23
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent fT (FTKProduct (FTKR ZSR FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret x1 -> tfromS (STKProduct (STKR (SNat @0) STKScalar) (STKR (SNat @0) STKScalar)) (tpair (sscalar 2.0 * sfromR dret) (sscalar 3.0 * sfromR dret))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\x1 -> rfromS (sscalar 2.0 * sfromR (tproject1 x1) + sscalar 3.0 * sfromR (tproject2 x1))"

reluPrimal
  :: forall target n r.
     (ADReady target, GoodScalar r, KnownNat n, Differentiable r)
  => target (TKR n r) -> target (TKR n r)
reluPrimal v =
  let oneIfGtZero = rmap0N (\x -> ifH (x <=. rscalar 0) (rscalar 0.0) (rscalar 1.0))
                           (rprimalPart v)
  in scale2 oneIfGtZero v

scale2 :: forall target r n.
          (ADReady target, GoodScalar r, KnownNat n)
       => PrimalOf target (TKR n r) -> target (TKR n r) -> target (TKR n r)
scale2 a d = rfromPrimal @target a * d

testReluPP :: Assertion
testReluPP = do
  resetVarCounter >> resetIdCounter
  let reluT :: AstTensor AstMethodLet FullSpan (TKR 2 Double) -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT = reluPrimal
      (var3, ast3) = funToAst (FTKR [3, 4] FTKScalar) Nothing reluT
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> rfromS (tfromPrimal (STKS [3,4] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifH (tprimalPart (sfromR m1) !$ [i4, i3] <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * sfromR m1)"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactDelta UseIncomingCotangent reluT (FTKR [3, 4] FTKScalar)
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i5, i6])) 0 1]) * sfromR dret)"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i5, i6])) 0 1]) * sfromR m1)"
  show deltas
    @?= "DeltaFromS (STKR (SNat @2) STKScalar) (DeltaShare 100000003 (DeltaScale <primal> (DeltaSFromR [3,4] (DeltaInput (InputId 0)))))"

testReluPP2 :: Assertion
testReluPP2 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 1 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      reluT2 (t, r) = reluPrimal (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5] FTKScalar) Nothing (\t -> reluT2 (t, rscalar 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\v1 -> rfromS (tfromPrimal (STKS [5] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i2] -> [ifH (sfromR (rfromS (sscalar 7.0 * tprimalPart (sfromR v1) !$ [i2])) <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * (sfromR v1 * tfromPrimal (STKS [5] STKScalar) (sreplicate @5 (sscalar 7.0))))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKR [5] FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> tfromS (STKProduct (STKR (SNat @1) STKScalar) (STKR (SNat @0) STKScalar)) (let v9 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 v1) !$ [i3]) * sfromR (tproject2 v1)) 0 1]) * sfromR dret in tpair (sreplicate @5 (sfromR (tproject2 v1)) * v9) (sdot0 (sfromR (tproject1 v1)) v9))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 v1) !$ [i3]) * sfromR (tproject2 v1)) 0 1]) * (sfromR (tproject1 v1) * sreplicate @5 (sfromR (tproject2 v1))))"

testReluSimpler :: Assertion
testReluSimpler = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 relu (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluSimplerPP :: Assertion
testReluSimplerPP = do
  resetVarCounter >> resetIdCounter
  let reluT :: AstTensor AstMethodLet FullSpan (TKR 2 Double) -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT = relu
      (var3, ast3) = funToAst (FTKR [3, 4] FTKScalar) Nothing reluT
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> rfromS (tfromPrimal (STKS [3,4] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i4, i3] -> [ifH (tprimalPart (sfromR m1) !$ [i4, i3] <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * sfromR m1)"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactDelta UseIncomingCotangent reluT (FTKR [3, 4] FTKScalar)
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i5, i6])) 0 1]) * sfromR dret)"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i6] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i5, i6])) 0 1]) * sfromR m1)"
  show deltas
    @?= "DeltaFromS (STKR (SNat @2) STKScalar) (DeltaShare 100000003 (DeltaScale <primal> (DeltaSFromR [3,4] (DeltaInput (InputId 0)))))"

testReluSimplerPP2 :: Assertion
testReluSimplerPP2 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 1 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      reluT2 (t, r) = relu (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5] FTKScalar) Nothing (\t -> reluT2 (t, rscalar 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\v1 -> rfromS (tlet (sfromR v1 * tfromPrimal (STKS [5] STKScalar) (sreplicate @5 (sscalar 7.0))) (\\v2 -> tfromPrimal (STKS [5] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i3] -> [ifH (sfromR (tprimalPart (rfromS (v2 !$ [i3]))) <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * v2))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKR [5] FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> tfromS (STKProduct (STKR (SNat @1) STKScalar) (STKR (SNat @0) STKScalar)) (let v8 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 v1) !$ [i5]) * sfromR (tproject2 v1)) 0 1]) * sfromR dret in tpair (sreplicate @5 (sfromR (tproject2 v1)) * v8) (sdot0 (sfromR (tproject1 v1)) v8))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (let v4 = sfromR (tproject1 v1) * sreplicate @5 (sfromR (tproject2 v1)) in sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5] -> [ifH (sscalar -0.0 <=. negate (v4 !$ [i5])) 0 1]) * v4)"

testReluSimplerPP3 :: Assertion
testReluSimplerPP3 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 2 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
      (var3, ast3) = funToAst (FTKR [3, 4] FTKScalar) Nothing (\t -> reluT2 (t, rscalar 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> rfromS (tlet (sfromR m1 * tfromPrimal (STKS [3,4] STKScalar) (sreplicate @3 (sreplicate @4 (sscalar 7.0)))) (\\m2 -> tfromPrimal (STKS [3,4] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifH (tprimalPart m2 !$ [i5, i4] <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * m2))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKR [3, 4] FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @0) STKScalar)) (let m11 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 m1) !$ [i7, i8]) * sfromR (tproject2 m1)) 0 1]) * sfromR dret in tpair (sreplicate @3 (sreplicate @4 (sfromR (tproject2 m1))) * m11) (sdot0 (sfromR (tproject1 m1)) m11))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m6 = sfromR (tproject1 m1) * sreplicate @3 (sreplicate @4 (sfromR (tproject2 m1))) in sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (m6 !$ [i7, i8])) 0 1]) * m6)"

testReluSimpler3 :: Assertion
testReluSimpler3 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 2 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT2 (t, r) = relu (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (grad (kfromR . rsum0 . reluT2) (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testReluSimplerPP4 :: Assertion
testReluSimplerPP4 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 2 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
      (var3, ast3) = funToAst (FTKR [3, 4] FTKScalar) Nothing (\t -> reluT2 (t, rscalar 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> rfromS (tlet (sfromR m1 * tfromPrimal (STKS [3,4] STKScalar) (sreplicate @3 (sreplicate @4 (sscalar 7.0)))) (\\m2 -> tfromPrimal (STKS [3,4] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifH (tprimalPart m2 !$ [i5, i4] <=. sfromR (rfromS (sscalar 0.0))) 0 1])) * m2))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKR [3, 4] FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @0) STKScalar)) (let m11 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 m1) !$ [i7, i8]) * sfromR (tproject2 m1)) 0 1]) * sfromR dret in tpair (sreplicate @3 (sreplicate @4 (sfromR (tproject2 m1))) * m11) (sdot0 (sfromR (tproject1 m1)) m11))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (let m6 = sfromR (tproject1 m1) * sreplicate @3 (sreplicate @4 (sfromR (tproject2 m1))) in sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (m6 !$ [i7, i8])) 0 1]) * m6)"

testReluSimpler4 :: Assertion
testReluSimpler4 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 2 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT2 (t, r) = relu (t * rreplicate0N [3, 4] r)
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (grad (kfromR . rsum0 . reluT2) (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testReluSimplerPP4s :: Assertion
testReluSimplerPP4s = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKS '[3, 4] Float), AstTensor AstMethodLet FullSpan (TKS '[] Float))
             -> AstTensor AstMethodLet FullSpan (TKS '[3, 4] Float)
      reluT2 (t, r) = reluS (t * sreplicate0N r)
      (var3, ast3) = funToAst (FTKS knownShS FTKScalar) Nothing (\t -> reluT2 (t, srepl 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> tlet (m1 * tfromPrimal (STKS [3,4] STKScalar) (sreplicate @3 (sreplicate @4 (sscalar 7.0)))) (\\m2 -> tfromPrimal (STKS [3,4] STKScalar) (sgather [] (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i5, i4] -> [ifH (sscalar -0.0 <=. negate (tprimalPart m2 !$ [i5, i4])) 0 1])) * m2)"

testReluSimplerPP4s2 :: Assertion
testReluSimplerPP4s2 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKS '[3, 4] Double), AstTensor AstMethodLet FullSpan (TKS '[] Double))
             -> AstTensor AstMethodLet FullSpan (TKS '[3, 4] Double)
      -- This is tweaked compared to above to avoid test artifacts coming
      -- from counter resets, which are inherently unsafe (cse, etc.).
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKS [3, 4] FTKScalar) (FTKS ZSS FTKScalar))
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m6 = tproject1 m1 * sreplicate @3 (sreplicate @4 (tproject2 m1)) ; m9 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (m6 !$ [i7, i8])) 0 1]) ; m11 = m9 * dret in tpair (sreplicate @3 (sreplicate @4 (tproject2 m1)) * m11) (ssum @4 (ssum @3 (tproject1 m1 * m11)))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> let m6 = tproject1 m1 * sreplicate @3 (sreplicate @4 (tproject2 m1)) ; m9 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (m6 !$ [i7, i8])) 0 1]) in m9 * m6"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> let m11 = sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (tproject1 m1 !$ [i7, i8]) * tproject2 m1) 0 1]) * dret in tpair (sreplicate @3 (sreplicate @4 (tproject2 m1)) * m11) (sdot0 (tproject1 m1) m11)"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> let m6 = tproject1 m1 * sreplicate @3 (sreplicate @4 (tproject2 m1)) in sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i7, i8] -> [ifH (sscalar -0.0 <=. negate (m6 !$ [i7, i8])) 0 1]) * m6"

testReluSimpler4s :: Assertion
testReluSimpler4s = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKS '[3, 4] Double), AstTensor AstMethodLet FullSpan (TKS '[] Double))
             -> AstTensor AstMethodLet FullSpan (TKS '[3, 4] Double)
      reluT2 (t, r) = reluS (t * sreplicate0N r)
  assertEqualUpToEpsilon 1e-10
    ( sconcrete
      $ Nested.sfromListPrimLinear @_ @'[3, 4] knownShS [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , srepl 57.1 )
    (grad (kfromS . ssum0 . reluT2) (sconcrete $ Nested.sfromListPrimLinear @_ @'[3, 4] knownShS [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], srepl 7))

reluMax :: forall target n r. (ADReady target, GoodScalar r, KnownNat n)
        => target (TKR n r) -> target (TKR n r)
reluMax = rmap0N (maxH (rscalar 0))

testReluMax :: Assertion
testReluMax = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3, 4] [1.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,0.0,0.0,1.0,1.0])
    (rev' @Double @2 reluMax (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12]))

testReluMaxPP :: Assertion
testReluMaxPP = do
  resetVarCounter >> resetIdCounter
  let reluT :: AstTensor AstMethodLet FullSpan (TKR 2 Double) -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT = reluMax
      (var3, ast3) = funToAst (FTKR [3, 4] FTKScalar) Nothing reluT
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\m1 -> rfromS (sgather [] (tfromVector (SNat @2) (STKS [3,4] STKScalar) (fromList [tfromPrimal (STKS [3,4] STKScalar) (sreplicate @3 (sreplicate @4 (sscalar 0.0))), sfromR m1])) (\\[i5, i4] -> [ifH (tprimalPart (sfromR m1) !$ [i5, i4] <=. sfromR (rfromS (sscalar 0.0))) 0 1, i5, i4]))"
  resetVarCounter
  let (artifactRev, deltas) = revArtifactDelta UseIncomingCotangent reluT (FTKR [3, 4] FTKScalar)
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> rfromS (sscatter (sfromR dret) (\\[i9, i10] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i9, i10])) 0 1, i9, i10]) !$ [1])"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (sgather (sfromVector (fromList [sconcrete (sreplicate [3,4] 0.0), sfromR m1])) (\\[i6, i7] -> [ifH (sscalar -0.0 <=. negate (sfromR m1 !$ [i6, i7])) 0 1, i6, i7]))"
  show deltas
    @?= "DeltaFromS (STKR (SNat @2) STKScalar) (DeltaShare 100000005 (DeltaGatherS [3,4] [] [2,3,4] (DeltaShare 100000003 (DeltaFromVector (SNat @2) (STKS [3,4] STKScalar) [DeltaZero (FTKS [3,4] FTKScalar),DeltaSFromR [3,4] (DeltaInput (InputId 0))])) <function>))"

testReluMaxPP2 :: Assertion
testReluMaxPP2 = do
  resetVarCounter
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 1 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 1 Double)
      reluT2 (t, r) = reluMax (t * rreplicate 5 r)
      (var3, ast3) = funToAst (FTKR [5] FTKScalar) Nothing (\t -> reluT2 (t, rscalar 7))
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\v1 -> rfromS (sgather [] (tfromVector (SNat @2) (STKS [5] STKScalar) (fromList [tfromPrimal (STKS [5] STKScalar) (sreplicate @5 (sscalar 0.0)), sfromR v1 * tfromPrimal (STKS [5] STKScalar) (sreplicate @5 (sscalar 7.0))])) (\\[i3] -> [ifH (sscalar 7.0 * tprimalPart (sfromR v1) !$ [i3] <=. sfromR (rfromS (sscalar 0.0))) 0 1, i3]))"
  resetVarCounter
  let (artifactRev, _deltas) = revArtifactDelta UseIncomingCotangent reluT2 (FTKProduct (FTKR [5] FTKScalar) (FTKR ZSR FTKScalar))
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> let m11 = sscatter (sfromR dret) (\\[i8] -> [let x9 = sfromR (tproject1 v1) !$ [i8] ; x10 = sfromR (rreplicate 5 (tproject2 v1)) !$ [i8] in ifH (sscalar -0.0 <=. negate x9 * x10) 0 1, i8]) ; v12 = m11 !$ [1] in tpair (rfromS (sfromR (rreplicate 5 (tproject2 v1)) * v12)) (rsum (rfromS (sfromR (tproject1 v1) * v12)))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> rfromS (sgather (sfromVector (fromList [sreplicate @5 (sscalar 0.0), sfromR (tproject1 v1) * sfromR (rreplicate 5 (tproject2 v1))])) (\\[i4] -> [let x5 = sfromR (tproject1 v1) !$ [i4] ; x6 = sfromR (rreplicate 5 (tproject2 v1)) !$ [i4] in ifH (sscalar -0.0 <=. negate x5 * x6) 0 1, i4]))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> tfromS (STKProduct (STKR (SNat @1) STKScalar) (STKR (SNat @0) STKScalar)) (let v12 = sscatter (sfromR dret) (\\[i8] -> [ifH (sscalar -0.0 <=. negate (sfromR (tproject1 v1) !$ [i8]) * sfromR (tproject2 v1)) 0 1, i8]) !$ [1] in tpair (sreplicate @5 (sfromR (tproject2 v1)) * v12) (sdot0 (sfromR (tproject1 v1)) v12))"

testReluMax3 :: Assertion
testReluMax3 = do
  let reluT2 :: (AstTensor AstMethodLet FullSpan (TKR 2 Double), AstTensor AstMethodLet FullSpan (TKR 0 Double))
             -> AstTensor AstMethodLet FullSpan (TKR 2 Double)
      reluT2 (t, r) = reluMax (t * rreplicate 3 (rreplicate 4 r))
  assertEqualUpToEpsilon 1e-10
    ( ringestData [3, 4] [7.0,0.0,0.0,7.0,7.0,7.0,7.0,7.0,0.0,0.0,7.0,7.0]
    , rscalar 57.1 )
    (grad (kfromR . rsum0 . reluT2) (ringestData [3, 4] [1.1, -2.2, 0, 4.4, 5.5, 6.6, 7.7, 8.8, -9.9, -10, 11, 12], rscalar 7))

testDot1PP :: Assertion
testDot1PP = do
  resetVarCounter
  let (artifactRev, _) =
        revArtifactDelta UseIncomingCotangent (uncurry (rdot0 @1 @Double))
                 (FTKProduct (FTKR [3] FTKScalar) (FTKR [3] FTKScalar))
  printArtifactPretty artifactRev
    @?= "\\dret v1 -> tpair (rfromS (sfromR (tproject2 v1) * sreplicate @3 (sfromR dret))) (rfromS (sfromR (tproject1 v1) * sreplicate @3 (sfromR dret)))"
  printArtifactPrimalPretty artifactRev
    @?= "\\v1 -> rfromS (ssum @3 (sfromR (tproject1 v1) * sfromR (tproject2 v1)))"

testDot2PP :: Assertion
testDot2PP = do
  resetVarCounter
  let (artifactRev, _deltas) =
        revArtifactDelta UseIncomingCotangent (uncurry (rdot0 @2 @Double))
                 (FTKProduct (FTKR [2, 3] FTKScalar) (FTKR [2, 3] FTKScalar))
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> let m3 = sreshape @[2,3] (sreplicate @6 (sfromR dret)) in tpair (rfromS (sfromR (tproject2 m1) * m3)) (rfromS (sfromR (tproject1 m1) * m3))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (ssum @6 (sreshape @[6] (sfromR (tproject1 m1) * sfromR (tproject2 m1))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (tpair (sfromR (tproject2 m1) * sreplicate @2 (sreplicate @3 (sfromR dret))) (sfromR (tproject1 m1) * sreplicate @2 (sreplicate @3 (sfromR dret))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (sdot0 (sfromR (tproject1 m1)) (sfromR (tproject2 m1)))"

testMatvecmulPP :: Assertion
testMatvecmulPP = do
  resetVarCounter
  let (artifactRev, _) =
        revArtifactDelta
                 UseIncomingCotangent (uncurry rmatvecmul)
                 (FTKProduct (FTKR [2, 3] FTKScalar) (FTKR [3] FTKScalar))
  printArtifactPretty @_ @(TKR 1 Double) artifactRev
    @?= "\\dret m1 -> tpair (rfromS (str (str (sreplicate @2 (sfromR (tproject2 m1))) * sreplicate @3 (sfromR dret)))) (rfromS (ssum @2 (str (str (sfromR (tproject1 m1)) * sreplicate @3 (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (ssum @3 (str (sreplicate @2 (sfromR (tproject2 m1))) * str (sfromR (tproject1 m1))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @1) STKScalar)) (tpair (sreplicate @2 (sfromR (tproject2 m1)) * str (sreplicate @3 (sfromR dret))) (ssdot1In (str (sfromR (tproject1 m1))) (sreplicate @3 (sfromR dret))))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (ssdot1In (sreplicate @2 (sfromR (tproject2 m1))) (sfromR (tproject1 m1)))"

testMatmul2PP :: Assertion
testMatmul2PP = do
  resetVarCounter
  let (artifactRev, _) =
        revArtifactDelta
                 UseIncomingCotangent (uncurry rmatmul2)
                 (FTKProduct (FTKR [2, 3] FTKScalar) (FTKR [3, 4] FTKScalar))
  printArtifactPretty @_ @(TKR 2 Double) artifactRev
    @?= "\\dret m1 -> tpair (rfromS (ssum @4 (stranspose @[2,1,0] (str (sreplicate @2 (sfromR (tproject2 m1))) * sreplicate @3 (sfromR dret))))) (rfromS (ssum @2 (str (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * sreplicate @3 (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (ssum @3 (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * str (sreplicate @2 (sfromR (tproject2 m1)))))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tfromS (STKProduct (STKR (SNat @2) STKScalar) (STKR (SNat @2) STKScalar)) (tpair (smatmul2 (sfromR dret) (str (sfromR (tproject2 m1)))) (smatmul2 (str (sfromR (tproject1 m1))) (sfromR dret)))"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> rfromS (smatmul2 (sfromR (tproject1 m1)) (sfromR (tproject2 m1)))"

testMatmul2FromMatvecmulPP :: Assertion
testMatmul2FromMatvecmulPP = do
  resetVarCounter
  let rmatmul2F :: (BaseTensor target, GoodScalar r)
                => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
      rmatmul2F m1 m2 =
        rbuild1 (rwidth m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
      (artifactRev, _) =
        revArtifactDelta
                 UseIncomingCotangent (uncurry rmatmul2F)
                 (FTKProduct (FTKR [2, 3] FTKScalar) (FTKR [3, 4] FTKScalar))
  printArtifactPretty @_ @(TKR 2 Double) artifactRev
    @?= "\\dret m1 -> tpair (rfromS (ssum @4 (stranspose @[2,1,0] (str (sreplicate @2 (sfromR (tproject2 m1))) * sreplicate @3 (sfromR dret))))) (rfromS (ssum @2 (str (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * sreplicate @3 (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (ssum @3 (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * str (sreplicate @2 (sfromR (tproject2 m1)))))"

testMatmul2PaperPP :: Assertion
testMatmul2PaperPP = do
  resetVarCounter
  let rmatmul2P :: (BaseTensor target, GoodScalar r)
                => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
      rmatmul2P a b =
        let k :$: m :$: _ = rshape a
            _ :$: n :$: _ = rshape b
        in rbuild1 k (\i ->
             rbuild1 n (\j ->
               rsum (rbuild1 m (\p -> a ! [i, p] * b ! [p, j]))))
      (artifactRev, _) =
        revArtifactDelta
                 UseIncomingCotangent (uncurry rmatmul2P)
                 (FTKProduct (FTKR [2, 3] FTKScalar) (FTKR [3, 4] FTKScalar))
  printArtifactPretty @_ @(TKR 2 Double) artifactRev
    @?= "\\dret m1 -> tpair (rfromS (ssum @4 (stranspose @[2,1,0] (str (sreplicate @2 (sfromR (tproject2 m1))) * sreplicate @3 (sfromR dret))))) (rfromS (ssum @2 (str (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * sreplicate @3 (sfromR dret)))))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> rfromS (ssum @3 (stranspose @[2,1,0] (sreplicate @4 (sfromR (tproject1 m1))) * str (sreplicate @2 (sfromR (tproject2 m1)))))"

testMatmul2PPS :: Assertion
testMatmul2PPS = do
  resetVarCounter
  let (artifactRev, _) =
        revArtifactDelta
                 UseIncomingCotangent (uncurry smatmul2)
                 (FTKProduct (FTKS (SNat @2 :$$ SNat @3 :$$ ZSS) (FTKScalar @Float)) (FTKS (SNat @3 :$$ SNat @4 :$$ ZSS) (FTKScalar @Float)))
  printArtifactPretty artifactRev
    @?= "\\dret m1 -> tpair (ssum @4 (stranspose @[2,1,0] (str (sreplicate @2 (tproject2 m1)) * sreplicate @3 dret))) (ssum @2 (str (stranspose @[2,1,0] (sreplicate @4 (tproject1 m1)) * sreplicate @3 dret)))"
  printArtifactPrimalPretty artifactRev
    @?= "\\m1 -> ssum @3 (stranspose @[2,1,0] (sreplicate @4 (tproject1 m1)) * str (sreplicate @2 (tproject2 m1)))"
  printArtifactPretty (simplifyArtifact artifactRev)
    @?= "\\dret m1 -> tpair (smatmul2 dret (str (tproject2 m1))) (smatmul2 (str (tproject1 m1)) dret)"
  printArtifactPrimalPretty (simplifyArtifact artifactRev)
    @?= "\\m1 -> smatmul2 (tproject1 m1) (tproject2 m1)"

testAddSpeedBig :: Assertion
testAddSpeedBig =
  let m1 :: Concrete (TKR 2 Double)
      m1 = ringestData [1000,1000] [1 .. 1000000]
      m2 = m1 + m1
  in assertEqualUpToEpsilon 1e-10 m2 m2

testMatmul2SpeedBig :: Assertion
testMatmul2SpeedBig =
  let m1 :: Concrete (TKR 2 Double)
      m1 = ringestData [1000,1000] [1 .. 1000000]
      m2 = rmatmul2 m1 m1
  in assertEqualUpToEpsilon 1e-10 m2 m2

bar :: forall a. RealFloatH a => (a, a) -> a
bar (x, y) =
  let w = foo2 (x, y, x) * sin y
  in atan2H x w + y * w

barF :: forall a. RealFloatH a => (a, a) -> a
barF (x, y) =
  let w = foo2 (x, y, x) * sin y
  in atan2H x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (rscalar 3.1435239435581166,rscalar (-1.1053869545195814))
    (cgrad (kfromR . bar @(ADVal Concrete (TKR 0 Double))) (rscalar 1.1, rscalar 2.2))

testBarS :: Assertion
testBarS =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (cgrad (kfromS . barF @(ADVal Concrete (TKS '[] Double))) (srepl 1.1, srepl 2.2))

testBar2S :: Assertion
testBar2S =
  assertEqualUpToEpsilon 1e-9
    (srepl 3.1435239435581166, srepl (-1.1053869545195814))
    (grad (kfromS . ssum0 . barF @(AstTensor AstMethodLet FullSpan (TKS '[52, 2, 2, 1, 1, 3] Double))) (srepl 1.1, srepl 2.2))

testBarCFwd :: Assertion
testBarCFwd =
  assertEqualUpToEpsilon 1e-9
    (rscalar 9.327500345189534e-2)
    (cjvp (bar @(ADVal Concrete (TKR 0 Double))) (rscalar 1.1, rscalar 2.2) (rscalar 0.1, rscalar 0.2))

testBarFwd :: Assertion
testBarFwd =
  assertEqualUpToEpsilon 1e-9
    (rscalar 9.327500345189534e-2)
    (jvp @_ @(TKR 0 Double)
         bar (rscalar 1.1, rscalar 2.2) (rscalar 0.1, rscalar 0.2))

barADVal2 :: forall a. RealFloatH a
          => (a, a, a) -> a
barADVal2 (x,y,z) =
  let w = foo2 (x,y,z) * sin y
  in atan2H z w + z * w

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
baz :: ( ADVal Concrete (TKR 0 Double)
       , ADVal Concrete (TKR 0 Double)
       , ADVal Concrete (TKR 0 Double) )
    -> ADVal Concrete (TKR 0 Double)
baz (_x,y,z) =
  let w = fooFromPrimal * barADVal2 (y,y,z) * sin y
  in atan2H z w + z * w

-- An "old term", computed once, stored at top level.
fooFromPrimal :: ADVal Concrete (TKR 0 Double)
fooFromPrimal = foo2 (rscalar 7, rscalar 8, rscalar 9)

testBaz :: Assertion
testBaz =
  assertEqualUpToEpsilon 1e-9
    (rscalar 0, rscalar (-5219.20995030263), rscalar 2782.276274462047)
    (cgrad (kfromR . baz) (rscalar 1.1, rscalar 2.2, rscalar 3.3))

-- If terms are numbered and @z@ is, wrongly, decorated with number 0,
-- here @fooFromPrimal@ is likely to clash with @z@, since it was numbered
-- starting from 0, too.
-- The test fails if term numbering is reset to 0 between gradient computation
-- runs (verified) as well as when delta-expression evaluation assumes
-- it can only encounter terms numbered in the current run and,
-- e.g., allocates an array with only that much space (not verified).
-- Actually, with term counter zeroed just before @cgrad@ application,
-- even a single @testBaz@ execution produces wrong results, but this test
-- is likely to fail in less naive implementations, as well.
testBazRenumbered :: Assertion
testBazRenumbered =
  assertEqualUpToEpsilon 1e-9
    (rscalar 0, rscalar (-5219.20995030263), rscalar 2783.276274462047)
    (cgrad (kfromR . (\(x,y,z) -> z + baz (x,y,z))) (rscalar 1.1, rscalar 2.2, rscalar 3.3))

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r. r ~ Double
     => ListR 3 (ADVal Concrete (TKR 0 r)) -> ADVal Concrete (TKR 0 r)
fooD (x ::: y ::: z ::: ZR) =
  let w = x * sin y
  in atan2H z w + z * w

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    (fromList [rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627])
    (cgrad (kfromR . fooD) (fromList [rscalar 1.1, rscalar 2.2, rscalar 3.3]))

fooBuild1 :: (ADReady target, GoodScalar r, Differentiable r)
          => target (TKR 1 r) -> target (TKR 1 r)
fooBuild1 v =
  let r = rsum0 v
      v' = rminimum v
  in rbuild1 3 $ \ix ->
       r * foo2 ( rscalar 3
               , rscalar 5 * r
               , r * rminimum v * v')
       + bar (r, rindex v [ix + 1])

testFooBuildDt :: Assertion
testFooBuildDt =
  assertEqualUpToEpsilon 1e-5
    (rconcrete $ Nested.rfromListPrimLinear [4] [-189890.46351219364,-233886.08744601303,-222532.22669716467,-206108.68889329425])
    (vjp @_ @(TKR 1 Double)
           fooBuild1 (ringestData [4] [1.1, 2.2, 3.3, 4]) (rreplicate0N [3] (rscalar 42)))

testFooBuildCFwd :: Assertion
testFooBuildCFwd =
  assertEqualUpToEpsilon 1e-5
    (rconcrete $ Nested.rfromListPrimLinear [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (cjvp @_ @(TKR 1 Double)
          fooBuild1 (ringestData [4] [1.1, 2.2, 3.3, 4]) (rreplicate0N [4] (rscalar 42)))

testFooBuildFwd :: Assertion
testFooBuildFwd =
  assertEqualUpToEpsilon 1e-5
    (rconcrete $ Nested.rfromListPrimLinear [3] [-296584.8166864211,-290062.472288043,-265770.1775742018])
    (jvp @_ @(TKR 1 Double)
         fooBuild1 (ringestData [4] [1.1, 2.2, 3.3, 4]) (rreplicate0N [4] (rscalar 42)))

testFooBuild :: Assertion
testFooBuild =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [4] [-4521.201512195087,-5568.7163677622175,-5298.386349932494,-4907.349735554627])
    (rev' @Double @1 fooBuild1 (ringestData [4] [1.1, 2.2, 3.3, 4]))

fooNoGo :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
        => target (TKR 1 r) -> target (TKR 1 r)
fooNoGo v =
  let r = rsum0 v
  in rbuild1 3 (\ix' -> let ix :: PrimalOf target (TKS '[] Int64)
                            ix = sfromR $ rfromK ix' in
       bar (rscalar 3.14, bar (rscalar 3.14, rindex v [kfromS $ (ix + (sprimalPart . sfloor . sfromR) r) `minH` sscalar 2 `maxH` sscalar 0]))
       + ifH ((&&*) (rindex @1 v [ix' * 2] <=. rscalar 0)
                    (sscalar 6 >. abs ix))
               r (rscalar 5 * r))
     / rslice 1 3 (rmap0N (\x -> ifH (x >. r) r x) v)
     * rbuild1 3 (const (rscalar 1))

testFooNoGo0 :: Assertion
testFooNoGo0 =
  assertEqualUpToEpsilon' 1e-6
   (ringestData [5] [5.037878787878788,-14.394255484765257,43.23648655081373,-0.8403418295960368,5.037878787878788])
   (rev' @Double @1 fooNoGo
         (ringestData [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall target r.
                  (ADReady target, GoodScalar r, Differentiable r)
               => target (TKR 0 r) -> target (TKR 1 r)
nestedBuildMap r =
  let w = rreplicate0N [4]
      v0' = rreplicate0N [177] r :: target (TKR 1 r)
  in tlet v0' $ \v' ->
    let nestedMap x0 = tlet x0 $ \x -> rmap0N (x /) (w x)
        variableLengthBuild iy = rbuild1 7 (\ix -> rindex v' (ix + iy :.: ZIR))
        doublyBuild = rbuild1 5 (rminimum . variableLengthBuild)
        fooMap1 :: target (TKR 0 r) -> target (TKR 1 r)
        fooMap1 r2 =
          let v = fooBuild1 $ rreplicate0N [130] r2
          in rmap0N (\x -> x * r2 + rscalar 5) v
    in rmap0N (\x0 -> tlet x0 $ \x -> x * rsum0
                           (rbuild1 3 (\ix -> bar (x, rindex v' [ix]))
                            + (tlet (nestedMap x) $ \x3 -> fooBuild1 x3)
                            / (tlet x $ \x4 -> fooMap1 x4))
              ) doublyBuild

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 107.25984443006627)
    (rev' @Double @1 nestedBuildMap (rscalar 1.1))

nestedSumBuild :: (ADReady target, GoodScalar r, Differentiable r)
               => target (TKR 1 r) -> target (TKR 1 r)
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
     nbmt `rindex` [minH ix 4])))

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (ringestData [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @Double @1 nestedSumBuild (ringestData [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall target r. (ADReady target, GoodScalar r)
                 => target (TKR 1 r) -> target (TKR 1 r)
nestedBuildIndex v =
  rbuild1 2 $ \ix2 -> rindex (rbuild1 3 $ \ix3 -> rindex (rbuild1 4 $ \ix4 -> rindex v (ix4 :.: ZIR)) [ix3]) (ix2 :.: ZIR)

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [5] [1,1,0,0,0])
    (rev' @Double @1 nestedBuildIndex (ringestData [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( ADReady target, GoodScalar r, KnownNat n, Differentiable r )
  => target (TKR n r) -> target (TKR n r)
barRelu x = relu $ bar (x, relu x)

testBarReluDt :: Assertion
testBarReluDt =
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [191.20462646925841])
    (vjp @_ @(TKR 0 Double)
           barRelu (rscalar 1.1) (rscalar 42.2))

testBarRelu :: Assertion
testBarRelu =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [4.5309153191767395])
    (rev' @Double @0 barRelu (ringestData [] [1.1]))

testBarRelu3 :: Assertion
testBarRelu3 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barRelu (ringestData [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluMax0
  :: ( ADReady target, GoodScalar r, KnownNat n, RealFloatH (target (TKR n r)) )
  => target (TKR n r) -> target (TKR n r)
barReluMax0 x = reluMax $ bar (x, x)

barReluMax
  :: ( ADReady target, GoodScalar r, KnownNat n, RealFloatH (target (TKR n r)) )
  => target (TKR n r) -> target (TKR n r)
barReluMax x = reluMax $ bar (x, reluMax x)

testBarReluMaxDt :: Assertion
testBarReluMaxDt =
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [191.20462646925841])
    (vjp @_ @(TKR 0 Double)
           barReluMax (rfromList0N [] [rscalar 1.1]) (rscalar 42.2))

testBarReluMax :: Assertion
testBarReluMax =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [4.5309153191767395])
    (rev' @Double @0 barReluMax (ringestData [] [1.1]))

testBarReluMax30 :: Assertion
testBarReluMax30 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1] [4.5309153191767395])
    (rev' @Double @1 barReluMax0 (ringestData [1] [1.1]))

testBarReluMax31 :: Assertion
testBarReluMax31 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev' @Double @3 barReluMax (ringestData [2, 1, 2] [1.1, 2, 3, 4.2]))

testBarReluMax3CFwd :: Assertion
testBarReluMax3CFwd =
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (cjvp @_ @(TKR 3 Double)
          barReluMax
                     (rconcrete $ Nested.rfromListPrimLinear (fromList [2, 1, 2]) [1.1, 2, 3, 4.2])
                     (ringestData [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

reluMaxS :: forall target sh r. (ADReady target, GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS sh r)
reluMaxS = smap0N (maxH (srepl 0))

barReluMaxS
  :: ( ADReady target, GoodScalar r, KnownShS sh
     , RealFloatH (target (TKS sh r)) )
  => target (TKS sh r) -> target (TKS sh r)
barReluMaxS x = reluMaxS $ barF (x, reluMaxS x)

-- Previously the shape of FromListR[DeltaZero] couldn't be determined
-- in buildDerivative, so this was needed. See below that it now works fine.
testBarReluMax3FwdS :: Assertion
testBarReluMax3FwdS =
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (jvp @_ @(TKS '[2, 1, 2] Double)
         barReluMaxS
         (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdFrom :: Assertion
testBarReluMax3FwdFrom =
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (jvp @_ @(TKS '[2, 1, 2] Double)
         (sfromR . barReluMax . rfromS)
         (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [1.1, 2, 3, 4.2])
         (sconcrete $ Nested.sfromListPrimLinear @_ @'[2, 1, 2] knownShS [0.1, 0.2, 0.3, 0.42]))

testBarReluMax3FwdR :: Assertion
testBarReluMax3FwdR =
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2, 1, 2] [0.45309153191767404,0.9060427799711201,-2.8186426018387007,40.02498898648793])
    (jvp @_ @(TKR 3 Double)
         barReluMax
         (ringestData [2, 1, 2] [1.1, 2, 3, 4.2])
         (ringestData [2, 1, 2] [0.1, 0.2, 0.3, 0.42]))

f1 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 0 r)
f1 = \arg -> rsum0 (rbuild1 10 (\i -> arg * rfromIndex0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    (rscalar 45.0)
    (grad (kfromR @_ @Double . f1) (rscalar 1.1))

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 45.0)
    (rev' @Double @0 f1 (rscalar 1.1))

f2 :: forall target r. (ADReady target, GoodScalar r)
   => target (TKR 0 r) -> target (TKR 0 r)
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
    (grad (kfromR @_ @Double . f2) (rscalar 1.1))

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 470)
    (rev' @Double @0 f2 (rscalar 1.1))

testF2CFwd :: Assertion
testF2CFwd =
  assertEqualUpToEpsilon 1e-10
    (rscalar 47)
    (cjvp @_ @(TKR 0 Double)
          f2 (rscalar 1.1) (rscalar 0.1))

testF2Fwd :: Assertion
testF2Fwd =
  assertEqualUpToEpsilon 1e-10
    (rscalar 47)
    (jvp @_ @(TKR 0 Double)
         f2 (rscalar 1.1) (rscalar 0.1))

braidedBuilds :: forall target r.
                 (ADReady target, GoodScalar r, Differentiable r)
              => target (TKR 0 r) -> target (TKR 2 r)
braidedBuilds r =
  rbuild1 3 (\ix1 ->
    rbuild1 4 (\ix2 -> rindex (rfromList0N [4]
      [rfromIndex0 ix2, rscalar 7, r, rscalar (-0.2)]) (ix1 :.: ZIR)))

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4.0)
    (rev' @Double @2 braidedBuilds (rscalar 3.4))

recycled :: (ADReady target, GoodScalar r, Differentiable r)
         => target (TKR 0 r) -> target (TKR 5 r)
recycled r =
  tlet (nestedSumBuild (rreplicate0N [7] r)) $ \nsb ->
    rbuild1 2 $ \_ -> rbuild1 4 $ \_ -> rbuild1 2 $ \_ -> rbuild1 3 $ const nsb

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilonShort 1e-6
    (rscalar 348356.9278600814)
    (rev' @Double @5 recycled (rscalar 0.0000001))

concatBuild :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 2 r)
concatBuild r =
  rbuild1 7 (\i ->
    rappend (rappend (rbuild1 5 (const r))
                     (rreplicate 1 (rfromIndex0 i)))
            (rbuild1 13 (const r)))

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 126.0)
    (rev' @Double @2 concatBuild (rscalar 3.4))

concatBuild2 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
concatBuild2 r =
  tlet (rfromList [r, rscalar 1, rscalar 2, rscalar 3, rscalar 4]) $ \a ->
    rbuild1 10 (\i -> ifH (i <. 5) (rindex a [i]) (rindex a [i - 5]))

testConcatBuild2 :: Assertion
testConcatBuild2 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0)
    (rev' @Double @1 concatBuild2 (rscalar 3.4))

concatBuild3 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
concatBuild3 r =
  tlet (rfromList [r, rscalar 1, rscalar 2, rscalar 3, rscalar 4]) $ \a ->
    rbuild1 10 (\i -> ifH (i <. 5) (rindex a [i]) (rindex a [i - 5 + (1 `quotH` maxH 1 (i - 5))]))

testConcatBuild3 :: Assertion
testConcatBuild3 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' @Double @1 concatBuild3 (rscalar 3.4))

concatBuild4 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
concatBuild4 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotH` (4 + i)) :.: ZIR)) $ \a ->
    rappend a a

testConcatBuild4 :: Assertion
testConcatBuild4 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 10)
    (rev' @Double @1 concatBuild4 (rscalar 3.4))

concatBuild5 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
concatBuild5 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotH` (5 + i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotH` (5 + i)) :.: ZIR)))

testConcatBuild5 :: Assertion
testConcatBuild5 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 10)
    (rev' @Double @1 concatBuild5 (rscalar 3.4))

concatBuild6 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 2 r)
concatBuild6 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotH` (4 + i)) :.: ZIR)) $ \a ->
    (rappend (rgather1 5 (rreplicate 1 r)
                         (\i -> (1 `quotH` (100 * maxH 1 (i - j))) :.: ZIR)) a))
                     (rreplicate 1 (rfromIndex0 j)))
            (rbuild1 13 (const r)))

testConcatBuild6 :: Assertion
testConcatBuild6 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 161)
    (rev' @Double @2 concatBuild6 (rscalar 3.4))

concatBuild7 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
concatBuild7 r =
  rbuild1 10 $ \j ->
    (rappend (rreplicate 5 r) (rgather1 5 (rreplicate 1 r)
                                 (\i -> (1 `quotH` maxH 1 (j - i)) :.: ZIR)))
     ! (j :.: ZIR)

testConcatBuild7 :: Assertion
testConcatBuild7 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 10)
    (rev' @Double @1 concatBuild7 (rscalar 3.4))

-- These tests show that term rewriting changes the value
-- of out-of-bounds indexing, e.g., of gather(replicate)
-- that reduces to a non-gather. Vectorization is not needed for that.
_concatBuild8 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 1 r)
_concatBuild8 r =
  tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotH` (5 - i)) :.: ZIR)) $ \a ->
    (rappend a (rgather1 5 (rreplicate 1 r)
                           (\i -> (1 `quotH` (5 - i)) :.: ZIR)))

_testConcatBuild8 :: Assertion
_testConcatBuild8 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 10)
    (rev' @Double @1 _concatBuild8 (rscalar 3.4))

_concatBuild9 :: (ADReady target, GoodScalar r) => target (TKR 0 r) -> target (TKR 2 r)
_concatBuild9 r =
  rbuild1 7 (\j ->
    rappend (rappend
             (tlet (rgather1 5 (rreplicate 1 r)
                   (\i -> (1 `quotH` (4 - i)) :.: ZIR)) $ \a ->
    (rappend (rgather1 5 (rreplicate 1 r)
                         (\i -> (1 `quotH` (100 * maxH 0 (i - j))) :.: ZIR)) a))
                     (rreplicate 1 (rfromIndex0 j)))
            (rbuild1 13 (const r)))

_testConcatBuild9 :: Assertion
_testConcatBuild9 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 161)
    (rev' @Double @2 _concatBuild9 (rscalar 3.4))

concatBuild10 :: (ADReady target, GoodScalar r)
              => target (TKR 0 r) -> target (TKR 2 r)
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
    (rscalar 91)
    (rev' @Double @2 concatBuild10 (rscalar 3.4))

concatBuild11 :: (ADReady target, GoodScalar r)
              => target (TKR 0 r) -> target (TKR 1 r)
concatBuild11 r =
  rgather1 5 (rreplicate 1 r) (\_i -> (-1) :.: ZIR)

testConcatBuild11 :: Assertion
testConcatBuild11 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0)
    (rev' @Double @1 concatBuild11 (rscalar 3.4))

concatBuild12 :: (ADReady target, GoodScalar r)
              => target (TKR 0 r) -> target (TKR 0 r)
concatBuild12 r =
  rindex (rreplicate 1 r) ((-1) :.: ZIR)

testConcatBuild12 :: Assertion
testConcatBuild12 =
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0)
    (rev' @Double @0 concatBuild12 (rscalar 3.4))

-- TODO: copy-paste a variant of emptyArgs with r not GoodScalar
-- or maybe generalize emptyArgs and then in half of the tests do TKScalar
emptyArgs :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
          => target (TKR 1 r) -> target (TKR 1 r)
emptyArgs t =
  emptyTensor
  - rfromList0N (rshape @target @_ @(TKScalar r) emptyTensor) []
  + rconcrete Nested.remptyArray
  - rsum (rfromList0N (0 :$: rshape @target @_ @(TKScalar r) emptyTensor) [])
  * rsum (rconcrete $ Nested.rreshape (0 :$: 0 :$: ZSR) Nested.remptyArray)
  * rconcrete (Nested.rsumOuter1 $ Nested.rfromListOuter
               $ NonEmpty.fromList [Nested.remptyArray])
  * rsum (rconcrete $ Nested.rfromListOuter
          $ NonEmpty.fromList [Nested.remptyArray])
  * rsum (rfromList [rconcrete Nested.remptyArray])
  * rsum (rfromList [emptyTensor])
  * rsum (rfromList [rsum (rfromList0N
                             (0 :$: rshape @target @_ @(TKScalar r)
                                      emptyTensor) [])])
  - rindex (rfromList0N (0 :$: 0 :$: ZSR) []) (42 :.: ZIR)
  - rindex (rfromList0N (0 :$: rshape @target @_ @(TKScalar r)
                                     emptyTensor) []) (42 :.: ZIR)
  - rreshape @1 [0] emptyTensor
  - rsum (rreshape @1 [0, 0] emptyTensor)
-- TODO:
--  - rgather1 0 emptyTensor (:.: ZIR)
--  - rsum (rgather1 0 emptyTensor (const ZIR))
--  - rsum (rgather @target @(TKScalar r) @2 (0 :$: 0 :$: ZSR) emptyTensor (const (0 :.: ZIR)))
--  - rsum (rgather @target @(TKScalar r) @2 @0 @1 [0, 0] emptyTensor (const [0]))
--  * rflatten (rtr (rgather1 0 t (const ZIR)))
  + rbuild1 0 (\i -> t ! (i :.: ZIR))
  + rbuild1 0 (\i -> t ! [fromIntegral (rlength t) `quotH` i] / rfromIndex0 i)
  + rbuild @1 (0 :$: ZSR) (const $ rscalar 73)
  - rsum (rbuild @0 (0 :$: 0 :$: ZSR)
                 (const (rreplicate 1 emptyTensor)))
  + rfromS
      (sfromList0N []
       + sconcrete (Nested.semptyArray ZSS)
       - ssum @0 (sfromList0N [])
       * ssum @0 (sconcrete $ Nested.semptyArray (SNat @0 :$$ ZSS))
       * sconcrete (Nested.ssumOuter1 $ Nested.sfromListOuter (SNat @1)
                    $ NonEmpty.fromList [Nested.semptyArray ZSS])
       * ssum @1 (sconcrete $ Nested.sfromListOuter SNat
                        $ NonEmpty.fromList [Nested.semptyArray ZSS])
       * ssum @1 (sfromList [sconcrete $ Nested.semptyArray ZSS])
       * ssum @1 (sfromList [sfromR @_ @'[0] emptyTensor])
       * ssum @1 (sfromList [ssum @0 (sfromList0N [])])
       - sindex @'[0] (sfromList0N []) (42 :.$ ZIS)
       - sindex @'[0] (sfromList0N []) (42 :.$ ZIS)
       - sreshape @_ @'[0] (sfromR @_ @'[0] emptyTensor)
       - ssum (sreshape @_ @'[0, 0] (sfromR @_ @'[0] emptyTensor))
       * sbuild1 @0 (\i -> sfromR @_ @'[0] (rslice 0 0 t) !$ (i :.$ ZIS))
       + sbuild1 @0 (\i -> sfromR @_ @'[0] (rslice 0 0 t)
                              !$ (fromIntegral (rlength t) `quotH` i :.$ ZIS)
                              / sfromIndex0 i)
       + sbuild @1 (const $ sscalar 73)
       - ssum (sbuild @0
                      (const (sreplicate @1 (sfromR emptyTensor)))))
  + rfromX
      (xfromList0N (SKnown (SNat @0) :$% ZSX) []
       + xconcrete (Nested.memptyArray ZSX)
       - xsum @0 (xfromList0N
                          (SKnown (SNat @0) :$% SKnown (SNat @0) :$% ZSX) [])
       * xsum @0 (xconcrete
                        $ Nested.memptyArray (SKnown (SNat @0) :$% ZSX))
       * xconcrete (Nested.msumOuter1 $ Nested.mfromListOuter
                    $ NonEmpty.fromList [Nested.memptyArray ZSX])
       * xsum @1 (xconcrete
                        $ Nested.mcast
                            (SKnown (SNat @1) :!% SKnown (SNat @0) :!% ZKX)
                        $ Nested.mfromListOuter
                        $ NonEmpty.fromList [Nested.memptyArray ZSX])
       * xsum @1 (xfromList [xconcrete $ Nested.memptyArray ZSX])
       * xsum @1 (xfromList [xfromR @_ @'[Just 0] emptyTensor])
       * xsum @1 (xfromList [xsum @0
                                     (xfromList0N
                                        (SKnown (SNat @0)
                                         :$% xshape @target @_ @(TKScalar r)
                                               (xfromR @_ @'[Just 0]
                                                  emptyTensor)) [])])
       - xindex @_ @'[Just 0] (xfromList0N
                                    (SKnown (SNat @0)
                                     :$% SKnown (SNat @0)
                                     :$% ZSX) []) (42 :.% ZIX)
       - xindex @_ @'[Just 0] (xfromList0N
                                    (SKnown (SNat @0)
                                     :$% xshape @target @_ @(TKScalar r)
                                             (xfromR @_ @'[Just 0]
                                                emptyTensor)) []) (42 :.% ZIX)
       - xreshape (SKnown (SNat @0) :$% ZSX) (xfromR @_ @'[Just 0] emptyTensor)
       - xsum (xreshape (SKnown (SNat @0) :$% SKnown (SNat @0) :$% ZSX) (xfromR @_ @'[Just 0] emptyTensor))
       * xbuild1 @0 (\i -> xfromR @_ @'[Nothing] (rslice 0 0 t)
                            `xindex` (i :.% ZIX))
       + xbuild1 @0 (\i -> xfromR @_ @'[Nothing] (rslice 0 0 t)
                              `xindex`
                              (fromIntegral (rlength t) `quotH` i :.% ZIX)
                              / xfromIndex0 i)
       + xbuild @1 (SKnown (SNat @0) :$% ZSX)
                (const $ xscalar 73)
       - xsum (xbuild @0 (SKnown (SNat @0)
                                                :$% SKnown (SNat @0)
                                                :$% ZSX)
                      (const (xreplicate (xfromR emptyTensor)))))
  -- - rsum (rbuild @2 (0 :$: 0 :$: ZSR) (const 73))
  -- - rsum (rbuild @1 (0 :$: 0 :$: ZSR) (const emptyTensor))
       -- these two fail and rightly so; TODO: make them fail earlier
 where
  emptyTensor :: target (TKR 1 r)
  emptyTensor = rconcrete $ Nested.rfromListPrimLinear (fromList [0]) []

testEmptyArgs0 :: Assertion
testEmptyArgs0 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [0] [])
    (rev' @Double @1 emptyArgs (ringestData [0] []))

testEmptyArgs1 :: Assertion
testEmptyArgs1 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1] [0])
    (rev' @Float @1 emptyArgs (ringestData [1] [0.24]))

testEmptyArgs4 :: Assertion
testEmptyArgs4 =
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1] [0])
    (rev' @Double @1
          (\t -> rbuild [2, 5, 11, 0] (const $ emptyArgs t))
          (ringestData [1] [0.24]))

filterPositiveFail :: ADReady target
                   => target (TKR 1 Double) -> target (TKR 1 Double)
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
    (ringestData [5] [1.0,1.0,1.0,0.0,0.0])
    (rev' @Double @1
          filterPositiveFail
          (ringestData [5] [0.24, 52, -0.5, 0.33, 0.1]))

-- Catastrophic loss of sharing prevented.
fblowup :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
        => Int -> target (TKR 1 r) -> target (TKR 0 r)
fblowup k inputs =
  let blowup :: Int -> target (TKR 0 r) -> target (TKR 0 r)
      blowup 0 y = y - rfromIndex0 0
      blowup n y =
        let ysum = y + y - rfromIndex0 0
            yscaled = rscalar 0.499999985 * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled
      y0 = (inputs ! [0]) / (inputs ! [1])
  in blowup k y0

fblowupLet :: forall target r. (ADReady target, GoodScalar r, Differentiable r)
           => IntOf target -> Int -> target (TKR 1 r) -> target (TKR 0 r)
fblowupLet i k inputs =
  let blowup :: Int -> target (TKR 0 r) -> target (TKR 0 r)
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
            => Int -> target (TKR 1 r) -> target (TKR 0 r)
fblowupMult k inputs =
  let blowup :: Int -> target (TKR 0 r) -> target (TKR 0 r)
      blowup 0 y = y
      blowup n y =
        let ysum = y + y * y / (y - rscalar 0.000000001)
            yscaled = sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 0
      y0 = (inputs ! [0 `remH` 2]) * (inputs ! [1])
  in blowup k y0

fblowupMultLet :: forall target r.
                  (ADReady target, GoodScalar r, Differentiable r)
               => IntOf target -> Int -> target (TKR 1 r) -> target (TKR 0 r)
fblowupMultLet i k inputs =
  let blowup :: Int -> target (TKR 0 r) -> target (TKR 0 r)
      blowup 0 y = y
      blowup n y1 = tlet y1 $ \y ->
        let ysum0 = y + y * y / (y - rscalar 0.000001)
            yscaled = tlet ysum0 $ \ysum ->
                        sqrt $ rscalar 0.499999985 * rscalar 0.499999985 * ysum * ysum
              -- without the scaling we'd get NaN at once
        in blowup (pred n) yscaled - rfromIndex0 i
      y0 = (inputs ! [i `remH` 2]) * (inputs ! [1])
  in blowup k y0

fblowupPP :: Assertion
fblowupPP = do
  resetVarCounter
  let fblowupT = fblowup @(AstTensor AstMethodLet FullSpan) @Double 1
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fblowupT (FTKR [4] FTKScalar)
  printArtifactSimple artifactRev
    @?= "\\dret v1 -> tlet (sfromR v1 !$ [0]) (\\x2 -> tlet (sfromR v1 !$ [1]) (\\x3 -> tlet (sfromR v1 !$ [0]) (\\x4 -> tlet (sfromR v1 !$ [1]) (\\x5 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x8 -> rfromS (soneHot (recip x3 * x8) [0] + (soneHot ((negate x2 / (x3 * x3)) * x8) [1] + (soneHot (recip x5 * x8) [0] + soneHot ((negate x4 / (x5 * x5)) * x8) [1]))))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\v1 -> tlet (sfromR v1 !$ [0]) (\\x2 -> tlet (sfromR v1 !$ [1]) (\\x3 -> tlet (sfromR v1 !$ [0]) (\\x4 -> tlet (sfromR v1 !$ [1]) (\\x5 -> tlet ((x2 / x3 + x4 / x5) + negate (sfromIntegral (sscalar 0))) (\\x6 -> rfromS (sscalar 0.499999985 * x6 + negate (sfromIntegral (sscalar 0))))))))"

fblowupLetPP :: Assertion
fblowupLetPP = do
  resetVarCounter
  let fblowupLetT = fblowupLet @(AstTensor AstMethodLet FullSpan) @Double 0 1
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fblowupLetT (FTKR [4] FTKScalar)
  printArtifactSimple artifactRev
    @?= "\\dret v1 -> tlet (sfromR v1 !$ [0]) (\\x3 -> tlet (sfromR v1 !$ [1]) (\\x4 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x8 -> tlet (x8 + x8) (\\x9 -> rfromS (soneHot (recip x4 * x9) [0] + soneHot ((negate x3 / (x4 * x4)) * x9) [1])))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\v1 -> tlet (sfromR v1 !$ [0]) (\\x3 -> tlet (sfromR v1 !$ [1]) (\\x4 -> tlet (x3 / x4) (\\x5 -> tlet ((x5 + x5) + negate (sfromIntegral (sscalar 0))) (\\x6 -> rfromS (sscalar 0.499999985 * x6 + negate (sfromIntegral (sscalar 0)))))))"

fblowupLetPP23 :: Assertion
fblowupLetPP23 = do
  resetVarCounter
  let fblowupLetT = fblowupLet @(AstTensor AstMethodLet FullSpan) @Double 2 3
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fblowupLetT (FTKR [4] FTKScalar)
  printArtifactSimple artifactRev
    @?= "\\dret v1 -> tlet (sfromR v1 !$ [0]) (\\x5 -> tlet (sfromR v1 !$ [1]) (\\x6 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x14 -> tlet (sscalar 0.499999985 * x14 + sscalar 0.499999985 * x14) (\\x15 -> tlet (sscalar 0.499999985 * x15 + sscalar 0.499999985 * x15) (\\x16 -> tlet (x16 + x16) (\\x17 -> rfromS (soneHot (recip x6 * x17) [0] + soneHot ((negate x5 / (x6 * x6)) * x17) [1])))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\v1 -> tlet (sfromR v1 !$ [0]) (\\x5 -> tlet (sfromR v1 !$ [1]) (\\x6 -> tlet (x5 / x6) (\\x7 -> tlet ((x7 + x7) + negate (sfromIntegral (sscalar 2))) (\\x8 -> tlet (sscalar 0.499999985 * x8) (\\x9 -> tlet ((x9 + x9) + negate (sfromIntegral (sscalar 2))) (\\x10 -> tlet (sscalar 0.499999985 * x10) (\\x11 -> tlet ((x11 + x11) + negate (sfromIntegral (sscalar 2))) (\\x12 -> rfromS (sscalar 0.499999985 * x12 + negate (sfromIntegral (sscalar 2)))))))))))"
  printArtifactSimple (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> rfromS (tlet (sfromR v1 !$ [1]) (\\x6 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x14 -> tlet (sscalar 0.499999985 * x14 + sscalar 0.499999985 * x14) (\\x15 -> tlet (sscalar 0.499999985 * x15 + sscalar 0.499999985 * x15) (\\x16 -> tlet (x16 + x16) (\\x17 -> soneHot (recip x6 * x17) [0] + soneHot ((negate (sfromR v1 !$ [0]) / (x6 * x6)) * x17) [1]))))))"

fblowupLetPP10 :: Assertion
fblowupLetPP10 = do
  resetVarCounter
  let fblowupLetT = fblowupLet @(AstTensor AstMethodLet FullSpan) @Double 0 6
  let (artifactRev, _) = revArtifactDelta UseIncomingCotangent fblowupLetT (FTKR [2] FTKScalar)
  printArtifactSimple artifactRev
    @?= "\\dret v1 -> tlet (sfromR v1 !$ [0]) (\\x8 -> tlet (sfromR v1 !$ [1]) (\\x9 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x23 -> tlet (sscalar 0.499999985 * x23 + sscalar 0.499999985 * x23) (\\x24 -> tlet (sscalar 0.499999985 * x24 + sscalar 0.499999985 * x24) (\\x25 -> tlet (sscalar 0.499999985 * x25 + sscalar 0.499999985 * x25) (\\x26 -> tlet (sscalar 0.499999985 * x26 + sscalar 0.499999985 * x26) (\\x27 -> tlet (sscalar 0.499999985 * x27 + sscalar 0.499999985 * x27) (\\x28 -> tlet (x28 + x28) (\\x29 -> rfromS (soneHot (recip x9 * x29) [0] + soneHot ((negate x8 / (x9 * x9)) * x29) [1]))))))))))"
  printArtifactPrimalSimple artifactRev
    @?= "\\v1 -> tlet (sfromR v1 !$ [0]) (\\x8 -> tlet (sfromR v1 !$ [1]) (\\x9 -> tlet (x8 / x9) (\\x10 -> tlet ((x10 + x10) + negate (sfromIntegral (sscalar 0))) (\\x11 -> tlet (sscalar 0.499999985 * x11) (\\x12 -> tlet ((x12 + x12) + negate (sfromIntegral (sscalar 0))) (\\x13 -> tlet (sscalar 0.499999985 * x13) (\\x14 -> tlet ((x14 + x14) + negate (sfromIntegral (sscalar 0))) (\\x15 -> tlet (sscalar 0.499999985 * x15) (\\x16 -> tlet ((x16 + x16) + negate (sfromIntegral (sscalar 0))) (\\x17 -> tlet (sscalar 0.499999985 * x17) (\\x18 -> tlet ((x18 + x18) + negate (sfromIntegral (sscalar 0))) (\\x19 -> tlet (sscalar 0.499999985 * x19) (\\x20 -> tlet ((x20 + x20) + negate (sfromIntegral (sscalar 0))) (\\x21 -> rfromS (sscalar 0.499999985 * x21 + negate (sfromIntegral (sscalar 0)))))))))))))))))"
  printArtifactSimple (simplifyArtifact artifactRev)
    @?= "\\dret v1 -> rfromS (tlet (sfromR v1 !$ [1]) (\\x9 -> tlet (sscalar 0.499999985 * sfromR dret) (\\x23 -> tlet (sscalar 0.499999985 * x23 + sscalar 0.499999985 * x23) (\\x24 -> tlet (sscalar 0.499999985 * x24 + sscalar 0.499999985 * x24) (\\x25 -> tlet (sscalar 0.499999985 * x25 + sscalar 0.499999985 * x25) (\\x26 -> tlet (sscalar 0.499999985 * x26 + sscalar 0.499999985 * x26) (\\x27 -> tlet (sscalar 0.499999985 * x27 + sscalar 0.499999985 * x27) (\\x28 -> tlet (x28 + x28) (\\x29 -> soneHot (recip x9 * x29) [0] + soneHot ((negate (sfromR v1 !$ [0]) / (x9 * x9)) * x29) [1])))))))))"

-- TODO: should do 1000000 in a few seconds
blowupTests :: TestTree
blowupTests = testGroup "Catastrophic blowup avoidance tests"
  [ testCase "blowup prim 7" $ do
      assertEqualUpToEpsilon' 1e-5
        (ringestData [2] [0.3333332333333467,-0.22222215555556446])
        (rev' @Double @0 (fblowup 7) (ringestData [2] [2, 3]))
  , testCase "blowupLet prim 2000" $ do
      assertEqualUpToEpsilon' 1e-10
        (ringestData [2] [0.3333133339329949,-0.22220888928866325])
        (rev' @Double @0 (fblowupLet 1 2000) (ringestData [2] [2, 3]))
  , testCase "blowupLet 7000" $ do
      assertEqualUpToEpsilon 1e-10
        (ringestData [2] [0.3332633406816766,-0.22217556045445108])
        (grad (kfromR @_ @Double . rsum0 . fblowupLet 0 7000) (ringestData [2] [2, 3]))
  , testCase "blowupLet tbuild0" $ do
      assertEqualUpToEpsilon 1e-10
        (ringestData [2] [333.2633406816765,-222.175560454451])
        (grad (kfromR @_ @Double . rsum0 . (\intputs -> rbuild1 1000 (\_ -> fblowupLet 0 7000 intputs)))
              (ringestData [2] [2, 3]))
  , testCase "blowupLet tbuild2" $ do
      assertEqualUpToEpsilon 1e-10
        (ringestData [2] [333.2633406816765,-222.175560454451])
        (grad (kfromR @_ @Double . rsum0 . (\intputs -> rbuild1 1000 (\_ -> fblowupLet 2 7000 intputs)))
              (ringestData [2] [2, 3]))
  , testCase "blowupLet tbuildi" $ do
      assertEqualUpToEpsilon 1e-10
        (ringestData [2] [333.2983351701977,-222.19889011346513])
        (grad (kfromR @_ @Double . rsum0 . (\intputs -> rbuild1 1000 (\i -> fblowupLet i 3500 intputs)))
              (ringestData [2] [2, 3]))
  , testCase "blowupLet tbuildc" $ do
      assertEqualUpToEpsilon 1e-7
        (ringestData [2] [333.326333406717,-222.21755560448116])
        (cgrad (kfromR @_ @Double . rsum0 . (\intputs -> rbuild1 1000 (\i -> fblowupLet i 700 intputs)))
              (ringestData [2] [2, 3]))
  , testCase "blowupLet prim tbuild" $ do
      assertEqualUpToEpsilonShort 1e-7
        (ringestData [2] [33.33263334067178,-22.221755560447928])
        (rev' @Double @1
              (\intputs -> rbuild1 100 (\i -> fblowupLet i 700 intputs))
              (ringestData [2] [2, 3]))
  , testCase "blowupMult 3" $ do
      assertEqualUpToEpsilon' 1e-5
        (ringestData [2] [2.999999730000007,1.9999998200000046])
        (rev' @Double @0 (fblowupMult 3) (ringestData [2] [2, 3]))
  , testCase "blowupMultLet 5" $ do
      assertEqualUpToEpsilon' 1e-10
        (ringestData [2] [2.9999995500000267,1.9999997000000178])
        (rev' @Double @0 (fblowupMultLet 0 5)
                                   (ringestData [2] [2, 3]))
  , testCase "blowupMultLet 50" $ do
      assertEqualUpToEpsilon' 1e-10
        (ringestData [2] [2.999995500001215,1.99999700000081])
        (rev' @Double @0 (fblowupMultLet 0 50)
                                   (ringestData [2] [2, 3]))
  , testCase "blowupMultLet tbuild1" $ do
      assertEqualUpToEpsilonShort 1e-10
        (ringestData [2] [14.9999773958889,39.9999398380561])
        (rev' @Double @1
              (\intputs -> rbuild1 100 (\i -> fblowupMultLet i 50 intputs))
              (ringestData [2] [0.2, 0.3]))
  ]

concatBuild33 :: (ADReady target, GoodScalar r)
             => target (TKR 1 r) -> target (TKR 2 r)
concatBuild33 _r =
  rbuild1 5 (\i ->
    rbuild1 2 (\j -> rfromIndex0 (maxH j (i `quotH` (j + 1)))))

testConcatBuild3PP :: Assertion
testConcatBuild3PP = do
  resetVarCounter
  let t = concatBuild33 @(AstTensor AstMethodLet FullSpan) @Float
      (var3, ast3) = funToAst (FTKR [3] FTKScalar) Nothing t
  "\\" ++ printAstVarName var3
       ++ " -> " ++ printAstSimple ast3
    @?= "\\v1 -> tfromPrimal (STKR (SNat @2) STKScalar) (rfromS (sgather [] (sfromIntegral (tfromVector (SNat @2) (STKS [5,2] STKScalar) (fromList [sreplicate @5 (siota (SNat @2)), quotH (str (sreplicate @2 (siota (SNat @5)))) (sreplicate @5 (sreplicate @2 (sscalar 1) + siota (SNat @2)))]))) (\\[i5, i4] -> [ifH (0 <=. i4 + quotH (negate i5) (1 + i4)) 0 1, i5, i4])))"

testConcatBuild3PP2 :: Assertion
testConcatBuild3PP2 = do
  resetVarCounter
  let t = concatBuild33 @(AstTensor AstMethodLet FullSpan) @Double
  let (artifactRev, _) =
        revArtifactDelta UseIncomingCotangent t (FTKR [3] FTKScalar)
  printArtifactSimple artifactRev
    @?= "\\dret v1 -> rfromS (sconcrete (sreplicate [3] 0.0))"
  printArtifactPrimalSimple artifactRev
    @?= "\\v1 -> rfromS (sgather [] (sfromIntegral (tfromVector (SNat @2) (STKS [5,2] STKScalar) (fromList [sreplicate @5 (siota (SNat @2)), quotH (str (sreplicate @2 (siota (SNat @5)))) (sreplicate @5 (sreplicate @2 (sscalar 1) + siota (SNat @2)))]))) (\\[i6, i7] -> [ifH (0 <=. i7 + quotH (negate i6) (1 + i7)) 0 1, i6, i7]))"
  printArtifactPrimalSimple (simplifyArtifact artifactRev)
    @?= "\\v1 -> rfromS (sgather [] (sconcrete (sfromListLinear [2,5,2] [0.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0,0.0,1.0,0.0,0.0,1.0,0.0,2.0,1.0,3.0,1.0,4.0,2.0])) (\\[i6, i7] -> [ifH (0 <=. i7 + quotH (negate i6) (1 + i7)) 0 1, i6, i7]))"
