{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import Data.IntMap.Strict qualified as IM
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested (IShR, IxR (..), KnownShS (..), ShR (..), ShS (..))
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Core.OpsAst
import HordeAd.Core.OpsConcrete ()

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "4SRrev" testFooRrev
  , testCase "4SRrev2" testFooRrev2
  , testCase "4SRrevPP1" testFooRrevPP1
  , testCase "4SRrevPP2" testFooRrevPP2
  , testCase "4SRrev3" testFooRrev3
  , testCase "4S0Rrev" testSin0Rrev
  , testCase "4S0RrevPP1" testSin0RrevPP1
  , testCase "4S0RrevPP2" testSin0RrevPP2
  , testCase "4S0Rrev3" testSin0Rrev3
  , testCase "4S0Rrev4" testSin0Rrev4
  , testCase "4S0RrevPP4" testSin0RrevPP4
  , testCase "4S0Rrev5" testSin0Rrev5
  , testCase "4S0RrevPP5" testSin0RrevPP5
  , testCase "4S0Rrev3'" testSin0Rrev3'
  , testCase "4S0Rrev4'" testSin0Rrev4'
  , testCase "4S0Rrev5'" testSin0Rrev5'
  , testCase "4S0Rfwd" testSin0Rfwd
  , testCase "4S0RfwdPP0" testSin0RfwdPP0
  , testCase "4S0RfwdPP1" testSin0RfwdPP1
  , testCase "4S0RfwdPP1FullUnsimp" testSin0RfwdPP1FullUnsimp
  , testCase "4S0RfwdPP1Full" testSin0RfwdPP1Full
  , testCase "4S0Rfwd3" testSin0Rfwd3
  , testCase "4S0Rfwd4" testSin0Rfwd4
  , testCase "4S0RfwdPP4P" testSin0RfwdPP4P
  , testCase "4S0RfwdPP4Dual" testSin0RfwdPP4Dual
  , testCase "4S0Rfwd5" testSin0Rfwd5
  , testCase "4S0RfwdPP5" testSin0RfwdPP5
  , testCase "4S0Rfwd3'" testSin0Rfwd3'
  , testCase "4S0Rfwd4'" testSin0Rfwd4'
  , testCase "4S0Rfwd5'" testSin0Rfwd5'
  , testCase "4S0Rrev5S" testSin0Rrev5S
  , testCase "4S0RrevPP5S" testSin0RrevPP5S
  , testCase "4S0Fold0" testSin0Fold0
  , testCase "4S0Fold0ForComparison" testSin0Fold0ForComparison
  , testCase "4S0Fold1" testSin0Fold1
  , testCase "4S0FoldB1" testSin0FoldB1
  , testCase "4S0FoldB1PP" testSin0FoldB1PP
  , testCase "4S0FoldB2" testSin0FoldB2
  , testCase "4S0FoldB3" testSin0FoldB3
  , testCase "4S0FoldB4" testSin0FoldB4
  , testCase "4S0Fold2" testSin0Fold2
  , testCase "4S0FoldForComparison" testSin0FoldForComparison
  , testCase "4S0Fold3" testSin0Fold3
  , testCase "4S0Fold4" testSin0Fold4
  , testCase "4S0Fold5" testSin0Fold5
  , testCase "4S0Fold6" testSin0Fold6
  , testCase "4S0Fold7" testSin0Fold7
  , testCase "4S0Fold8" testSin0Fold8
  , testCase "4S0Fold0S" testSin0Fold0S
  , testCase "4S0Fold1S" testSin0Fold1S
  , testCase "4S0Fold2S" testSin0Fold2S
  , testCase "4S0FoldForComparisonS" testSin0FoldForComparisonS
  , testCase "4S0Fold3S" testSin0Fold3S
  , testCase "4S0Fold4S" testSin0Fold4S
  , testCase "4S0Fold5S" testSin0Fold5S
  , testCase "4S0Fold6S" testSin0Fold6S
  , testCase "4S0Fold7S" testSin0Fold7S
  , testCase "4S0Fold8S" testSin0Fold8S
  , testCase "4S0Fold8rev" testSin0Fold8rev
  , testCase "4S0Fold8rev2" testSin0Fold8rev2
  , testCase "4S0Fold8Srev" testSin0Fold8Srev
  , testCase "4S0Fold8Srev2" testSin0Fold8Srev2
  , testCase "4S0Fold182Srev" testSin0Fold182Srev
  , testCase "4S0Fold182SrevPP" testSin0Fold182SrevPP
  , testCase "4S0Fold18Srev" testSin0Fold18Srev
  , testCase "4S0Fold8fwd" testSin0Fold8fwd
  , testCase "4S0Fold8fwd2" testSin0Fold8fwd2
  , testCase "4S0Fold8Sfwd" testSin0Fold8Sfwd
  , testCase "4S0Fold8Sfwd2" testSin0Fold8Sfwd2
  , testCase "4S0Fold5Sfwd" testSin0Fold5Sfwd
  , testCase "4S0Fold5Sfwds" testSin0Fold5Sfwds
  , testCase "4S0Scan0" testSin0Scan0
  , testCase "4S0Scan1" testSin0Scan1
  , testCase "4S0Scan1ForComparison" testSin0Scan1ForComparison
  , testCase "4S0Scan2" testSin0Scan2
  , testCase "4S0Scan3" testSin0Scan3
  , testCase "4S0Scan4" testSin0Scan4
  , testCase "4S0Scan5" testSin0Scan5
  , testCase "4S0Scan6" testSin0Scan6
  , testCase "4S0Scan7" testSin0Scan7
  , testCase "4S0Scan8" testSin0Scan8
  , testCase "4S0Scan8rev" testSin0Scan8rev
  , testCase "4S0Scan8rev2" testSin0Scan8rev2
  , testCase "4S0Scan8Srev2" testSin0Scan8Srev2
  , testCase "4S0Scan1RevPP1" testSin0Scan1RevPP1
  , testCase "4S0Scan1RevPPForComparison" testSin0Scan1RevPPForComparison
  , testCase "4S0ScanFwdPP" testSin0ScanFwdPP
  , testCase "4S0ScanFwdPPFull" testSin0ScanFwdPPFull
  , testCase "4S0Scan1Rev2PP1" testSin0Scan1Rev2PP1
  , testCase "4S0Scan1Rev2PPA" testSin0Scan1Rev2PPA
  , testCase "4S0Scan1Rev2PPForComparison" testSin0Scan1Rev2PPForComparison
  , testCase "4S0Scan1Rev2" testSin0Scan1Rev2
  , testCase "4S0Scan1Rev2ForComparison" testSin0Scan1Rev2ForComparison
  , testCase "4S0Scan1Rev3PP0" testSin0Scan1Rev3PP0
  , testCase "4S0Scan1Rev3PPForComparison" testSin0Scan1Rev3PPForComparison
  , testCase "4S0ScanFwd3PP" testSin0ScanFwd3PP
  , testCase "4S0Scan1Rev3" testSin0Scan1Rev3
  , testCase "4S0Scan1Rev3ForComparison" testSin0Scan1Rev3ForComparison
  , testCase "4S0Scan0fwd" testSin0Scan0fwd
  , testCase "4S0Scan1fwd" testSin0Scan1fwd
  , testCase "4S0Scan1FwdForComparison" testSin0Scan1FwdForComparison
  , testCase "4S0Scan8fwd" testSin0Scan8fwd
  , testCase "4S0Scan8fwd2" testSin0Scan8fwd2
  , testCase "4SUnitriangular0PP" testUnitriangular0PP
  , testCase "4SUnitriangular1PP" testUnitriangular1PP
  , testCase "4SUnitriangular2PP" testUnitriangular2PP
  , testCase "4S0rmapAccumRD0SC" testSin0rmapAccumRD0SC
  , testCase "4S0rmapAccumRD0S" testSin0rmapAccumRD0S
  , testCase "4S0rmapAccumRD00SC" testSin0rmapAccumRD00SC
  , testCase "4S0rmapAccumRD00S0" testSin0rmapAccumRD00S0
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD00S" testSin0rmapAccumRD00S
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD00S7" testSin0rmapAccumRD00S7
  , testCase "4S0rmapAccumRD00SCacc0" testSin0rmapAccumRD00SCacc0
  , testCase "4S0rmapAccumRD00SCacc" testSin0rmapAccumRD00SCacc
  , testCase "4S0rmapAccumRD00Sacc0" testSin0rmapAccumRD00Sacc0
  , testCase "4S0rmapAccumRD00Sacc" testSin0rmapAccumRD00Sacc
  , testCase "4S0rmapAccumRD00SCall0" testSin0rmapAccumRD00SCall0
  , testCase "4S0rmapAccumRD00SCall" testSin0rmapAccumRD00SCall
  , testCase "4S0rmapAccumRD00Sall0" testSin0rmapAccumRD00Sall0
  , testCase "4S0rmapAccumRD00Sall" testSin0rmapAccumRD00Sall
  , testCase "4S0rmapAccumRD0RC" testSin0rmapAccumRD0RC
  , testCase "4S0rmapAccumRD0R" testSin0rmapAccumRD0R
  , testCase "4S0rmapAccumRD01SC" testSin0rmapAccumRD01SC
  , testCase "4S0rmapAccumRD01SN" testSin0rmapAccumRD01SN
  , testCase "4S0rmapAccumRD01SN2" testSin0rmapAccumRD01SN2
  , testCase "4S0rmapAccumRD01SN3" testSin0rmapAccumRD01SN3
  , testCase "4S0rmapAccumRD01SN4" testSin0rmapAccumRD01SN4
  , testCase "4S0rmapAccumRD01SN5" testSin0rmapAccumRD01SN5
  , testCase "4S0rmapAccumRD01SN51" testSin0rmapAccumRD01SN51
  , testCase "4S0rmapAccumRD01SN52" testSin0rmapAccumRD01SN52
  , testCase "4S0rmapAccumRD01SN53" testSin0rmapAccumRD01SN53
  , testCase "4S0rmapAccumRD01SN531" testSin0rmapAccumRD01SN531
  , testCase "4S0rmapAccumRD01SN531a" testSin0rmapAccumRD01SN531a
  , testCase "4S0rmapAccumRD01SN531b0" testSin0rmapAccumRD01SN531b0
  , testCase "4S0rmapAccumRD01SN531bS" testSin0rmapAccumRD01SN531bS
  , testCase "4S0rmapAccumRD01SN531bR" testSin0rmapAccumRD01SN531bR
  , testCase "4S0rmapAccumRD01SN531b0PP" testSin0rmapAccumRD01SN531b0PP
  , testCase "4S0rmapAccumRD01SN531bSPP" testSin0rmapAccumRD01SN531bSPP
  , testCase "4S0rmapAccumRD01SN531bSPPFull" testSin0rmapAccumRD01SN531bSPPFull
  , testCase "4S0rmapAccumRD01SN531b0PPj" testSin0rmapAccumRD01SN531b0PPj
  , testCase "4S0rmapAccumRD01SN531bSPPj" testSin0rmapAccumRD01SN531bSPPj
  , testCase "4S0rmapAccumRD01SN531bRPPj" testSin0rmapAccumRD01SN531bRPPj
  , testCase "4S0rmapAccumRD01SN531c" testSin0rmapAccumRD01SN531c
  , testCase "4S0rmapAccumRD01SN531d" testSin0rmapAccumRD01SN531d
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD01SN531Slice" testSin0rmapAccumRD01SN531Slice
  , testCase "4S0rmapAccumRD01SN54" testSin0rmapAccumRD01SN54
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD01SN55" testSin0rmapAccumRD01SN55
  , testCase "4S0rmapAccumRD01SN55acc" testSin0rmapAccumRD01SN55acc
  , testCase "4S0rmapAccumRD01SN56" testSin0rmapAccumRD01SN56
  , testCase "4S0rmapAccumRD01SN57" testSin0rmapAccumRD01SN57
  , testCase "4S0rmapAccumRD01SN58" testSin0rmapAccumRD01SN58
  , testCase "4S0rmapAccumRD01SN59" testSin0rmapAccumRD01SN59
  , testCase "4S0rmapAccumRD01SN6" testSin0rmapAccumRD01SN6
  , testCase "4S0rmapAccumRD01SN7" testSin0rmapAccumRD01SN7
  , testCase "4S0ScanD51" testSin0ScanD51
  , testCase "4S0ScanD8" testSin0ScanD8
  , testCase "4S0ScanD8MapAccum" testSin0ScanD8MapAccum
  , testCase "4S0ScanD8rev" testSin0ScanD8rev
  , testCase "4S0ScanD8rev4" testSin0ScanD8rev4
  , testCase "4S0ScanD1RevPP" testSin0ScanD1RevPP
  , testCase "4S0ScanDFwdPP" testSin0ScanDFwdPP
  , testCase "4S0ScanD1Rev2PP" testSin0ScanD1Rev2PP
  , testCase "4S0ScanDFwd2PP" testSin0ScanDFwd2PP
  , testCase "4S0ScanDFwd3PP" testSin0ScanDFwd3PP
  , testCase "4S0ScanD1fwd" testSin0ScanD1fwd
  , testCase "4S0ScanD8fwd" testSin0ScanD8fwd
  , testCase "4S0ScanD8fwdMapAccum" testSin0ScanD8fwdMapAccum
  , testCase "4S0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4S0FoldNestedS1" testSin0FoldNestedS1
  , testCase "4S0FoldNestedS1PP" testSin0FoldNestedS1PP
  , testCase "4S0FoldNestedR1PP" testSin0FoldNestedR1PP
  , testCase "4S0FoldNestedR1SimpPP" testSin0FoldNestedR1SimpPP
  , testCase "4S0FoldNestedR0LengthPPs" testSin0FoldNestedR0LengthPPs
  , testCase "4S0FoldNestedR1LengthPPs" testSin0FoldNestedR1LengthPPs
  , testCase "4S0FoldNestedR2LengthPPs" testSin0FoldNestedR2LengthPPs
  , testCase "4S0FoldNestedR3LengthPPs" testSin0FoldNestedR3LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR4LengthPPs" testSin0FoldNestedR4LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR5LengthPPs" testSin0FoldNestedR5LengthPPs
  , testCase "4S0FoldNestedR2LengthPPsDummy7" testSin0FoldNestedR2LengthPPsDummy7
  , testCase "4S0FoldNestedR2Dummy7" testSin0FoldNestedR2Dummy7
  , testCase "4S0FoldNestedR2Tan" testSin0FoldNestedR2Tan
  , testCase "4S0MapAccumNestedR3LengthPP" testSin0MapAccumNestedR3LengthPP
  , testCase "4S0MapAccumNestedR4" testSin0MapAccumNestedR4
  , testCase "4S0MapAccumNestedR5" testSin0MapAccumNestedR5
  , testCase "4S0MapAccumNestedR5r" testSin0MapAccumNestedR5r
  , testCase "4S0MapAccumNestedR10r" testSin0MapAccumNestedR10r
  , testCase "4S0MapAccumNestedR10f" testSin0MapAccumNestedR10f
  , testCase "4S0MapAccumNestedR10fN" testSin0MapAccumNestedR10fN
  , testCase "4S0MapAccumNestedR10rf" testSin0MapAccumNestedR10rf
  , testCase "4S0MapAccumNestedR10rr" testSin0MapAccumNestedR10rr
  , testCase "4S0FoldNestedS1FwdFwd0" testSin0FoldNestedS1FwdFwd0
  , testCase "4S0FoldNestedS1FwdFwd" testSin0FoldNestedS1FwdFwd
  , testCase "4S0FoldNestedS1RevRev" testSin0FoldNestedS1RevRev
  , testCase "4S0FoldNestedS2" testSin0FoldNestedS2
  , testCase "4S0FoldNestedS3" testSin0FoldNestedS3
  , testCase "4S0FoldNestedS4" testSin0FoldNestedS4
  , testCase "4S0FoldNestedS5" testSin0FoldNestedS5
  , testCase "4S0FoldNestedS5rev" testSin0FoldNestedS5rev
  , testCase "4S0FoldNestedS5fwd" testSin0FoldNestedS5fwd
  , testCase "4S0FoldNestedSi" testSin0FoldNestedSi
  , testCase "4S0FoldNestedR1" testSin0FoldNestedR1
  , testCase "4S0FoldNestedR1RevFwd" testSin0FoldNestedR1RevFwd
  , testCase "4S0FoldNestedR2" testSin0FoldNestedR2
  , testCase "4S0FoldNestedR2RevFwd" testSin0FoldNestedR2RevFwd
  , testCase "4S0FoldNestedR3" testSin0FoldNestedR3
  , testCase "4S0FoldNestedR4" testSin0FoldNestedR4
  , testCase "4S0FoldNestedR41" testSin0FoldNestedR41
  , testCase "4S0FoldNestedR40" testSin0FoldNestedR40
  , testCase "4S0FoldNestedR400" testSin0FoldNestedR400
  , testCase "4S0FoldNestedRi" testSin0FoldNestedRi
  , testCase "4S0FoldNestedR22" testSin0FoldNestedR22
  , testCase "4S0FoldNestedR21" testSin0FoldNestedR21
  , testCase "4S0FoldNestedR21PP" testSin0FoldNestedR21PP
  , testCase "4S0revhV" testSin0revhV
  , testCase "4S0revhVPP" testSin0revhVPP
  , testCase "4S0revhV2" testSin0revhV2
  , testCase "4S0revhV3" testSin0revhV3
  , testCase "4S0revhV4" testSin0revhV4
  , testCase "4S0revhV5" testSin0revhV5
  , testCase "4S0revhV6" testSin0revhV6
  , testCase "4S0revhV7" testSin0revhV7
  , testCase "4S0revhV8" testSin0revhV8
  ]

foo :: RealFloatF a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

fooRrev :: forall g a. (ADReady g, GoodScalar a, Differentiable a)
        => (a, a, a) -> (g (TKR 0 a), g (TKR 0 a), g (TKR 0 a))
fooRrev (x, y, z) =
  let fHVector :: forall f. ADReady f => f TKUntyped -> f (TKR 0 a)
      fHVector v = foo (rfromD $ dunHVector v V.! 0, rfromD $ dunHVector v V.! 1, rfromD $ dunHVector v V.! 2)
      zero = voidFromShS @a @'[]
      shapes = V.fromList [zero, zero, zero]
      domsOf = rrev @g fHVector (FTKUntyped shapes)
                    (dmkHVector $ V.fromList
                       [ DynamicShaped $ sconcrete @g $ Nested.sscalar x
                       , DynamicShaped $ sconcrete @g $ Nested.sscalar y
                       , DynamicShaped $ sconcrete @g $ Nested.sscalar z ])
  in ( tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 0)
     , tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 1)
     , tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 2) )

testFooRrev :: Assertion
testFooRrev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (fooRrev @RepN @Double (1.1, 2.2, 3.3))

testFooRrev2 :: Assertion
testFooRrev2 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396284, rscalar (-1.9533751), rscalar 0.96548253)
    (fooRrev @RepN @Float (1.1, 2.2, 3.3))

testFooRrevPP1 :: Assertion
testFooRrevPP1 = do
  resetVarCounter
  let (a1, _, _) = fooRrev @(AstTensor AstMethodLet PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstPretty IM.empty a1
    @?= "rfromS (let h44 = let x8 = sin (sscalar 2.2) ; x10 = sscalar 1.1 * x8 ; x11 = recip (sscalar 3.3 * sscalar 3.3 + x10 * x10) ; x17 = sin (sscalar 2.2) ; x20 = sscalar 3.3 * sscalar 1.0 ; x21 = (negate (sscalar 3.3) * x11) * sscalar 1.0 in [x8 * x21 + x17 * x20, cos (sscalar 2.2) * (sscalar 1.1 * x21) + cos (sscalar 2.2) * (sscalar 1.1 * x20), (x10 * x11) * sscalar 1.0 + (sscalar 1.1 * x17) * sscalar 1.0] in sproject h44 0)"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstTensor AstMethodLet PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty (simplifyInlineContract a1)
    @?= "rfromS (tlet (sin (sscalar 2.2)) (\\x52 -> tlet (sscalar 1.1 * x52) (\\x54 -> x52 * ((negate (sscalar 3.3) * recip (sscalar 3.3 * sscalar 3.3 + x54 * x54)) * sscalar 1.0) + sin (sscalar 2.2) * (sscalar 3.3 * sscalar 1.0))))"

testFooRrev3 :: Assertion
testFooRrev3 = do
  let f :: ADVal RepN (TKR 0 Double) -> ADVal RepN (TKR 0 Double)
      f (D a _) =
        let (a1, _, _) = fooRrev @(ADVal RepN) @Double
                                 (Nested.runScalar (unRepN a), 2.2, 3.3)
        in a1
  assertEqualUpToEpsilon 1e-10
    (rscalar 0)
    (crev f (rscalar 1.1))

testSin0Rrev :: Assertion
testSin0Rrev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.4535961214255773)
    (rrev1 @RepN @Double @0 @0 sin (rscalar 1.1))

testSin0RrevPP1 :: Assertion
testSin0RrevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rfromS (cos (sscalar 1.1) * sscalar 1.0)"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstSimple IM.empty a1
    @?= "rfromS (cos (sscalar 1.1) * sscalar 1.0)"

testSin0Rrev3 :: Assertion
testSin0Rrev3 = do
  let f = rrev1 @(ADVal RepN) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (crev f (rscalar 1.1))

testSin0Rrev4 :: Assertion
testSin0Rrev4 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.8988770945225438)
    ((rrev1 sin . rrev1 @RepN @Double @0 @0 sin) (rscalar 1.1))

testSin0RrevPP4 :: Assertion
testSin0RrevPP4 = do
  let a1 = (rrev1 sin . rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (cos (cos (sscalar 1.1) * sscalar 1.0) * sscalar 1.0)"

testSin0Rrev5 :: Assertion
testSin0Rrev5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (rrev1 @RepN @Double @0 @0 (rrev1 sin) (rscalar 1.1))

testSin0RrevPP5 :: Assertion
testSin0RrevPP5 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 (rrev1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (negate (sin (sscalar 1.1)) * (sscalar 1.0 * sscalar 1.0))"

testSin0Rrev3' :: Assertion
testSin0Rrev3' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.8912073600614354) :: RepN (TKR 0 Double))
    (rev' (rrev1 sin) (rscalar 1.1))

testSin0Rrev4' :: Assertion
testSin0Rrev4' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.39052780643689855 :: RepN (TKR 0 Double))
    (rev' (rrev1 sin . rrev1 sin) (rscalar 1.1))

testSin0Rrev5' :: Assertion
testSin0Rrev5' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.4535961214255773) :: RepN (TKR 0 Double))
    (rev' (rrev1 (rrev1 sin)) (rscalar 1.1))

testSin0Rfwd :: Assertion
testSin0Rfwd = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.4535961214255773)
    (rfwd1 @RepN @Double @0 @0 sin (rscalar 1.1))

testSin0RfwdPP0 :: Assertion
testSin0RfwdPP0 = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rfromS (sscalar 1.0 * cos (sscalar 1.1))"

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 * cos (sscalar 1.1))"

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "(\\x1 -> rfromS (sfromR (tproject1 x1) * cos (sfromR (tproject2 x1)))) (tfromS (tpair (sscalar 1.0, sscalar 1.1)))"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "(\\x1 -> rfromS (sfromR (tproject1 x1) * cos (sfromR (tproject2 x1)))) (tfromS (tpair (sscalar 1.0, sscalar 1.1)))"

testSin0Rfwd3 :: Assertion
testSin0Rfwd3 = do
  let f = rfwd1 @(ADVal RepN) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.9803280960675791))
    (cfwd f (rscalar 1.1) (rscalar 1.1))

testSin0Rfwd4 :: Assertion
testSin0Rfwd4 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.8988770945225438)
    ((rfwd1 sin . rfwd1 @RepN @Double @0 @0 sin) (rscalar 1.1))

testSin0RfwdPP4P :: Assertion
testSin0RfwdPP4P = do
  let a1 = (rfwd1 sin . rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 * cos (sscalar 1.0 * cos (sscalar 1.1)))"

testSin0RfwdPP4Dual :: Assertion
testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstTensor AstMethodLet DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "(\\x18 -> rfromS (sfromR (tproject1 x18) * cos (sfromR (tproject2 x18)))) (tfromS (tpair (sdualPart (sscalar 1.0), (\\x14 -> rfromS (sfromR (tproject1 x14) * cos (sfromR (tproject2 x14)))) (tfromS (tpair (sdualPart (sscalar 1.0), rdualPart (rfromS (sscalar 1.1))))))))"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (rfwd1 @RepN @Double @0 @0 (rfwd1 sin) (rscalar 1.1))

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 (rfwd1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 0.0 * cos (sscalar 1.1) + (sscalar 1.0 * negate (sin (sscalar 1.1))) * sscalar 1.0)"

testSin0Rfwd3' :: Assertion
testSin0Rfwd3' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.8912073600614354) :: RepN (TKR 0 Double))
    (rev' (rfwd1 sin) (rscalar 1.1))

testSin0Rfwd4' :: Assertion
testSin0Rfwd4' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.39052780643689855 :: RepN (TKR 0 Double))
    (rev' (rfwd1 sin . rfwd1 sin) (rscalar 1.1))

testSin0Rfwd5' :: Assertion
testSin0Rfwd5' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.4535961214255773) :: RepN (TKR 0 Double))
    (rev' (rfwd1 (rfwd1 sin)) (rscalar 1.1))

testSin0Rrev5S :: Assertion
testSin0Rrev5S = do
  assertEqualUpToEpsilon 1e-10
    (srepl (-0.8912073600614354))
    (srev1 @RepN @Double @'[] @'[] (srev1 sin) (srepl 1.1))

testSin0RrevPP5S :: Assertion
testSin0RrevPP5S = do
  resetVarCounter
  let a1 = srev1 @(AstTensor AstMethodLet PrimalSpan) @Double @'[] @'[] (srev1 sin) (srepl 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "negate (sin (sscalar 1.1)) * sscalar 1.0"

testSin0Fold0 :: Assertion
testSin0Fold0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = rfold (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0Fold0ForComparison :: Assertion
testSin0Fold0ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. f (TKR 0 Double) -> f (TKR 0 Double)
               f = id
           in f) (rscalar 1.1))

testSin0Fold1 :: Assertion
testSin0Fold1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR 0 Double))
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @Double @1 [1] 42)) (rscalar 1.1))

testSin0FoldB1 :: Assertion
testSin0FoldB1 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: RepN (TKR 0 Double))
    (rrev1 (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
                f x0 = rfold (\_x _a -> rscalar 7)
                         (rscalar 5) (rreplicate 1 x0)
            in f) (rscalar 1.1))

testSin0FoldB1PP :: Assertion
testSin0FoldB1PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan)
             (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
                  f x0 = rfold (\_x _a -> rscalar 7)
                           (rscalar 5) (rreplicate 1 x0)
              in f) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rsum (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [Z0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sscalar 5.0) (sreplicate (sscalar 1.1)))), sreplicate (sscalar 1.1))))))"

testSin0FoldB2 :: Assertion
testSin0FoldB2 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: RepN (TKR 0 Double))
    (rev (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
              f x0 = rfold (\_x _a -> rscalar 7)
                       (rscalar 5) (rreplicate 1 x0)
          in f) (rscalar 1.1))

testSin0FoldB3 :: Assertion
testSin0FoldB3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = rfold (\_x _a -> rscalar 7)
                        (rscalar 5) (rreplicate 1 x0)
           in f) (rscalar 1.1))

testSin0FoldB4 :: Assertion
testSin0FoldB4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = rfold (\_x _a -> rscalar 7)
                        x0 (rrepl @Double @1 [1] 42)
           in f) (rscalar 1.1))

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR 0 Double))
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @Double @1 [5] 42)) (rscalar 1.1))

testSin0FoldForComparison :: Assertion
testSin0FoldForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR 0 Double))
    (rev' (sin . sin . sin . sin . sin) (rscalar 1.1))

testSin0Fold3 :: Assertion
testSin0Fold3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\_x a -> sin a)
                        (rscalar 84) (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold4 :: Assertion
testSin0Fold4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar  (-0.7053476446727861) :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\x a -> atan2F (sin x) (sin a))
                        (rscalar 2 * a0) (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold5 :: Assertion
testSin0Fold5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2992412552109085 :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                          (rsum $ sin $ rsum
                                           $ rtr $ rreplicate 7 a))
                        (rscalar 2 * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0)))) (rscalar 1.1))

testSin0Fold6 :: Assertion
testSin0Fold6 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6 :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (rscalar 1.1))

testSin0Fold7 :: Assertion
testSin0Fold7 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 250 :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (rscalar 1.1))

testSin0Fold8 :: Assertion
testSin0Fold8 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR 0 Double))
    (rev' (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold0S :: Assertion
testSin0Fold0S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[] @'[] @0
                            (\x _a -> sin x)
                            x0 (srepl 0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold1S :: Assertion
testSin0Fold1S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR 0 Double))
    (rev' ((let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
                f x0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS '[] Double) -> f2 (TKS '[] Double)
                                   -> f2 (TKS '[] Double)
                                  g x _a = sin x
                              in g)
                        x0 (srepl @'[1] 42)
            in rfromS . f . sfromR)) (rscalar 1.1))

testSin0Fold2S :: Assertion
testSin0Fold2S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = sfold (\x _a -> sin x)
                        x0 (srepl @'[5] @Double 42)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldForComparisonS :: Assertion
testSin0FoldForComparisonS = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f = sin . sin . sin . sin . sin
          in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold3S :: Assertion
testSin0Fold3S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\_x a -> sin a)
                        (srepl 84) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold4S :: Assertion
testSin0Fold4S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar  (-0.7053476446727861) :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a -> atan2F (sin x) (sin a))
                        (srepl 2 * a0) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold5S :: Assertion
testSin0Fold5S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2992412552109085 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS '[] Double) -> f2 (TKS '[2, 5] Double)
                                   -> f2 (TKS '[] Double)
                                 g x a = ssum
                                   $ atan2F (sin $ sreplicate @f2 @5 x)
                                            (ssum $ sin $ ssum
                                             $ str $ sreplicate @f2 @7 a)
                             in g)
                        (srepl 2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold6S :: Assertion
testSin0Fold6S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 1] Double)
               f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 1] @'[] @2
                        (\x a -> str
                                 $ str x + sreplicate @_ @1
                                                      (sreplicate @_ @2 a))
                        (sreplicate @_ @2 (sreplicate @_ @1 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold7S :: Assertion
testSin0Fold7S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 250 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
               f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @2
                        (\x _a -> str $ sreplicate @_ @5 $ ssum (str x))
                        (sreplicate @_ @2 (sreplicate @_ @5 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8S :: Assertion
testSin0Fold8S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
               f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8rev :: Assertion
testSin0Fold8rev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR 0 Double))
    (rrev1 @RepN @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rscalar 2 * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold8rev2 :: Assertion
testSin0Fold8rev2 = do
  let h = rrev1 @(ADVal RepN) @Double @0 @2
        (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rscalar 2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rscalar 98.72666469795736)
    (crev h (rscalar 1.1))

testSin0Fold8Srev :: Assertion
testSin0Fold8Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR 0 Double))
    (rrev1 (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
                f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8Srev2 :: Assertion
testSin0Fold8Srev2 = do
  let h = srev1 @(ADVal RepN)
                (let f :: forall f. ADReady f
                       => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
                     f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (sscalar 2 * a0)))
                        (sreplicate @_ @3 a0)
                 in f)
  assertEqualUpToEpsilon 1e-10
    (RepN $ Nested.sscalar 6.182232283434464e-2)  -- seems quite unstable
    (crev h (srepl 0.0001))

testSin0Fold182Srev :: Assertion
testSin0Fold182Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.4409160296923509) :: RepN (TKR 0 Double))
    (rrev1 (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5] Double)
                f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold182SrevPP :: Assertion
testSin0Fold182SrevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan)
           (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5] Double)
                f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rfromS (let v5 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (tconcrete (FTKS [5] FTKScalar) (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])) (tpair (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [Z0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate (sscalar 1.1)) (sreplicate (sscalar 1.1)))), sreplicate (sscalar 1.1)))) in ssum (tproject1 v5) + ssum (tproject2 v5))"

testSin0Fold18Srev :: Assertion
testSin0Fold18Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.4026418024701366) :: RepN (TKR 0 Double))
    (rrev1 (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
                f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @2
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @2 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8fwd :: Assertion
testSin0Fold8fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2, 5] (replicate 10 (-0.2200311410593445)))
    (rfwd1 @RepN @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold8fwd2 :: Assertion
testSin0Fold8fwd2 = do
  let h = rfwd1 @(ADVal RepN) @Double @0 @2
        (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rscalar 2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rscalar 98.72666469795735)
    (crev h (rscalar 1.1))

testSin0Fold8Sfwd :: Assertion
testSin0Fold8Sfwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2, 5] (replicate 10 (-0.2200311410593445)))
    (rfwd1 @RepN
           (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
                f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8Sfwd2 :: Assertion
testSin0Fold8Sfwd2 = do
  let h = rfwd1 @(ADVal RepN)
                (let f :: forall f. ADReady f
                       => f (TKS '[] Double) -> f (TKS '[2, 5] Double)
                     f a0 = sfold @f @(TKScalar Double) @(TKScalar Double) @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
                 in rfromS . f . sfromR)
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2, 5] (replicate 10 10.859933116775313))
    (cfwd h (rscalar 1.1) (rscalar 1.1))

testSin0Fold5Sfwd :: Assertion
testSin0Fold5Sfwd = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 1.4291653807319993)
    (cfwd (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS '[] Double) -> f2 (TKS '[2, 5] Double)
                                   -> f2 (TKS '[] Double)
                                 g x a = ssum
                                   $ atan2F (sin $ sreplicate @f2 @5 x)
                                            (ssum $ sin $ ssum
                                             $ str $ sreplicate @f2 @7 a)
                             in g)
                        (srepl 2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in rfromS . f . sfromR) (rscalar 1.1) (rscalar 1.1))

testSin0Fold5Sfwds :: Assertion
testSin0Fold5Sfwds = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1.4291653807319993)
    (cfwd (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS '[] Double) -> f2 (TKS '[2, 5] Double)
                                   -> f2 (TKS '[] Double)
                                 g x a = ssum
                                   $ atan2F (sin $ sreplicate @f2 @5 x)
                                            (ssum $ sin $ ssum
                                             $ str $ sreplicate @f2 @7 a)
                             in g)
                        (srepl 2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in f) (srepl 1.1) (srepl 1.1))

testSin0Scan0 :: Assertion
testSin0Scan0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 1 Double)
               f x0 = rscan (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0Scan1 :: Assertion
testSin0Scan1 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR 5 Double))
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rrepl @Double @1 [1] 42))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan1ForComparison :: Assertion
testSin0Scan1ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR 5 Double))
    (rev' (\x0 -> rfromList [x0, sin x0])
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan2 :: Assertion
testSin0Scan2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [2.2207726343670955] :: RepN (TKR 5 Double))
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rrepl @Double @1 [5] 42))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan3 :: Assertion
testSin0Scan3 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.360788364276732] :: RepN (TKR 5 Double))
    (rev' (\a0 -> rscan (\_x a -> sin a)
                        (rreplicate0N [1,1,1,1,1] (rscalar 84))
                        (rreplicate 3 a0)) (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan4 :: Assertion
testSin0Scan4 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [-0.4458209450295252] :: RepN (TKR 5 Double))
    (rev' (\a0 -> rscan (\x a -> atan2F (sin x) (sin a))
                        (rreplicate0N [1,1,1,1,1] (rscalar 2) * a0)
                        (rreplicate 3 a0)) (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan5 :: Assertion
testSin0Scan5 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [4.126141830000979] :: RepN (TKR 4 Double))
    (rev' (\a0 -> rscan (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7 a))
                        (rreplicate0N [1,1,1,1] (rscalar 2) * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0))))
          (ringestData [1,1,1,1] [1.1]))

testSin0Scan6 :: Assertion
testSin0Scan6 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1] [12] :: RepN (TKR 2 Double))
    (rev' (\a0 -> rscan (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0Scan7 :: Assertion
testSin0Scan7 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1] [310] :: RepN (TKR 2 Double))
    (rev' (\a0 -> rscan (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0Scan8 :: Assertion
testSin0Scan8 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR 3 Double))
    (rev' (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                        (rreplicate 3 a0)) (ringestData [1,1,1] [1.1]))

testSin0Scan8rev :: Assertion
testSin0Scan8rev = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [9.53298735735276])
    (rrev1 @RepN @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Scan8rev2 :: Assertion
testSin0Scan8rev2 = do
  let h = rrev1 @(ADVal RepN) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                               $ atan2F (rsum (rtr $ sin x))
                                        (rreplicate 2
                                         $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [285.9579482947575])
    (crev h (rscalar 1.1))

testSin0Scan8Srev2 :: Assertion
testSin0Scan8Srev2 = do
  let h = srev1 @(ADVal RepN) @Double @'[]
        (\a0 -> sscan (\x a -> str $ sreplicate @_ @5
                               $ atan2F (ssum (str $ sin x))
                                        (sreplicate @_ @2
                                         $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 ((sscalar 2) * a0)))
                        (sreplicate @_ @3 a0))
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear [] [285.9579482947575])
    (crev h (sscalar 1.1))

testSin0Scan1RevPP1 :: Assertion
testSin0Scan1RevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v3 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [42.0,42.0]) ; v6 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) in v6 !$ [0] + tproject1 (dmapAccumRDer (SNat @2) (\\x9 -> tfromS (tpair (cos (sfromR (tproject1 (tproject2 (tproject2 x9)))) * (sscalar 0.0 + tproject1 (tproject2 x9) + tproject1 x9), sscalar 0.0))) (\\x17 -> tfromS (tpair ((sfromR (tproject1 (tproject2 (tproject2 (tproject1 x17)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))))) * (sscalar 0.0 + tproject1 (tproject2 (tproject2 x17)) + tproject1 (tproject2 x17)) + (tproject1 (tproject2 (tproject1 x17)) + tproject1 (tproject1 x17)) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))), sscalar 0.0))) (\\x33 -> tfromS (let x34 = let x31 = sscalar 0.0 + tproject1 (tproject1 x33) ; x32 = cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x33))))) * x31 in tpair (x32, tpair (x32, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x33)))))) * ((sscalar 0.0 + tproject1 (tproject2 (tproject2 x33)) + tproject1 (tproject2 x33)) * x31), sscalar 0.0))) in tpair (tproject1 x34, tpair (tproject1 (tproject2 x34), tpair (tproject1 (tproject2 (tproject2 x34)), tproject2 (tproject2 (tproject2 x34))))))) (sscalar 0.0) (tpair (sslice v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x36 -> tfromS (let x39 = sin (tproject1 x36) in tpair (x39, tpair (tproject1 x36, x39)))) (\\x42 -> tfromS (let x49 = tproject1 (tproject1 x42) * cos (tproject1 (tproject2 x42)) in tpair (x49, tpair (tproject1 (tproject1 x42), x49)))) (\\x52 -> tpair (cos (tproject1 (tproject2 x52)) * (sscalar 0.0 + sfromR (tproject2 (tproject2 (tproject1 x52))) + tproject1 (tproject1 x52)) + sfromR (tproject1 (tproject2 (tproject1 x52))), sscalar 0.0)) (sscalar 1.1) v3)), v3)))))"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) in cos (sscalar 1.1) * (cos (sin (sscalar 1.1)) * v4 !$ [0]) + cos (sscalar 1.1) * v4 !$ [1] + v4 !$ [2])"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [42.0,42.0]) in sappend (sreplicate (sscalar 1.0)) (sfromR (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> tfromS (let x16 = tproject1 x9 * cos (sfromR (tproject1 (tproject2 (tproject2 x9)))) in tpair (x16, x16))) (\\x18 -> tfromS (let x25 = tproject1 (tproject1 x18) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x18))))) + (sfromR (tproject1 (tproject2 (tproject2 (tproject1 x18)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x18))))))) * tproject1 (tproject2 x18) in tpair (x25, x25))) (\\x33 -> tfromS (let x32 = sscalar 0.0 + sfromR (tproject2 (tproject1 x33)) + tproject1 (tproject1 x33) in tpair (cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x33))))) * x32, tpair (sscalar 0.0, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x33)))))) * (tproject1 (tproject2 x33) * x32), sscalar 0.0))))) (sscalar 1.0) (tpair (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x44 -> tfromS (let x47 = sin (tproject1 x44) in tpair (x47, tpair (tproject1 x44, x47)))) (\\x50 -> tfromS (let x51 = tproject1 (tproject1 x50) * cos (tproject1 (tproject2 x50)) in tpair (x51, tpair (tproject1 (tproject1 x50), x51)))) (\\x54 -> tpair (cos (tproject1 (tproject2 x54)) * (sscalar 0.0 + sfromR (tproject2 (tproject2 (tproject1 x54))) + tproject1 (tproject1 x54)) + sfromR (tproject1 (tproject2 (tproject1 x54))), sscalar 0.0)) (sscalar 1.1) v4)), v4)))))))"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "(\\x1 -> rfromS (let v4 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [42.0,42.0]) in sappend (sreplicate (sfromR (tproject1 x1))) (sfromR (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> tfromS (let x16 = sfromR (tproject1 x9) * cos (sfromR (tproject1 (tproject2 (tproject2 x9)))) in tpair (x16, x16))) (\\x17 -> tfromS (let x24 = sfromR (tproject1 (tproject1 x17)) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))) + (sfromR (tproject1 (tproject2 (tproject2 (tproject1 x17)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))))) * sfromR (tproject1 (tproject2 x17)) in tpair (x24, x24))) (\\x31 -> tfromS (let x30 = sscalar 0.0 + sfromR (tproject2 (tproject1 x31)) + sfromR (tproject1 (tproject1 x31)) in tpair (cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x31))))) * x30, tpair (sscalar 0.0, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x31)))))) * (sfromR (tproject1 (tproject2 x31)) * x30), sscalar 0.0))))) (tproject1 x1) (tpair (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x37 -> tfromS (let x40 = sin (sfromR (tproject1 x37)) in tpair (x40, tpair (tproject1 x37, x40)))) (\\x42 -> tfromS (let x43 = sfromR (tproject1 (tproject1 x42)) * cos (sfromR (tproject1 (tproject2 x42))) in tpair (x43, tpair (tproject1 (tproject1 x42), x43)))) (\\x45 -> tfromS (tpair (cos (sfromR (tproject1 (tproject2 x45))) * (sscalar 0.0 + sfromR (tproject2 (tproject2 (tproject1 x45))) + sfromR (tproject1 (tproject1 x45))) + sfromR (tproject1 (tproject2 (tproject1 x45))), sscalar 0.0))) (tproject2 x1) v4)), v4)))))))) (tfromS (tpair (sscalar 1.0, sscalar 1.1)))"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v3 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [5.0,7.0]) ; v6 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) in v6 !$ [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v3)), v3)))))"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rscan @_ @(TKScalar Double) (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7])))
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v5 x1 -> rfromS (let v2 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [5.0,7.0]) in sfromR v5 !$ [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice (sfromR v5), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> x1 v2)), v2)))))"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - rscalar 5) - rscalar 7, sin x0 - rscalar 5, x0])
                 (rscalar 1.1)
  printArtifactPretty @_ @(TKR 1 Double) IM.empty (simplifyArtifact art)
    @?= "\\v3 x1 -> rfromS (cos (sfromR x1) * (cos (sin (sfromR x1) - sscalar 5.0) * sfromR v3 !$ [0]) + cos (sfromR x1) * sfromR v3 !$ [1] + sfromR v3 !$ [2])"

testSin0Scan1Rev2 :: Assertion
testSin0Scan1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [1.1961317861865948] :: RepN (TKR 0 Double))
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                    (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1))

testSin0Scan1Rev2ForComparison :: Assertion
testSin0Scan1Rev2ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [1.1961317861865948] :: RepN (TKR 0 Double))
    (rev' (\x0 -> rfromList [sin (sin x0 - rscalar 5) - rscalar 7, sin x0 - rscalar 5, x0]) (rscalar 1.1))

testSin0Scan1Rev3PP0 :: Assertion
testSin0Scan1Rev3PP0 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v3 = sfromVector (fromList [sscalar 1.1 * sscalar 5.0, sscalar 1.1 * sscalar 7.0]) ; v6 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) ; v7 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v3)), v3))) in v6 !$ [0] + sscalar 5.0 * tproject2 v7 !$ [0] + sscalar 7.0 * tproject2 v7 !$ [1] + tproject1 v7)"


testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * rscalar 5) - x0 * rscalar 7, sin x0 - x0 * rscalar 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) ; x5 = v4 !$ [1] ; x6 = v4 !$ [0] ; x7 = cos (sin (sscalar 1.1) - sscalar 1.1 * sscalar 5.0) * x6 in cos (sscalar 1.1) * x7 + sscalar 5.0 * (sscalar -1.0 * x7) + sscalar 7.0 * (sscalar -1.0 * x6) + cos (sscalar 1.1) * x5 + sscalar 5.0 * (sscalar -1.0 * x5) + v4 !$ [2])"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = sfromVector (fromList [sscalar 1.1 * sscalar 5.0, sscalar 1.1 * sscalar 7.0]) in sappend (sreplicate (sscalar 1.0)) (sfromR (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sfromVector (fromList [sscalar 1.0 * sscalar 5.0, sscalar 1.0 * sscalar 7.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v4)), v4)))))))"

testSin0Scan1Rev3 :: Assertion
testSin0Scan1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (ringestData [] [-10.076255083995068] :: RepN (TKR 0 Double))
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1))

testSin0Scan1Rev3ForComparison :: Assertion
testSin0Scan1Rev3ForComparison = do
  assertEqualUpToEpsilon' 1e-5
    (ringestData [] [-10.076255083995068] :: RepN (TKR 0 Double))
    (rev' (\x0 -> rfromList [sin (sin x0 - x0 * rscalar 5) - x0 * rscalar 7, sin x0 - x0 * rscalar 5, x0]) (rscalar 1.1))

testSin0Scan0fwd :: Assertion
testSin0Scan0fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [1] [1.0])
    (rfwd1 @RepN @Double @0 @1
    (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 1 Double)
         f x0 = rscan (\x _a -> sin x)
                      x0 (rzero @f @Double (0 :$: ZSR))
     in f) (rscalar 1.1))

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 (rrepl @Double @1 [1] 42))
          (rscalar 1.1))

testSin0Scan1FwdForComparison :: Assertion
testSin0Scan1FwdForComparison = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rfromList [x0, sin x0]) (rscalar 1.1))

testSin0Scan8fwd :: Assertion
testSin0Scan8fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @RepN @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Scan8fwd2 :: Assertion
testSin0Scan8fwd2 = do
  let h = rfwd1 @(ADVal RepN) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [285.95794829475744])
    (crev h (rscalar 1.1))

testUnitriangular0PP :: Assertion
testUnitriangular0PP = do
  resetVarCounter
  let k = 1000000
      a1 = rbuild1 @(AstTensor AstMethodLet PrimalSpan) @(TKScalar Double) @1 k
           $ \i -> rbuild1 k
           $ \j -> ifF (i <=. j) (rscalar 0) (rscalar 1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sgather (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1]))"

unitriangular1 :: (KnownNat k, GoodScalar rk, ADReady target)
               => Int -> IShR k -> target (TKR (2 + k) rk)
unitriangular1 k sh =
  rbuild1 k $ \i ->
    rbuild1 k $ \j ->
      ifF (i <=. j) (rreplicate0N sh (rscalar 0)) (rreplicate0N sh (rscalar 1))

testUnitriangular1PP :: Assertion
testUnitriangular1PP = do
  resetVarCounter
  let sh = 200 :$: 300 :$: 600 :$: ZSR
      k = 1000000
      a1 = unitriangular1 @3 @Double @(AstTensor AstMethodLet PrimalSpan) k sh
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sgather (sfromVector (fromList [sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sscalar 0.0))))), sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sscalar 1.0)))))])) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6]))"

unitriangular2 :: (KnownNat k, GoodScalar rk, ADReady target)
               => Int -> IShR k -> target (TKR (2 + k) rk)
unitriangular2 k sh =
  rgather @_ @_ @_ @_ @1 (k :$: k :$: sh)
          (rfromList [ rreplicate0N sh (rscalar 0)
                     , rreplicate0N sh (rscalar 1) ])
          (\(i :.: j :.: ZIR) -> ifF (i <. j) 0 1 :.: ZIR)

testUnitriangular2PP :: Assertion
testUnitriangular2PP = do
  resetVarCounter
  let sh = 200 :$: 300 :$: 600 :$: ZSR
      k = 1000000
      a1 = unitriangular2 @3 @Double @(AstTensor AstMethodLet PrimalSpan) k sh
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sgather (sfromVector (fromList [sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sscalar 0.0))))), sreplicate (sreplicate (sreplicate (sreplicate (sreplicate (sscalar 1.0)))))])) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4]))"

rscanZip :: forall rn n rn2 n2 target.
            (GoodScalar rn, KnownNat n, GoodScalar rn2, KnownNat n2, ADReady target)
         => (forall f. ADReady f => f (TKR n rn) -> f (TKR n2 rn2) -> f (TKR n rn))
         -> FullTensorKind (TKR n2 rn2)
         -> target (TKR n rn)
         -> target (TKR (1 + n2) rn2)
         -> target (TKR (1 + n) rn)
rscanZip f eShs acc0 es =
  let width = rlength es
      ftk = tftk stensorKind acc0
  in withSNat width $ \snat ->
    tlet
      (dmapAccumL Proxy snat ftk ftk eShs
         (let g :: forall f. ADReady f
                => f (TKR n rn) -> f (TKR n2 rn2)
                -> f (TKProduct (TKR n rn) (TKR n rn))
              g acc e = tlet (f acc e) (\res -> tpair res res)
          in g)
         acc0 es)
      (\res -> rappend (rfromList [acc0]) (tproject2 res))

testSin0rmapAccumRD0SC :: Assertion
testSin0rmapAccumRD0SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                  -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                  -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Double)
              f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD0RC :: Assertion
testSin0rmapAccumRD0RC = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 1)
    (crev (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ dunHVector xh V.! 0
                             in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ dunHVector xh V.! 0
                             in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SC :: Assertion
testSin0rmapAccumRD01SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = flip (sindex0 @_ @'[1]) [0] $ (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [DynamicShaped x0, DynamicShaped x0])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD01SN :: Assertion
testSin0rmapAccumRD01SN = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 1
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[] (srepl 3)
                                      , DynamicShaped x0 ])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN2 :: Assertion
testSin0rmapAccumRD01SN2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[1] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN3 :: Assertion
testSin0rmapAccumRD01SN3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[1, 3] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[2]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1, 2] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN4 :: Assertion
testSin0rmapAccumRD01SN4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[1, 3] Double)
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN5 :: Assertion
testSin0rmapAccumRD01SN5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[1, 3] Double)
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN51 :: Assertion
testSin0rmapAccumRD01SN51 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-69.90586521651421))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = (\res -> ssum @_ @_ @6 (sfromD (res V.! 0))
                               + ssum0 @_ @_ @'[6, 5, 4, 3]
                                   (sfromD (res V.! 2)))
                      $ dunHVector
                      $ dbuild1 @f (SNat @6) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[4, 3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                    x1 = sfromD @Double @'[3] $ xh V.! 1
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3) ])
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sbuild1 @_ @_ @4 $ \i ->
                                             sfromD (a V.! 1)
                                             - sin x1 / sreplicate @_ @3
                                                          (srepl 1 + sfromIndex0 i) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped $ x0 / (srepl 1 + sfromIndex0 j)
                                      , DynamicShaped $ sreplicate @_ @3 x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 3]
                                           $ sreplicate0N @_ @_ @'[5, 3]
                                               (sfromIndex0 j)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ]))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN52 :: Assertion
testSin0rmapAccumRD01SN52 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2207726343670955)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5, 3] Double)
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN53 :: Assertion
testSin0rmapAccumRD01SN53 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6.529656272211302)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5, 3] Double)
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 2) ])
                                            (dmkHVector
                                    $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[4]
                                                       (sfromD (a V.! 3)) [1]
                                              - smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sfromD (a V.! 2)
                                                   / sin x / srepl 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1)))
                                           + sin x / srepl 3 ])
                          in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531 :: Assertion
testSin0rmapAccumRD01SN531 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3]
       [-0.4284609293514655,0.2047077016162759,0.9242422110631052])
    (rev' (let f :: forall f. ADReady f => f (TKS '[3] Double) -> f (TKS '[2, 3] Double)
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ ingestData [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1) ])
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ srepl 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (ingestData
                                           [0.4, -0.01, -0.3, 0.2, 0.5, 1.3]) ])
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531a :: Assertion
testSin0rmapAccumRD01SN531a = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3]
       [1.8478609886246988,-22.194216099801963,-40.72162125038692])
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[3] Double) -> f (TKS '[2, 2, 2, 3] Double)
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[6] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    x2 = sfromD @Double @'[6] $ xh V.! 1
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList
                                             [srepl 0.01, ssum @_ @_ @6 x2, srepl 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - sfromD (a V.! 1))) ])
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sreplicate @_ @3 (sfromIndex0 j))
                                      , DynamicShaped
                                        $ sreplicate @_ @6 (sfromIndex0 i)
                                          - sflatten (sappend x0 x0) ] )
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [srepl (-0.1), sreshape @_ @_ @'[] @'[1] $ sfromIndex0 j])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sscalar 0.4, sscalar (-0.01), sscalar (-0.3), sfromIndex0 i, sscalar 0.5, sscalar 1.3]) ])))
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531b0 :: Assertion
testSin0rmapAccumRD01SN531b0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKR 0 Double) -> f (TKR 2 Double)
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromR x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SN531bS :: Assertion
testSin0rmapAccumRD01SN531bS = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f(TKS  '[2, 2] Double)
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531bR :: Assertion
testSin0rmapAccumRD01SN531bR = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKR 0 Double) -> f (TKR 2 Double)
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicRanked x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [1] [0] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SN531b0PP :: Assertion
testSin0rmapAccumRD01SN531b0PP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR 2 Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPrettyButNested
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h21 -> tpair ([sproject (tproject1 h21) 0], [0])) (\\h25 -> tpair ([sproject (tproject1 (tproject1 h25)) 0], [rfromS (sscalar 0.0)])) (\\h30 -> tpair ([sproject (tproject1 (tproject1 h30)) 0], tpair ([], tpair ([0], [0])))) [sscalar 4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) (\\h31 -> tpair ([sproject (tproject1 h31) 0], tpair (tproject1 h31, []))) (\\h35 -> tpair ([sproject (tproject1 (tproject1 h35)) 0], tpair (tproject1 (tproject1 h35), []))) (\\h41 -> tpair ([sproject (tproject1 (tproject1 h41)) 0 + sproject (tproject1 (tproject2 (tproject1 h41))) 0], [0])) [sscalar 1.1] [rfromS (tconcrete (FTKS [0] FTKScalar) (sfromListLinear [0] []))])), [rfromS (tconcrete (FTKS [0] FTKScalar) (sfromListLinear [0] []))]))))) 0)]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS '[2, 2] Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          x0
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscalar 4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sscalar 1.1] [tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])])), [tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])]))))) 0]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS '[2, 2] Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          x0
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet FullSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "(\\h1 -> [sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscalar 4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject h1 0] [tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])])), [tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])]))))) 0]) [sscalar 1.1]"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR 2 Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIndex0 (i + j)
                                 + sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum0 (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (stranspose (sreplicate siota) + sreplicate siota) + sreplicate (sreplicate (sscalar 1.1))] [rfromS (stranspose (sreplicate (sreplicate (tconcrete (FTKS [0] FTKScalar) (sfromListLinear [0] [])))))])), [rfromS (stranspose (sreplicate (sreplicate (tconcrete (FTKS [0] FTKScalar) (sfromListLinear [0] [])))))]))))) 0))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS '[2, 2] Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIndex0 (i + j)
                                 + sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[ssum0 (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sfromIntegral (stranspose (sreplicate siota) + sreplicate siota) + sreplicate (sreplicate (sscalar 1.1))] [stranspose (sreplicate (sreplicate (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0]))))])), [stranspose (sreplicate (sreplicate (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0]))))]))))) 0)]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR 2 Double)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)

                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicRanked @Double @0
                               $ rfromIndex0 (i + j)
                                 + rfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [1] [0] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum0 (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rfromS (tconcrete (FTKS [2,2] FTKScalar) (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]))] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromS (sfromIntegral (stranspose (sreplicate siota) + sreplicate siota) + sreplicate (sreplicate (sscalar 1.1)))] [rfromS (stranspose (sreplicate (sreplicate (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])))))])), [rfromS (stranspose (sreplicate (sreplicate (tconcrete (FTKS [1] FTKScalar) (sfromListLinear [1] [0.0])))))]))))) 0))]"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-1.8866871148429984))
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[2, 2, 2] Double)
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 1))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                         (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sfromIndex0 j) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIndex0 i]) ])))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531d :: Assertion
testSin0rmapAccumRD01SN531d = do
  assertEqualUpToEpsilon 1e-10
    V.empty
    ((let f :: forall f. ADReady f
            => f (TKS '[] Double) -> HVector f
          f x0 = dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @0) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                            in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIndex0 j) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIndex0 i]) ])))
      in f . sfromR) (rscalar 1.1 :: RepN (TKR 0 Double)))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN531Slice :: Assertion
_testSin0rmapAccumRD01SN531Slice = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[2, 2] Double)
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList [ DynamicShaped x ])
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [])))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN54 :: Assertion
testSin0rmapAccumRD01SN54 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.538239371140263)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5, 3] Double)
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0)))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                 let x = sfromD @Double @'[3] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sin x - sfromD (a V.! 2) ])
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN55 :: Assertion
_testSin0rmapAccumRD01SN55 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6.529656272211302)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5, 3] Double)
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    a = xh
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[4]
                                                       (sfromD (a V.! 0)) [1]
                                              - smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sfromD (a V.! 0)
                                                   / sin x / srepl 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 0)))
                                           + sin x / srepl 3 ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN55acc :: Assertion
testSin0rmapAccumRD01SN55acc = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3] [-21.0,-42.0,-21.0])
    (rev' (let f :: forall f. ADReady f => f (TKS '[3] Double) -> f (TKS '[2, 3] Double)
               f x0 = (\res -> srepl 2 - str (sreplicate @_ @3
                                         $ ssum @_ @_ @7
                                         $ str (sfromD (res V.! 1)))
                               - sfromD (res V.! 2))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g _xh a =
                                let x = sreplicate @g @3 (sscalar 2)
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [])
                                         (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ ingestData [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate0N (sscalar 1) - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / sreplicate0N (sscalar 3)
                                           - sreplicate @_ @3
                                             (sindex0 @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / sreplicate0N (sscalar 3))) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sindex0 x0 [1], sscalar (-0.01), sscalar (-0.3), ssum x0, sscalar 0.5, sscalar 1.3]) ])
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN56 :: Assertion
testSin0rmapAccumRD01SN56 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                            (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[2] knownShS [0.4989557335681351,1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[2] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x])
                                           (dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[5] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1)])
                                           (dmkHVector
                                      [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[5] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[1] knownShS [1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[1] Double)
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                       (dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[1] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN6 :: Assertion
testSin0rmapAccumRD01SN6 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReady f => f (TKS '[] Double) -> HVector f
               f x0 = dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           `atan2F` smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (dmkHVector
                                    $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                      (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in dmkHVector . f) (sscalar 1.1))

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f TKUntyped
               f x0 = productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           ** smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sin x / srepl 6
                                              + sindex0 @_ @'[2]
                                                        (sfromD (a V.! 2)) [1]
                                                / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 6) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in f @(ADVal RepN)) (sscalar 1.1))

testSin0ScanD51 :: Assertion
testSin0ScanD51 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [319.68688158967257] :: RepN (TKR 4 Double))
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rreplicate 2 $ rreplicate 5
                                          $ rsum $ rsum a))
                         (FTKR (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR) FTKScalar)
                         (rreplicate0N [1,1,1,1] (rscalar 2) * a0)
                         (rreplicate 3 (rreplicate 8 (rreplicate 3 a0)))
                         )
          (ringestData [1,1,1,1] [1.1]))

testSin0ScanD8 :: Assertion
testSin0ScanD8 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR 3 Double))
    (rev' (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum (rreplicate 7 a))))
                       (FTKR (1 :$: 1 :$: 1 :$: ZSR) FTKScalar)
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                       (rreplicate 3 a0))
          (ringestData [1,1,1] [1.1]))

testSin0ScanD8MapAccum :: Assertion
testSin0ScanD8MapAccum = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR 3 Double))
    (rev'
       (\a0 -> (rfromD @_ @6 . (V.! 1))
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                   (let g :: forall g. ADReady g
                          => g TKUntyped -> g TKUntyped -> g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @5 $ dunHVector xh V.! 0
                         in tpair (dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector a))))
                                   (dmkHVector $ V.singleton $ DynamicRanked x)
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5
                                      (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0))
       (ringestData [1,1,1] [1.1]))

testSin0ScanD8rev :: Assertion
testSin0ScanD8rev = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [9.53298735735276])
    (rrev1 @RepN @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum (rreplicate 7 a))))
                       (FTKR ZSR FTKScalar)
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8rev4 :: Assertion
testSin0ScanD8rev4 = do
  let h :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      h = rrev1 @f @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum (rreplicate 7 a))))
                       (FTKR ZSR FTKScalar)
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (rreplicate 3 a0))
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [285.95794829475744])
    (rev' h (rscalar 1.1))

testSin0ScanD1RevPP :: Assertion
testSin0ScanD1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (FTKR ZSR FTKScalar)
                           x0 (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [42.0,42.0]) ; v8 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) in tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice v8, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v4)), v4)))) + v8 !$ [0])"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (FTKR ZSR FTKScalar)
                           x0 (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v5 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [42.0,42.0]) in sappend (sreplicate (sscalar 1.0)) (sfromR (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v5)), v5)))))))"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                         (FTKR ZSR FTKScalar)
                         x0 (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v4 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [5.0,7.0]) ; v8 = tconcrete (FTKS [3] FTKScalar) (sfromListLinear [3] [1.0,1.0,1.0]) in tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice v8, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v4)), v4)))) + v8 !$ [0])"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                         (FTKR ZSR FTKScalar)
                         x0 (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v5 = tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [5.0,7.0]) in sappend (sreplicate (sscalar 1.0)) (sfromR (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [2] FTKScalar) (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v5)), v5)))))))"


testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                                (FTKR ZSR FTKScalar)
                                x0 (rfromList [x0 * rscalar 5, x0 * rscalar 7]))
                 (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let v5 = sfromVector (fromList [sscalar 1.1 * sscalar 5.0, sscalar 1.1 * sscalar 7.0]) in sappend (sreplicate (sscalar 1.0)) (sfromR (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sfromVector (fromList [sscalar 1.0 * sscalar 5.0, sscalar 1.0 * sscalar 7.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) v5)), v5)))))))"

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (FTKR ZSR FTKScalar)
                   x0 (rrepl @Double @1 [1] 42))
          (rscalar 1.1))

testSin0ScanD8fwd :: Assertion
testSin0ScanD8fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @RepN @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum (rreplicate 7 a))))
                      (FTKR ZSR FTKScalar)
                      (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                      (rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8fwdMapAccum :: Assertion
testSin0ScanD8fwdMapAccum = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @RepN @Double @0 @3 @Double
       (\a0 -> rreverse $ (rfromD . (V.! 1))
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                   (let g :: forall g. ADReady g
                          => g TKUntyped -> g TKUntyped -> g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @2 $ dunHVector xh V.! 0
                         in tpair (dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector a))))
                                   (dmkHVector $ V.singleton $ DynamicRanked x)
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0)) (rscalar 1.1))

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal RepN) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum (rreplicate 7 a))))
                       (FTKR ZSR FTKScalar)
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [285.95794829475744])
    (crev h (rscalar 1.1))

testSin0FoldNestedS1 :: Assertion
testSin0FoldNestedS1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1PP :: Assertion
testSin0FoldNestedS1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
      f z = sfold (\x a ->
               sfold (\x2 a2 -> x2 + tan a2)
                     a (sreplicate @_ @22 x))
                  z (sreplicate @_ @11 z)
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g x = srev (\v -> f (sfromD $ dunHVector v V.! 0))
                 (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
                 (dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [11] FTKScalar) (sfromListLinear [11] [Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.1) (sreplicate (sscalar 1.1)))), sreplicate (sscalar 1.1)))) in [ssum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR1PP :: Assertion
testSin0FoldNestedR1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [11] FTKScalar) (sfromListLinear [11] [Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.1) (sreplicate (sscalar 1.1)))), sreplicate (sscalar 1.1)))) in [rfromS (ssum (tproject2 v5) + tproject1 v5)]"

testSin0FoldNestedR1SimpPP :: Assertion
testSin0FoldNestedR1SimpPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (dmkHVector x)
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (tconcrete (FTKS [11] FTKScalar) (sfromListLinear [11] [Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.1) (sreplicate (sscalar 1.1)))), sreplicate (sscalar 1.1)))) in [rfromS (ssum (tproject2 v5) + tproject1 v5)]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInlineContract
       $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 1940

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInlineContract
       $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 23985

testSin0FoldNestedR2LengthPPs :: Assertion
testSin0FoldNestedR2LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 -> x3 + tan a3)
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 325479

testSin0FoldNestedR3LengthPPs :: Assertion
testSin0FoldNestedR3LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 ->
                   rfold (\x4 a4 -> x4 + tan a4)
                         a3 (rreplicate 2 x3))
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4971510

-- Takes 100s, probably due to some of the pipelines forcing all derivs.
_testSin0FoldNestedR4LengthPPs :: Assertion
_testSin0FoldNestedR4LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 ->
                   rfold (\x4 a4 ->
                     rfold (\x5 a5 -> x5 + tan a5)
                           a4 (rreplicate 2 x4))
                         a3 (rreplicate 2 x3))
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

_testSin0FoldNestedR5LengthPPs :: Assertion
_testSin0FoldNestedR5LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 ->
                   rfold (\x4 a4 ->
                     rfold (\x5 a5 ->
                       rfold (\x6 a6 -> x6 + tan a6)
                             a5 (rreplicate 2 x5))
                           a4 (rreplicate 2 x4))
                         a3 (rreplicate 2 x3))
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

testSin0FoldNestedR2LengthPPsDummy7 :: Assertion
testSin0FoldNestedR2LengthPPsDummy7 = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\_x3 _a3 -> rscalar 7)
                   -- the 7 causes Dummy RepM values
                   -- with the more precise typing of folds
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 94483

testSin0FoldNestedR2Dummy7 :: Assertion
testSin0FoldNestedR2Dummy7 = do
 resetVarCounter
 assertEqualUpToEpsilon' 1e-10
  (rscalar 0 :: RepN (TKR 0 Double))
  (rev'
   (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
        f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\_x3 _a3 -> rscalar 7)
                   -- the 7 causes Dummy RepM values
                   -- with the more precise typing of folds
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0FoldNestedR2Tan :: Assertion
testSin0FoldNestedR2Tan = do
 assertEqualUpToEpsilon' 1e-10
  (rscalar 25.000016360009603 :: RepN (TKR 0 Double))
  (rev'
   (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
        f z = rfold (\x a ->
                 rfold (\x2 a2 ->
                   rfold (\x3 a3 -> x3 + tan a3)
                         a2 (rreplicate 2 x2))
                       a (rreplicate 2 x))
                    z (rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 -> let y = rfromD @Double @0 $ dunHVector x4 V.! 0
                                        w = rfromD @Double @0 $ dunHVector a4 V.! 0
                                    in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (dmkHVector V.empty))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 6020372

testSin0MapAccumNestedR4 :: Assertion
testSin0MapAccumNestedR4 = do
 assertEqualUpToEpsilon' 1e-10
  (rscalar 1.0410225027528066 :: RepN (TKR 0 Double))
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 -> let y = rfromD @Double @0 $ dunHVector x5 V.! 0
                                          w = rfromD @Double @0 $ dunHVector a5 V.! 0
                                      in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR5 :: Assertion
testSin0MapAccumNestedR5 = do
 assertEqualUpToEpsilon' 1e-10
  (rscalar 6.308416949436515e-16 :: RepN (TKR 0 Double))
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector x6 V.! 0
                                            w = rfromD @Double @0 $ dunHVector a6 V.! 0
                                        in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * (y + tan w))
                                                    (dmkHVector V.empty))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 1.1))

testSin0MapAccumNestedR5r :: Assertion
testSin0MapAccumNestedR5r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.0837278549794862 :: RepN (TKR 0 Double))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector x6 V.! 0
                                            w = rfromD @Double @0 $ dunHVector a6 V.! 0
                                        in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10r :: Assertion
testSin0MapAccumNestedR10r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781 :: RepN (TKR 0 Double))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10f :: Assertion
testSin0MapAccumNestedR10f = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781e-4 :: RepN (TKR 0 Double))
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10fN :: Assertion
testSin0MapAccumNestedR10fN = do
 assertEqualUpToEpsilon 1e-10
  (tpair (srepl 1.379370673816781e-4 :: RepN (TKS '[1] Float))
         (rscalar 1.379370673816781e-4 :: RepN (TKR 0 Double)))
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      f :: forall f. ADReady f => f (TKR 0 Double)
        -> f (TKProduct (TKS '[1] Float) (TKR 0 Double))
      f x = tpair (sfromList [scast $ sfromR $ g x]) (g x + rscalar 0.2)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10rf :: Assertion
testSin0MapAccumNestedR10rf = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: RepN (TKR 0 Double))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rfwd1 f) (rscalar 0.0001))

testSin0MapAccumNestedR10rr :: Assertion
testSin0MapAccumNestedR10rr = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: RepN (TKR 0 Double))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rrev1 f) (rscalar 0.0001))

productToVectorOf
  :: ADReady f
  => f (TKProduct TKUntyped TKUntyped)
  -> f TKUntyped
productToVectorOf p = tlet @_ @_ @TKUntyped (tproject1 p) $ \p1 ->
                          tlet (tproject2 p) $ \p2 ->
                            dmkHVector $ dunHVector p1 V.++ dunHVector p2

testSin0FoldNestedS1FwdFwd0 :: Assertion
testSin0FoldNestedS1FwdFwd0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . sfwd1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1FwdFwd :: Assertion
testSin0FoldNestedS1FwdFwd = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * sfwd1 (sfwd1 (\b2 -> srepl 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfwd1 $ rfromS . sfwd1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1RevRev :: Assertion
testSin0FoldNestedS1RevRev = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * srev1 (srev1 (\b2 -> srepl 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rrev1 $ rfromS . srev1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS2 :: Assertion
testSin0FoldNestedS2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 -> srepl 0.7 * x3 * a3)
                                a2 (sreplicate @_ @4 x2))
                              a (sreplicate @_ @3 x))
                            a0 (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS3 :: Assertion
testSin0FoldNestedS3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 7.320500000000004e-4 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 -> srepl 0.1 * x4 * a4)
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @2 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS4 :: Assertion
testSin0FoldNestedS4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2400927000000009e-5 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 -> srepl 0.1 * x5 * a5)
                                    a4 (sreplicate @_ @2 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @2 x))
                            a0 (sreplicate @_ @1 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS5 :: Assertion
testSin0FoldNestedS5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.22000000000000003 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> sscalar 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)

           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS5rev :: Assertion
testSin0FoldNestedS5rev = do
  let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
      f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> sscalar 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)
  assertEqualUpToEpsilon 1e-10
    (srepl 0.22000000000000003)
    (srev1 @RepN @Double @'[] @'[] f (sscalar 1.1))

testSin0FoldNestedS5fwd :: Assertion
testSin0FoldNestedS5fwd = do
  let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
      f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> sscalar 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)
  assertEqualUpToEpsilon 1e-10
    (srepl 0.22000000000000003)
    (sfwd1 @RepN @Double @'[] @'[] f (sscalar 1.1))

testSin0FoldNestedSi :: Assertion
testSin0FoldNestedSi = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar  (-0.20775612781643243) :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[3] Double)
               f a0 = sfold (\x a -> atan2F
                                       (sscan (+) (ssum x)
                                          (sscan (*) (srepl 2)
                                                 (sreplicate @_ @1 a)))
                                       (sscan (\x1 a1 ->
                                          sfold (\x2 a2 ->
                                            sfold (\x3 a3 ->
                                                     (srepl 0.001) * (x3 * a3 - x3))
                                                  a2 (sscan (+) x2
                                                        (sreplicate @_ @3 a2)))
                                                x1 (sreplicate @_ @1 a1))
                                              a (sscan (-) (srepl 0)
                                                   (sslice (Proxy @0)
                                                           (Proxy @1) x))))
                            (sreplicate @_ @3 $ srepl 2 * a0) (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedR1 :: Assertion
testSin0FoldNestedR1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 -> rscalar 0.7 * x2 * a2)
                              a (rreplicate 7 x))
                            a0 (rreplicate 3 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR1RevFwd :: Assertion
testSin0FoldNestedR1RevFwd = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                                 x2 * rfwd1 (rrev1 (\b2 -> rscalar 0.7 * b2)) a2)
                              a (rreplicate 4 x))
                            a0 (rreplicate 2 a0)
           in rrev1 $ rfwd1 f) (rscalar 1.1))

testSin0FoldNestedR2 :: Assertion
testSin0FoldNestedR2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 -> rscalar 0.7 * x3 * a3)
                                a2 (rreplicate 4 x2))
                              a (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR2RevFwd :: Assertion
testSin0FoldNestedR2RevFwd = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                                   x3 * rrev1 (rfwd1 (rrev1 (\b3 ->
                                                               rscalar 0.7 * b3))) a3)
                                a2 (rreplicate 4 x2))
                              a (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in rfwd1 $ rrev1 $ rfwd1 f) (rscalar 1.1))

testSin0FoldNestedR3 :: Assertion
testSin0FoldNestedR3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 7.320500000000004e-4 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 -> rscalar 0.1 * x4 * a4)
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 2 x2))
                              a (rreplicate 1 x))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR4 :: Assertion
testSin0FoldNestedR4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2400927000000009e-5 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> rscalar 0.1 * x5 * a5)
                                    a4 (rreplicate 2 x4))
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 1 x2))
                              a (rreplicate 2 x))
                            a0 (rreplicate 1 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR41 :: Assertion
testSin0FoldNestedR41 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.22000000000000003 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> rscalar 0.1 * x5 * a5)
                                    a4 (rreplicate 1 x4))
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 1 x2))
                              a (rreplicate 1 x))
                            a0 (rreplicate 1 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR40 :: Assertion
testSin0FoldNestedR40 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> rscalar 0.1 * x5 * a5)
                                    a4 (rreplicate 0 x4))
                                  a3 (rreplicate 0 x3))
                                a2 (rreplicate 0 x2))
                              a (rreplicate 0 x))
                            a0 (rreplicate 0 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR400 :: Assertion
testSin0FoldNestedR400 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\_x5 _a5 -> 0)
                                    a4 (rreplicate 0 x4))
                                  a3 (rreplicate 0 x3))
                                a2 (rreplicate 0 x2))
                              a (rreplicate 0 x))
                            a0 (rreplicate 0 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedRi :: Assertion
testSin0FoldNestedRi = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.20775612781643243) :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 1 Double)
               f a0 = rfold (\x a -> atan2F
                                       (rscan (+) (rsum x)
                                          (rscan (*) (rscalar 2)
                                                 (rreplicate 1 a)))
                                       (rscan (\x1 a1 ->
                                          rfold (\x2 a2 ->
                                            rfold (\x3 a3 ->
                                                     (rscalar 0.001) * (x3 * a3 - x3))
                                                  a2 (rscan (+) x2
                                                            (rreplicate 3 a2)))
                                                x1 (rreplicate 1 a1))
                                              a (rscan (-) (rscalar 0) (rslice 0 1 x))))
                            (rreplicate 3 $ (rscalar 2) * a0) (rreplicate 2 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR22 :: Assertion
testSin0FoldNestedR22 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.877421010384167e-5 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 -> rscalar 0.44 * x3 * a3)
                                a2 (rscan (\x4 a4 -> x4 + a4) x2
                                          (rreplicate 2 a2)))
                              (rfold (\x4 a4 -> x4 * a4) a
                                     (rreplicate 2 x)) (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR21 :: Assertion
testSin0FoldNestedR21 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 7.667553331540788e-3 :: RepN (TKR 0 Double))
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a -> tlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR21PP :: Assertion
testSin0FoldNestedR21PP = do
  resetVarCounter
  let a1 =
        rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0
          (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f a0 = rfold (\x a -> tlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInlineContract a1))
    @?= 47650

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @(TKScalar Double) @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
  assertEqualUpToEpsilon 1e-10
    (dmkHVector $ V.singleton $ DynamicRanked @Double @0 (rscalar 0.4535961214255773))
    (f @RepN (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

testSin0revhVPP :: Assertion
testSin0revhVPP = do
  resetVarCounter
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @(TKScalar Double) @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
  printAstSimple IM.empty (f @(AstTensor AstMethodLet PrimalSpan)
                                    (V.singleton
                                     $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rfromS (cos (sscalar 1.1) * sscalar 1.0))])"

testSin0revhV2 :: Assertion
testSin0revhV2 = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @(TKScalar Double) @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (rscalar (-0.8912073600614354)))
    (crev f (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

testSin0revhV3 :: Assertion
testSin0revhV3 = do
  let f :: forall g. ADReady g
        => HVector g -> g TKUntyped
      f x =
        srev @g @_ @(TKScalar Double) @'[] (\v -> sin (sfromD $ dunHVector v V.! 0))
             (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
             (dmkHVector x)
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[] (sscalar $ -0.8912073600614354))
    (crev f (V.singleton $ DynamicShaped @Double @'[] (srepl 1.1)))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let doms = FTKR ZSR FTKScalar
      doms3 = FTKR (3 :$: ZSR) FTKScalar
      f :: forall g. (BaseTensor g)
        => g (TKR 1 Double) -> g (TKR 1 Double)
      f x =
        rrevDt @g @_ @(TKScalar Double) @1
               (\v -> rscanZip const doms (rscalar 5) v)
                doms3 x (ringestData [4] [1, 2, 3, 4])
  assertEqualUpToEpsilon 1e-10
    (rfromList [rscalar 0, rscalar 0, rscalar 0])
    (crev f (rreplicate 3 (rscalar 1.1)))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let doms = FTKR ZSR FTKScalar
      doms3 = FTKS (SNat @3 :$$ ZSS) FTKScalar
      f :: forall g. (BaseTensor g)
        => g (TKS '[3] Double) -> g (TKS '[3] Double)
      f x =
        srevDt @g @_ @(TKScalar Double)
               (\v -> sfromR @_ @'[4] $ rscanZip const doms (rscalar 5) (rfromS v))
                doms3 x (ingestData @_ @'[4] [1, 2, 3, 4])
  assertEqualUpToEpsilon 1e-10
    (sfromList @_ @_ @3 [sscalar 0, sscalar 0, sscalar 0])
    (crev f (sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let doms = FTKR ZSR FTKScalar
      doms3 = FTKR (3 :$: ZSR) FTKScalar
      f :: forall g. (BaseTensor g)
        => g (TKR 1 Double) -> g (TKR 1 Double)
      f x =
        rrevDt @g @_ @(TKScalar Double) @1
               (\v -> rscanZip (\_ z -> z * z) doms (rscalar 5) v)
                doms3 x (ringestData [4] [1, 2, 3, 4])
  assertEqualUpToEpsilon 1e-10
    (ringestData [3] [4.0,6.0,8.0])
    (crev f (rreplicate 3 (rscalar 1.1)))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let doms = FTKR ZSR FTKScalar
      doms3 = FTKS (SNat @3 :$$ ZSS) FTKScalar
      f :: forall g. (BaseTensor g)
        => g (TKS '[3] Double) -> g (TKS '[3] Double)
      f x =
        srevDt @g @_ @(TKScalar Double)
               (\v -> sfromR @_ @'[4] $ rscanZip (\_ z -> z * z) doms (rscalar 5) (rfromS v))
                doms3 x (ingestData @_ @'[4] [1, 2, 3, 4])
  assertEqualUpToEpsilon 1e-10
    (ingestData @_ @'[3] [4.0,6.0,8.0])
    (crev f (sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV8 :: Assertion
testSin0revhV8 = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f = dmkHVector
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [1, 1, 1])
    (crev @_ @TKUntyped
          f
          (V.singleton $ DynamicShaped @Double @'[3]
           $ sreplicate @RepN @3 (sscalar 1.1)))
