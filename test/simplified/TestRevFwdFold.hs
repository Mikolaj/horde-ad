{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import Data.IntMap.Strict qualified as IM
import Data.Proxy (Proxy (Proxy))
import GHC.TypeLits (KnownNat, type (+))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested (IShR, IxR (..), KnownShS (..), ShR (..), ShS (..))
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
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
  , testCase "4S0rmapAccumRD0S" testSin0rmapAccumRD0S
  , testCase "4S0rmapAccumRD00SC" testSin0rmapAccumRD00SC
  , testCase "4S0rmapAccumRD00S0" testSin0rmapAccumRD00S0
  , testCase "4S0rmapAccumRD00S" testSin0rmapAccumRD00S
  , testCase "4S0rmapAccumRD00S7" testSin0rmapAccumRD00S7
  , testCase "4S0rmapAccumRD00SCacc0" testSin0rmapAccumRD00SCacc0
  , testCase "4S0rmapAccumRD00SCacc" testSin0rmapAccumRD00SCacc
  , testCase "4S0rmapAccumRD00Sacc0" testSin0rmapAccumRD00Sacc0
  , testCase "4S0rmapAccumRD00Sacc" testSin0rmapAccumRD00Sacc
  , testCase "4S0rmapAccumRD00SCall0" testSin0rmapAccumRD00SCall0
  , testCase "4S0rmapAccumRD00SCall" testSin0rmapAccumRD00SCall
  , testCase "4S0rmapAccumRD00Sall0" testSin0rmapAccumRD00Sall0
  , testCase "4S0rmapAccumRD00Sall" testSin0rmapAccumRD00Sall
  , testCase "4S0rmapAccumRD0R" testSin0rmapAccumRD0R
  , testCase "4S0rmapAccumRD01SN" testSin0rmapAccumRD01SN
  , testCase "4S0rmapAccumRD01SN3" testSin0rmapAccumRD01SN3
  , testCase "4S0rmapAccumRD01SN5" testSin0rmapAccumRD01SN5
  , testCase "4S0rmapAccumRD01SN51" testSin0rmapAccumRD01SN51
  , testCase "4S0rmapAccumRD01SN531a" testSin0rmapAccumRD01SN531a
  , testCase "4S0rmapAccumRD01SN531b0" testSin0rmapAccumRD01SN531b0
  , testCase "4S0rmapAccumRD01SN531b0PP" testSin0rmapAccumRD01SN531b0PP
  , testCase "4S0rmapAccumRD01SN531b0PPj" testSin0rmapAccumRD01SN531b0PPj
  , testCase "4S0rmapAccumRD01SN531bRPPj" testSin0rmapAccumRD01SN531bRPPj
  , testCase "4S0rmapAccumRD01SN531c" testSin0rmapAccumRD01SN531c
  , testCase "4S0rmapAccumRD01SN531Slice" testSin0rmapAccumRD01SN531Slice
  , testCase "4S0rmapAccumRD01SN55" testSin0rmapAccumRD01SN55
  , testCase "4S0rmapAccumRD01SN55acc" testSin0rmapAccumRD01SN55acc
  , testCase "4S0rmapAccumRD01SN58" testSin0rmapAccumRD01SN58
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
  , testCase "4S0FoldNestedR0LengthPPs" testSin0FoldNestedR0LengthPPs
  , testCase "4S0FoldNestedR1LengthPPs" testSin0FoldNestedR1LengthPPs
  , testCase "4S0FoldNestedR2LengthPPs" testSin0FoldNestedR2LengthPPs
  , testCase "4S0FoldNestedR3LengthPPs" testSin0FoldNestedR3LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR4LengthPPs" testSin0FoldNestedR4LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR5LengthPPs" testSin0FoldNestedR5LengthPPs
  , testCase "4S0FoldNestedR2LengthPPsDummy7" testSin0FoldNestedR2LengthPPsDummy7
  , testCase "4S0FoldNestedR2Dummy7" testSin0FoldNestedR2Dummy7
  , testCase "4S0FoldNestedR2Tan" testSin0FoldNestedR2Tan
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
  , testCase "4S0revhV4" testSin0revhV4
  , testCase "4S0revhV5" testSin0revhV5
  , testCase "4S0revhV6" testSin0revhV6
  , testCase "4S0revhV7" testSin0revhV7
  ]

foo :: RealFloatF a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

fooRrev :: forall g a.
           (ADReady g, GoodScalar a, Differentiable a, ADTensorScalar a ~ a)
        => (a, a, a) -> (g (TKR 0 a), g (TKR 0 a), g (TKR 0 a))
fooRrev (x, y, z) =
  let fHVector :: forall f. ADReady f => f (TKProduct (TKProduct (TKR 0 a) (TKR 0 a)) (TKR 0 a)) -> f (TKR 0 a)
      fHVector v = foo (tproject1 (tproject1 v), tproject2 (tproject1 v), tproject2 v)
      shapes = FTKProduct (FTKProduct (FTKR ZSR FTKScalar) (FTKR ZSR FTKScalar)) (FTKR ZSR FTKScalar)
      domsOf = rrev @g fHVector shapes
                    (tpair (tpair (rconcrete @g $ Nested.rscalar x)
                                  (rconcrete @g $ Nested.rscalar y))
                           (rconcrete @g $ Nested.rscalar z))
  in ( tlet domsOf (\v -> tproject1 (tproject1 v))
     , tlet domsOf (\v -> tproject2 (tproject1 v))
     , tlet domsOf (\v -> tproject2 v) )

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
    @?= "rfromS (let x11 = let x3 = sin (sscalar 2.2) ; x4 = sscalar 1.1 * x3 ; x5 = recip (sscalar 10.889999999999999 + x4 * x4) ; x6 = sin (sscalar 2.2) ; x9 = (sscalar (-3.3) * x5) * sscalar 1.0 in tpair (tpair (x3 * x9 + x6 * sscalar 3.3, cos (sscalar 2.2) * (sscalar 1.1 * x9) + cos (sscalar 2.2) * sscalar 3.63), (x4 * x5) * sscalar 1.0 + (sscalar 1.1 * x6) * sscalar 1.0) in tproject1 (tproject1 x11))"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstTensor AstMethodLet PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty (simplifyInlineContract a1)
    @?= "rfromS (tlet (sin (sscalar 2.2)) (\\x14 -> tlet (sscalar 1.1 * x14) (\\x15 -> x14 * ((sscalar (-3.3) * recip (sscalar 10.889999999999999 + x15 * x15)) * sscalar 1.0) + sin (sscalar 2.2) * sscalar 3.3)))"

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
    @?= "rfromS (negate (sin (sscalar 1.1)) * sscalar 1.0)"

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
    @?= "(\\x18 -> rfromS (sfromR (tproject1 x18) * cos (sfromR (tproject2 x18)))) (tpair (rdualPart (rfromS (sscalar 1.0)), (\\x14 -> rfromS (sfromR (tproject1 x14) * cos (sfromR (tproject2 x14)))) (tpair (rdualPart (rfromS (sscalar 1.0)), rdualPart (rfromS (sscalar 1.1))))))"

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
                            x0 (rrepl @_ @Double (0 :$: ZSR) 0)
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
                        x0 (rrepl @1 @Double [1] 42)) (rscalar 1.1))

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
    @?= "rsum (tproject2 (tmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [1] [Z0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sscalar 5.0) (sreplicate @_ @1 (sscalar 1.1)))), sreplicate @_ @1 (sscalar 1.1))))))"

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
                        x0 (rrepl @1 @Double [1] 42)
           in f) (rscalar 1.1))

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR 0 Double))
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @1 @Double [5] 42)) (rscalar 1.1))

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
    @?= "rfromS (let v5 = tmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sconcrete (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])) (tpair (sconcrete (sfromListLinear [1] [Z0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate @_ @5 (sscalar 1.1)) (sreplicate @_ @1 (sscalar 1.1)))), sreplicate @_ @1 (sscalar 1.1)))) in ssum @_ @5 (tproject1 v5) + ssum @_ @1 (tproject2 v5))"

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
                            x0 (rrepl @_ @Double (0 :$: ZSR) 0)
           in f) (rscalar 1.1))

testSin0Scan1 :: Assertion
testSin0Scan1 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR 5 Double))
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rrepl @1 @Double [1] 42))
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
                        x0 (rrepl @1 @Double [5] 42))
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
                           (rrepl @1 @Double [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 + tproject1 (tmapAccumRDer (SNat @2) (\\x7 -> tfromS (tpair (cos (sfromR (tproject1 (tproject2 (tproject2 x7)))) * (sscalar 0.0 + tproject1 x7 + tproject1 (tproject2 x7)), sscalar 0.0))) (\\x15 -> tfromS (tpair ((sfromR (tproject1 (tproject2 (tproject2 (tproject1 x15)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x15))))))) * (sscalar 0.0 + tproject1 (tproject2 (tproject2 x15)) + tproject1 (tproject2 x15)) + (tproject1 (tproject1 x15) + tproject1 (tproject2 (tproject1 x15))) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x15))))), sscalar 0.0))) (\\x25 -> tfromS (let x32 = let x30 = sscalar 0.0 + tproject1 (tproject1 x25) ; x31 = cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * x30 in tpair (x31, tpair (x31, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x25)))))) * ((sscalar 0.0 + tproject1 (tproject2 (tproject2 x25)) + tproject1 (tproject2 x25)) * x30), sscalar 0.0))) in tpair (tproject1 x32, tpair (tproject1 (tproject2 x32), tpair (tproject1 (tproject2 (tproject2 x32)), tproject2 (tproject2 (tproject2 x32))))))) (sscalar 0.0) (tpair (sconcrete (sfromListLinear [2] [1.0,1.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) (\\x34 -> tfromS (let x37 = sin (tproject1 x34) in tpair (x37, tpair (tproject1 x34, x37)))) (\\x40 -> tfromS (let x47 = tproject1 (tproject1 x40) * cos (tproject1 (tproject2 x40)) in tpair (x47, tpair (tproject1 (tproject1 x40), x47)))) (\\x50 -> tpair (cos (tproject1 (tproject2 x50)) * (sscalar 0.0 + tproject1 (tproject1 x50) + sfromR (tproject2 (tproject2 (tproject1 x50)))) + sfromR (tproject1 (tproject2 (tproject1 x50))), sscalar 0.0)) (sscalar 1.1) (sconcrete (sfromListLinear [2] [42.0,42.0])))), sconcrete (sfromListLinear [2] [42.0,42.0]))))))"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 + cos (sscalar 1.1) * (cos (sin (sscalar 1.1)) * sscalar 1.0) + cos (sscalar 1.1) * sscalar 1.0)"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @1 @Double [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sappend (sreplicate @_ @1 (sscalar 1.0)) (sfromR (tproject2 (tmapAccumLDer (SNat @2) (\\x8 -> tfromS (let x15 = tproject1 x8 * cos (sfromR (tproject1 (tproject2 (tproject2 x8)))) in tpair (x15, x15))) (\\x17 -> tfromS (let x24 = tproject1 (tproject1 x17) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))) + (sfromR (tproject1 (tproject2 (tproject2 (tproject1 x17)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x17))))))) * tproject1 (tproject2 x17) in tpair (x24, x24))) (\\x26 -> tfromS (let x32 = sscalar 0.0 + sfromR (tproject2 (tproject1 x26)) + tproject1 (tproject1 x26) in tpair (cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x26))))) * x32, tpair (sscalar 0.0, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x26)))))) * (tproject1 (tproject2 x26) * x32), sscalar 0.0))))) (sscalar 1.0) (tpair (sconcrete (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) (\\x43 -> tfromS (let x46 = sin (tproject1 x43) in tpair (x46, tpair (tproject1 x43, x46)))) (\\x49 -> tfromS (let x50 = tproject1 (tproject1 x49) * cos (tproject1 (tproject2 x49)) in tpair (x50, tpair (tproject1 (tproject1 x49), x50)))) (\\x53 -> tpair (cos (tproject1 (tproject2 x53)) * (sscalar 0.0 + tproject1 (tproject1 x53) + sfromR (tproject2 (tproject2 (tproject1 x53)))) + sfromR (tproject1 (tproject2 (tproject1 x53))), sscalar 0.0)) (sscalar 1.1) (sconcrete (sfromListLinear [2] [42.0,42.0])))), sconcrete (sfromListLinear [2] [42.0,42.0]))))))))"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @1 @Double [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineContract a1)
    @?= "(\\x1 -> rfromS (sappend (sreplicate @_ @1 (sfromR (tproject1 x1))) (sfromR (tproject2 (tmapAccumLDer (SNat @2) (\\x8 -> tfromS (let x15 = sfromR (tproject1 x8) * cos (sfromR (tproject1 (tproject2 (tproject2 x8)))) in tpair (x15, x15))) (\\x16 -> tfromS (let x23 = sfromR (tproject1 (tproject1 x16)) * cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x16))))) + (sfromR (tproject1 (tproject2 (tproject2 (tproject1 x16)))) * negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x16))))))) * sfromR (tproject1 (tproject2 x16)) in tpair (x23, x23))) (\\x24 -> tfromS (let x30 = sscalar 0.0 + sfromR (tproject2 (tproject1 x24)) + sfromR (tproject1 (tproject1 x24)) in tpair (cos (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x24))))) * x30, tpair (sscalar 0.0, tpair (negate (sin (sfromR (tproject1 (tproject2 (tproject2 (tproject2 x24)))))) * (sfromR (tproject1 (tproject2 x24)) * x30), sscalar 0.0))))) (tproject1 x1) (tpair (sconcrete (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) (\\x36 -> tfromS (let x39 = sin (sfromR (tproject1 x36)) in tpair (x39, tpair (tproject1 x36, x39)))) (\\x41 -> tfromS (let x42 = sfromR (tproject1 (tproject1 x41)) * cos (sfromR (tproject1 (tproject2 x41))) in tpair (x42, tpair (tproject1 (tproject1 x41), x42)))) (\\x44 -> tfromS (tpair (cos (sfromR (tproject1 (tproject2 x44))) * (sscalar 0.0 + sfromR (tproject1 (tproject1 x44)) + sfromR (tproject2 (tproject2 (tproject1 x44)))) + sfromR (tproject1 (tproject2 (tproject1 x44))), sscalar 0.0))) (tproject2 x1) (sconcrete (sfromListLinear [2] [42.0,42.0])))), sconcrete (sfromListLinear [2] [42.0,42.0]))))))))) (tfromS (tpair (sscalar 1.0, sscalar 1.1)))"
testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 + tproject1 (tmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sconcrete (sfromListLinear [2] [1.0,1.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.0,7.0])))), sconcrete (sfromListLinear [2] [5.0,7.0]))))))"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rscan @_ @(TKScalar Double) (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7])))
                 (FTKR ZSR FTKScalar)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v4 x1 -> rfromS (sfromR v4 !$ [0] + tproject1 (tmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sslice (sfromR v4), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> x1 (sconcrete (sfromListLinear [2] [5.0,7.0])))), sconcrete (sfromListLinear [2] [5.0,7.0]))))))"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - rscalar 5) - rscalar 7, sin x0 - rscalar 5, x0])
                 (FTKR ZSR FTKScalar)
  printArtifactPretty @_ @(TKR 1 Double) IM.empty (simplifyArtifact art)
    @?= "\\v3 x1 -> rfromS (cos (sfromR x1) * (cos (sscalar (-5.0) + sin (sfromR x1)) * sfromR v3 !$ [0]) + cos (sfromR x1) * sfromR v3 !$ [1] + sfromR v3 !$ [2])"

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
    @?= "rfromS (let v6 = tmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sconcrete (sfromListLinear [2] [1.0,1.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.5,7.700000000000001])))), sconcrete (sfromListLinear [2] [5.5,7.700000000000001])))) in sscalar 1.0 + sscalar 5.0 * tproject2 v6 !$ [0] + sscalar 7.0 * tproject2 v6 !$ [1] + tproject1 v6)"


testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * rscalar 5) - x0 * rscalar 7, sin x0 - x0 * rscalar 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (let x6 = cos (sscalar (-5.5) + sin (sscalar 1.1)) * sscalar 1.0 in sscalar (-11.0) + cos (sscalar 1.1) * x6 + sscalar (-5.0) * x6 + cos (sscalar 1.1) * sscalar 1.0)"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sappend (sreplicate @_ @1 (sscalar 1.0)) (sfromR (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [2] [5.0,7.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.5,7.700000000000001])))), sconcrete (sfromListLinear [2] [5.5,7.700000000000001]))))))))"

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
                      x0 (rrepl @_ @Double (0 :$: ZSR) 0)
     in f) (rscalar 1.1))

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 (rrepl @1 @Double [1] 42))
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
    @?= "rfromS (sgather (sconcrete (sfromListLinear [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1]))"

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
    @?= "rfromS (sgather (sfromVector (fromList [sreplicate @_ @1000000 (sreplicate @_ @1000000 (sreplicate @_ @200 (sreplicate @_ @300 (sreplicate @_ @600 (sscalar 0.0))))), sreplicate @_ @1000000 (sreplicate @_ @1000000 (sreplicate @_ @200 (sreplicate @_ @300 (sreplicate @_ @600 (sscalar 1.0)))))])) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6]))"

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
    @?= "rfromS (sgather (sfromVector (fromList [sreplicate @_ @1000000 (sreplicate @_ @1000000 (sreplicate @_ @200 (sreplicate @_ @300 (sreplicate @_ @600 (sscalar 0.0))))), sreplicate @_ @1000000 (sreplicate @_ @1000000 (sreplicate @_ @200 (sreplicate @_ @300 (sreplicate @_ @600 (sscalar 1.0)))))])) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4]))"

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = tproject1 $ tmapAccumR (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKS '[] Double)
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (srepl 0)
           in f) (srepl 1.1))

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = tproject1 $ tmapAccumL (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKS '[] Double)
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (srepl 0)
            in f) (srepl 1.1))

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = tproject1 $ tmapAccumL (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g TKUnit
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (treplicate (SNat @0) stkUnit tunit)
           in f) (srepl 1.1))

testSin0rmapAccumRD00S :: Assertion
testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 8.621412119476068e-2)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
              f x0 = tproject1 $ tmapAccumR (Proxy @f) (SNat @7)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g TKUnit
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (treplicate (SNat @7) stkUnit tunit)
           in f) (srepl 1.1))

testSin0rmapAccumRD00S7 :: Assertion
testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1.4091291405664697)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Double)
              f x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @7)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g TKUnit
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (treplicate (SNat @7) stkUnit tunit)
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[0] Z0)
               f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @0)
                          ftkUnit
                          ftkUnit
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g (TKS '[] Double)
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (srepl 0)
            in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Z0)
               f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @7)
                          ftkUnit
                          ftkUnit
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g (TKS '[] Double)
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (srepl 0)
            in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[0] Z0)
              f _x0 = tproject2 $ tmapAccumL (Proxy @f) (SNat @0)
                          ftkUnit
                          ftkUnit
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g (TKS '[] Double)
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (srepl 0)
            in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Z0)
              f _x0 = tproject2 $ tmapAccumL (Proxy @f) (SNat @7)
                          ftkUnit
                          ftkUnit
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g (TKS '[] Double)
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (srepl 0)
            in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[0] Z0)
               f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @0)
                          ftkUnit
                          ftkUnit
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g TKUnit
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (treplicate (SNat @0) stkUnit tunit)
            in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Z0)
               f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @7)
                          ftkUnit
                          ftkUnit
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g TKUnit
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (treplicate (SNat @7) stkUnit tunit)
            in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[0] Z0)
              f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @0)
                          ftkUnit
                          ftkUnit
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g TKUnit
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (treplicate (SNat @0) stkUnit tunit)
            in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[7] Z0)
              f _x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @7)
                          ftkUnit
                          ftkUnit
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g TKUnit -> g TKUnit
                                 -> g (TKProduct TKUnit TKUnit)
                               g x _a = tpair x tunit
                           in g)
                          tunit
                          (treplicate (SNat @7) stkUnit tunit)
            in f) (srepl 1.1))

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' (let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
               f x0 = tproject1 $ tmapAccumR (Proxy @f) (SNat @0)
                          (FTKR ZSR FTKScalar)
                          (FTKR ZSR FTKScalar)
                          (FTKR ZSR FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKR 0 Double) -> g (TKR 0 Double)
                                 -> g (TKProduct (TKR 0 Double) (TKR 0 Double))
                               g x _a = tpair (sin x) (sin x)
                           in g)
                          x0
                          (rrepl [0] 0)
            in f) (rscalar 1.1))

testSin0rmapAccumRD01SN :: Assertion
testSin0rmapAccumRD01SN = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[1] Double)
               f x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @1)
                          (FTKProduct (FTKS ZSS FTKScalar) (FTKS ZSS FTKScalar))
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKProduct (TKS '[] Double)
                                                 (TKS '[] Double))
                                 -> g (TKS '[] Double)
                                 -> g (TKProduct (TKProduct (TKS '[] Double)
                                                            (TKS '[] Double))
                                                 (TKS '[] Double))
                               g xh _a = let x = tproject2 xh
                                         in tpair (tpair (sin x) (sin x)) (sin x)
                           in g)
                          (tpair (srepl 3) x0)
                          (srepl 0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN3 :: Assertion
testSin0rmapAccumRD01SN3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[1, 3] Double)
               f x0 = tproject2 $ tmapAccumR (Proxy @f) (SNat @1)
                          (FTKS ZSS FTKScalar)
                          (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                          (FTKS (SNat @2 :$$ ZSS) FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double)
                                 -> g (TKS '[2] Double)
                                 -> g (TKProduct (TKS '[] Double)
                                                 (TKS '[3] Double))
                               g x _a = tpair (sin x)
                                              (sreplicate @_ @3 (sin x / srepl 3))
                           in g)
                          x0
                          (srepl 0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN5 :: Assertion
testSin0rmapAccumRD01SN5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[1, 3] Double)
               f x0 = tproject2 $ tproject2 $ tmapAccumR (Proxy @f) (SNat @1)
                          (FTKS ZSS FTKScalar)
                          (FTKProduct (FTKS (SNat @3 :$$ ZSS) FTKScalar) (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (FTKProduct (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @2 :$$ ZSS) FTKScalar))
                                      (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @2 :$$ ZSS) FTKScalar)))
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double)
                                 -> g (TKProduct (TKProduct (TKS '[2] Double)
                                                            (TKS '[2] Double))
                                                 (TKProduct (TKS '[2] Double)
                                                            (TKS '[2] Double)))
                                 -> g (TKProduct (TKS '[] Double)
                                                 (TKProduct (TKS '[3] Double)
                                                            (TKS '[3] Double)))
                               g x a =
                                 tpair (sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (tproject2 $ tproject1 a))
                                   (tpair (sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                       (tproject1 $ tproject2 a) [1]
                                              / sin x / srepl 3))
                                          (sreplicate @_ @3
                                             (ssum @_ @2 (tproject2 $ tproject1 a)
                                              + sin x / srepl 3)))
                           in g)
                          x0
                          (tpair (tpair (srepl 0) (srepl 0))
                                 (tpair (srepl 0) (srepl 0)))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN51 :: Assertion
testSin0rmapAccumRD01SN51 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-69.90586521651421))
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[] Double)
               f x0 = (\res -> ssum @_ @6 (tproject1 $ tproject1 res)
                               + ssum0 @_ @_ @'[6, 5, 4, 3]
                                   (tproject2 res))
                      $ tbuild1 @f (SNat @6) knownSTK $ \j ->
                         tmapAccumR (Proxy @f) (SNat @5)
                          (FTKProduct (FTKS ZSS FTKScalar)
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (FTKS (SNat @4 :$$ SNat @3 :$$ ZSS) FTKScalar)
                          (FTKProduct (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                                      (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @2 :$$ ZSS) FTKScalar)))
                          (let g :: forall g. ADReady g
                                 => g (TKProduct (TKS '[] Double)
                                                 (TKS '[3] Double))
                                 -> g (TKProduct (TKProduct (TKS '[2] Double)
                                                            (TKS '[3] Double))
                                                 (TKProduct (TKS '[2] Double)
                                                            (TKS '[2] Double)))
                                 -> g (TKProduct (TKProduct (TKS '[] Double)
                                                            (TKS '[3] Double))
                                                 (TKS '[4, 3] Double))
                               g xh a =
                                 let x = tproject1 xh
                                     x1 = tproject2 xh
                                 in tpair (tpair
                                            (sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (tproject2 $ tproject2 a))
                                            (sreplicate @_ @3
                                             (sindex0 @_ @'[2]
                                                       (tproject1 $ tproject2 a) [1]
                                              / sin x / srepl 3)))
                                         (sbuild1 @_ @4 $ \i ->
                                             (tproject2 $ tproject1 a)
                                             - sin x1 / sreplicate @_ @3
                                                     (srepl 1 + sfromIndex0 i))
                           in g)
                          (tpair (x0 / (srepl 1 + sfromIndex0 j))
                                 (sreplicate @_ @3 x0))
                          (tpair (tpair (srepl 1) (sreplicate0N @_ @_ @'[5, 3]
                                               (sfromIndex0 j)))
                                 (tpair (srepl 3) (srepl 4)))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531a :: Assertion
testSin0rmapAccumRD01SN531a = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3]
       [1.8478609886246988,-22.194216099801963,-40.72162125038692])
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[3] Double) -> f (TKS '[2, 2, 2, 3] Double)
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (tproject1 $ tproject1 res)
                               - (tproject2 res))
                      $ tbuild1 @f (SNat @2) knownSTK $ \i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \j ->
                         tmapAccumR (Proxy @f) (SNat @2)
                          (FTKProduct (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                                      (FTKS (SNat @6 :$$ ZSS) FTKScalar))
                          (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                          (FTKProduct (FTKS (SNat @1 :$$ ZSS) FTKScalar)
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (let g :: forall g. ADReady g
                                 => g (TKProduct (TKS '[3] Double)
                                                 (TKS '[6] Double))
                                 -> g (TKProduct (TKS '[1] Double)
                                                 (TKS '[3] Double))
                                 -> g (TKProduct (TKProduct (TKS '[3] Double)
                                                            (TKS '[6] Double))
                                                 (TKS '[3] Double))
                               g xh a =
                                 let x = tproject1 xh
                                     x2 = tproject2 xh
                                 in tpair (tpair
                                            (sfromList
                                             [srepl 0.01, ssum @_ @6 x2, srepl 0.3]
                                           - sin x - (tproject2 a))
                                            (srepl 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - (tproject2 a)))))
                                         (srepl 1 - sreplicate @_ @3
                                             (ssum @_ @1 (tproject1 a))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @'[3]
                                                       (tproject2 a) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)))
                           in g)
                          (tpair (x0 / (srepl 1 + sreplicate @_ @3 (sfromIndex0 j)))
                                 (sreplicate @_ @6 (sfromIndex0 i)
                                          - sflatten (sappend x0 x0)))
                          (tpair (sfromList [srepl (-0.1), sreshape @_ @_ @'[] @'[1] $ sfromIndex0 j])
                                 ((sfromListLinear
                                           [sscalar 0.4, sscalar (-0.01), sscalar (-0.3), sfromIndex0 i, sscalar 0.5, sscalar 1.3]))))
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531b0 :: Assertion
testSin0rmapAccumRD01SN531b0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKR 0 Double)
                 -> f (TKR 2 Double)
               f x0 = rfromS $ tproject1
                      $ tbuild1 @f (SNat @2) knownSTK $ \_i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \_j ->
                         tmapAccumR (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (FTKR ZSR FTKScalar)
                          (let h :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKR 0 Double)
                                 -> g (TKProduct (TKS '[] Double) TKUnit)
                               h xh _a = tpair xh tunit
                           in h)
                          (sfromR x0)
                          (rconcrete $ Nested.rfromListPrimLinear [0] []))
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SN531b0PP :: Assertion
testSin0rmapAccumRD01SN531b0PP = do
  resetVarCounter
  let f :: forall f. ADReady f
                 => f (TKR 0 Double)
                 -> f (TKR 2 Double)
      f x0 = rfromS $ tproject1
                      $ tbuild1 @f (SNat @2) knownSTK $ \_i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \_j ->
                         tmapAccumR (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (FTKR ZSR FTKScalar)
                          (let h :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKR 0 Double)
                                 -> g (TKProduct (TKS '[] Double) TKUnit)
                               h xh _a = tpair xh tunit
                           in h)
                          (sfromR x0)
                          (rconcrete $ Nested.rfromListPrimLinear [0] []))
  printAstPrettyButNested
    IM.empty
    (simplifyInlineContract
     $ f @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1))
    @?= "rfromS (sreplicate @_ @2 (sreplicate @_ @2 (tproject1 (tmapAccumRDer (SNat @0) (\\x7 -> tpair (tproject1 x7, Z0)) (\\x8 -> tpair (tproject1 (tproject1 x8), Z0)) (\\x11 -> tpair (tproject1 (tproject1 x11), sscalar 0.0)) (sscalar 1.1) (sconcrete (sfromListLinear [0] []))))))"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f (TKR 0 Double) -> f (TKR 2 Double)
      f x0 = tlet (
                       (tbuild1 @f (SNat @2) knownSTK $ \i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \j ->
                       (tmapAccumR (Proxy @f) (SNat @0)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          (FTKR ZSR FTKScalar)
                          (let h :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKR 0 Double)
                                 -> g (TKProduct (TKS '[] Double) TKUnit)
                               h xh _a = tpair xh tunit
                           in h)
                          (sfromIndex0 (i + j) + sfromR x0)
                          (rconcrete $ Nested.rfromListPrimLinear [0] [])))))
                        $ \ !d -> rfromS $ tproject1 d
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ f @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1))
    @?= "rfromS (tproject1 (tmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 1.1)) + sfromIntegral (str (sreplicate @_ @2 (siota (SNat @2))) + sreplicate @_ @2 (siota (SNat @2)))) (stranspose @_ @[2,0,1] (sreplicate @_ @2 (sreplicate @_ @2 (sconcrete (sfromListLinear [0] [])))))))"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f (TKR 0 Double) -> f (TKR 2 Double)
      f x0 = tlet (
                       (tbuild1 @f (SNat @2) knownSTK $ \i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \j ->
                       (tmapAccumR (Proxy @f) (SNat @1)
                          (FTKR ZSR FTKScalar)
                          ftkUnit
                          (FTKR ZSR FTKScalar)
                          (let h :: forall g. ADReady g
                                 => g (TKR 0 Double) -> g (TKR 0 Double)
                                 -> g (TKProduct (TKR 0 Double) TKUnit)
                               h xh _a = tpair xh tunit
                           in h)
                          (rfromIndex0 (i + j) + x0)
                          (rconcrete $ Nested.rfromListPrimLinear [0] [])))))
                        $ \ !d -> tproject1 d
  printAstPretty
    IM.empty
    (simplifyInlineContract
     $ f @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1))
    @?= "rfromS (tproject1 (tmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate @_ @2 (sreplicate @_ @2 (sscalar 1.1)) + sfromIntegral (str (sreplicate @_ @2 (siota (SNat @2))) + sreplicate @_ @2 (siota (SNat @2)))) (stranspose @_ @[2,0,1] (sreplicate @_ @2 (sreplicate @_ @2 (sconcrete (sfromListLinear [0] [])))))))"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-1.8866871148429984))
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[2, 2, 2] Double)
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (tproject1 res)
                               - tproject2 res)
                      $ tbuild1 @f (SNat @2) knownSTK $ \i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \j ->
                       (tmapAccumR (Proxy @f) (SNat @2)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g (TKS '[] Double)
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x a =
                                tpair (sin x - a)
                                      (srepl 1 - sin x / srepl 3 - a)
                           in g)
                          (x0 / (srepl 1 + sfromIndex0 j))
                          (sfromListLinear [sscalar 0.4, sfromIndex0 i])))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531Slice :: Assertion
testSin0rmapAccumRD01SN531Slice = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[2, 2] Double)
               f x0 = tproject1
                      $ tbuild1 @f (SNat @2) knownSTK $ \_i ->
                       (tbuild1 @f (SNat @2) knownSTK $ \_j ->
                       (tmapAccumR (Proxy @f) (SNat @1)
                          (FTKS ZSS FTKScalar)
                          ftkUnit
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double) -> g TKUnit
                                 -> g (TKProduct (TKS '[] Double) TKUnit)
                               g x _a =
                                tpair x tunit
                           in g)
                          x0
                          (treplicate (SNat @1) stkUnit tunit)))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN55 :: Assertion
testSin0rmapAccumRD01SN55 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4.1200926532396815)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[5, 3] Double)
               f x0 = (\res -> sreplicate @_ @5 (tproject1 res)
                               * (tproject1 $ tproject2 res)
                               + (tproject2 $ tproject2 res))
                      $ tmapAccumL (Proxy @f) (SNat @5)
                          (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                          (FTKProduct (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          ftkUnit
                          (let g :: forall g. ADReady g
                                 => g (TKS '[3] Double)
                                 -> g TKUnit
                                 -> g (TKProduct (TKS '[3] Double)
                                                 (TKProduct (TKS '[3] Double)
                                                            (TKS '[3] Double)))
                               g x _a =
                                 tpair (sin x - x)
                                       (tpair (sreplicate @_ @3
                                             (sindex0 @_ @'[3] x [1]
                                              - smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (x / sin x / srepl 3)))
                                          (sreplicate @_ @3
                                             (ssum @_ @3 x)
                                           + sin x / srepl 3))
                           in g)
                          (sreplicate @_ @3 x0)
                          (treplicate (SNat @5) stkUnit tunit)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN55acc :: Assertion
testSin0rmapAccumRD01SN55acc = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3] [-21.0,-42.0,-21.0])
    (rev' (let f :: forall f. ADReady f
                 => f (TKS '[3] Double) -> f (TKS '[2, 3] Double)
               f x0 = (\res -> srepl 2 - str (sreplicate @_ @3
                                         $ ssum @_ @7
                                         $ str (tproject2 $ tproject1 $ tproject2 res))
                               - (tproject2 $ tproject2 res))
                      $ tmapAccumR (Proxy @f) (SNat @2)
                          ftkUnit
                          (FTKProduct (FTKProduct (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                                                  (FTKS (SNat @7 :$$ ZSS) FTKScalar))
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (FTKProduct (FTKS (SNat @1 :$$ ZSS) FTKScalar)
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (let g :: forall g. ADReady g
                                 => g TKUnit
                                 -> g (TKProduct (TKS '[1] Double)
                                                 (TKS '[3] Double))
                                 -> g (TKProduct TKUnit
                                         (TKProduct (TKProduct (TKS '[3] Double)
                                                              (TKS '[7] Double))
                                                    (TKS '[3] Double)))
                               g _xh a =
                                let x = sreplicate @g @3 (sscalar 2)
                                in tpair tunit
                                     (tpair
                                        (tpair
                                           (singestData [0.1, 0.2, 0.3]
                                            - sin x - tproject2 a)
                                           (srepl 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - tproject2 a)))
                                        (sreplicate0N (sscalar 1)
                                         - sreplicate @_ @3
                                             (ssum @_ @1 (tproject1 a))
                                           - sin x / sreplicate0N (sscalar 3)
                                           - sreplicate @_ @3
                                             (sindex0 @_ @'[3]
                                                       (tproject2 a) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / sreplicate0N (sscalar 3)))))
                           in g)
                          tunit
                          (tpair (singestData [-0.1, 0.23])
                                 (sfromListLinear
                                    [sindex0 x0 [1], sscalar (-0.01), sscalar (-0.3), ssum x0, sscalar 0.5, sscalar 1.3]))
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
    (cfwd (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKS '[5] Double)
               f x0 = tproject2
                      $ tmapAccumR (Proxy @f) (SNat @5)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (FTKS ZSS FTKScalar)
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double)
                                 -> g (TKS '[] Double)
                                 -> g (TKProduct (TKS '[] Double) (TKS '[] Double))
                               g x _a =
                                 tpair (sscalar 1) x
                           in g)
                          x0
                          (srepl 0)
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev (let f :: forall f. ADReady f
                 => f (TKS '[] Double) -> f (TKProduct (TKS '[] Double)
                                                 (TKProduct (TKS '[1, 3] Double)
                                                            (TKS '[1, 3] Double)))
               f x0 = tmapAccumR (Proxy @f) (SNat @1)
                          (FTKS ZSS FTKScalar)
                          (FTKProduct (FTKS (SNat @3 :$$ ZSS) FTKScalar)
                                      (FTKS (SNat @3 :$$ ZSS) FTKScalar))
                          (FTKProduct (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @2 :$$ ZSS) FTKScalar))
                                      (FTKProduct (FTKS (SNat @2 :$$ ZSS) FTKScalar) (FTKS (SNat @2 :$$ ZSS) FTKScalar)))
                          (let g :: forall g. ADReady g
                                 => g (TKS '[] Double)
                                 -> g (TKProduct (TKProduct (TKS '[2] Double)
                                                            (TKS '[2] Double))
                                                 (TKProduct (TKS '[2] Double)
                                                            (TKS '[2] Double)))
                                 -> g (TKProduct (TKS '[] Double)
                                                 (TKProduct (TKS '[3] Double)
                                                            (TKS '[3] Double)))
                               g x a =
                                  tpair (sin x
                                           ** smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (tproject2 $ tproject1 a))
                                    (tpair (sreplicate @_ @3
                                             (sin x / srepl 6
                                              + sindex0 @_ @'[2]
                                                        (tproject1 $ tproject2 a) [1]
                                                / sin x / srepl 3))
                                       (sreplicate @_ @3
                                             (ssum @_ @2 (tproject2 $ tproject1 a)
                                              + sin x / srepl 6)))
                           in g)
                          x0
                          (tpair
                             (tpair (sreplicate0N $ sscalar 0)
                                    (sreplicate0N $ sscalar 0))
                             (tpair (sreplicate0N $ sscalar 0)
                                    (sreplicate0N $ sscalar 0)))
           in f @(ADVal RepN)) (sscalar 1.1))

rscanZip :: forall rn n rn2 n2 target.
            (GoodScalar rn, KnownNat n, GoodScalar rn2, ADReady target)
         => (forall f. ADReady f => f (TKR n rn) -> f (TKR n2 rn2) -> f (TKR n rn))
         -> FullTensorKind (TKR n2 rn2)
         -> target (TKR n rn)
         -> target (TKR (1 + n2) rn2)
         -> target (TKR (1 + n) rn)
rscanZip f eShs acc0 es =
  let width = rlength es
      ftk = tftk knownSTK acc0
  in withSNat width $ \snat ->
    tlet
      (tmapAccumL Proxy snat ftk ftk eShs
         (let g :: forall f. ADReady f
                => f (TKR n rn) -> f (TKR n2 rn2)
                -> f (TKProduct (TKR n rn) (TKR n rn))
              g acc e = tlet (f acc e) (\res -> tpair res res)
          in g)
         acc0 es)
      (\res -> rappend (rfromList [acc0]) (tproject2 res))

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
       (\a0 -> tproject2
               $ tmapAccumR Proxy (SNat @4)
                   (FTKR (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR) FTKScalar)
                   (FTKR (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR) FTKScalar)
                   (FTKR (1 :$: 1 :$: 1 :$: ZSR) FTKScalar)
                   (let g :: forall g. ADReady g
                          => g (TKR 5 Double) -> g (TKR 3 Double)
                          -> g (TKProduct (TKR 5 Double) (TKR 5 Double))
                        g x a =
                          tpair (rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                                x
                    in g)
                      (rreplicate 2 (rreplicate 5
                                      (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                      (rreplicate 4 a0))
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
                           x0 (rrepl @1 @Double [2] 42)) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 + tproject1 (tmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sconcrete (sfromListLinear [2] [1.0,1.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [42.0,42.0])))), sconcrete (sfromListLinear [2] [42.0,42.0]))))))"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (FTKR ZSR FTKScalar)
                           x0 (rrepl @1 @Double [2] 42)) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sappend (sreplicate @_ @1 (sscalar 1.0)) (sfromR (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [42.0,42.0])))), sconcrete (sfromListLinear [2] [42.0,42.0]))))))))"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                         (FTKR ZSR FTKScalar)
                         x0 (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sscalar 1.0 + tproject1 (tmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 0.0) (tpair (sconcrete (sfromListLinear [2] [1.0,1.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.0,7.0])))), sconcrete (sfromListLinear [2] [5.0,7.0]))))))"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                         (FTKR ZSR FTKScalar)
                         x0 (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sappend (sreplicate @_ @1 (sscalar 1.0)) (sfromR (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [2] [0.0,0.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.0,7.0])))), sconcrete (sfromListLinear [2] [5.0,7.0]))))))))"


testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - a)
                                (FTKR ZSR FTKScalar)
                                x0 (rfromList [x0 * rscalar 5, x0 * rscalar 7]))
                 (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineContract a1)
    @?= "rfromS (sappend (sreplicate @_ @1 (sscalar 1.0)) (sfromR (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [2] [5.0,7.0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> (sscalar 1.1) (sconcrete (sfromListLinear [2] [5.5,7.700000000000001])))), sconcrete (sfromListLinear [2] [5.5,7.700000000000001]))))))))"

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (FTKR ZSR FTKScalar)
                   x0 (rrepl @1 @Double [1] 42))
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
       (\a0 -> rreverse $ tproject2
               $ tmapAccumR Proxy (SNat @4)
                   (FTKR (2 :$: 5 :$: ZSR) FTKScalar)
                   (FTKR (2 :$: 5 :$: ZSR) FTKScalar)
                   (FTKR ZSR FTKScalar)
                   (let g :: forall g. ADReady g
                          => g (TKR 2 Double) -> g (TKR 0 Double)
                          -> g (TKProduct (TKR 2 Double) (TKR 2 Double))
                        g x a =
                         tpair (rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                               x
                    in g)
                      (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                      (rreplicate 4 a0)) (rscalar 1.1))

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
      g :: forall f. ADReady f => f (TKS '[] Double) -> f (TKS '[] Double)
      g x = srev f (FTKS ZSS FTKScalar) x
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) ((sscalar 1.1)))
    @?= "let v5 = tmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [11] [Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.1) (sreplicate @_ @11 (sscalar 1.1)))), sreplicate @_ @11 (sscalar 1.1)))) in ssum @_ @11 (tproject2 v5) + tproject1 v5"

testSin0FoldNestedR1PP :: Assertion
testSin0FoldNestedR1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1))
    @?= "rfromS (let v5 = tmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.0) (tpair (sconcrete (sfromListLinear [11] [Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0,Z0]), tpair (tproject1 (tproject2 (tmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> (sscalar 1.1) (sreplicate @_ @11 (sscalar 1.1)))), sreplicate @_ @11 (sscalar 1.1)))) in ssum @_ @11 (sfromR (tproject2 v5)) + tproject1 v5)"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
      IM.empty
      (simplifyInlineContract
       $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
    @?= 2358

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
      IM.empty
      (simplifyInlineContract
       $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
    @?= 26946

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
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
    @?= 351702

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
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
    @?= 5277459

-- Takes 70s, probably due to something (simplification?) forcing all derivs.
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
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
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
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
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
      g :: forall f. ADReady f => f (TKR 0 Double) -> f (TKR 0 Double)
      g x = rrev f (FTKR ZSR FTKScalar) x
  length
    (printAstSimple
       IM.empty
       (simplifyInlineContract
        $ g @(AstTensor AstMethodLet PrimalSpan) (rscalar 1.1)))
    @?= 116880

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
                                                   (sslice (SNat @0) (SNat @1) SNat x))))
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
    @?= 52779

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. BaseTensor g
        => g (TKR 0 Double) -> g (TKR 0 Double)
      f x = rrev @g @_ @(TKScalar Double) @0 sin (FTKR ZSR FTKScalar) x
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.4535961214255773)
    (f @RepN (rscalar 1.1))

testSin0revhVPP :: Assertion
testSin0revhVPP = do
  resetVarCounter
  let f :: forall g. BaseTensor g
        => g (TKR 0 Double) -> g (TKR 0 Double)
      f x = rrev @g @_ @(TKScalar Double) @0 sin (FTKR ZSR FTKScalar) x
  printAstSimple IM.empty (f @(AstTensor AstMethodLet PrimalSpan)
                                    (rscalar 1.1))
    @?= "rfromS (cos (sscalar 1.1) * sscalar 1.0)"

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
                doms3 x (singestData @'[4] [1, 2, 3, 4])
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
                doms3 x (singestData @'[4] [1, 2, 3, 4])
  assertEqualUpToEpsilon 1e-10
    (singestData @'[3] [4.0,6.0,8.0])
    (crev f (sreplicate @_ @3 (sscalar 1.1)))
