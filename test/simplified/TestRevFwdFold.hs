{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Util.ShapedList (pattern (:.$), pattern ZIS)

import CrossTesting
import EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ testCase "4fooRrev" testFooRrev
  , testCase "4fooRrev2" testFooRrev2
  , testCase "4fooRrevPP1" testFooRrevPP1
--  , testCase "4fooRrevPP2" testFooRrevPP2
  , testCase "4fooRrev3" testFooRrev3
  , testCase "4Sin0Rrev" testSin0Rrev
  , testCase "4Sin0RrevPP1" testSin0RrevPP1
  , testCase "4Sin0RrevPP2" testSin0RrevPP2
  , testCase "4Sin0Rrev3" testSin0Rrev3
  , testCase "4Sin0Rrev4" testSin0Rrev4
  , testCase "4Sin0RrevPP4" testSin0RrevPP4
  , testCase "4Sin0Rrev5" testSin0Rrev5
  , testCase "4Sin0RrevPP5" testSin0RrevPP5
  , testCase "4Sin0Rrev3'" testSin0Rrev3'
  , testCase "4Sin0Rrev4'" testSin0Rrev4'
  , testCase "4Sin0Rrev5'" testSin0Rrev5'
  , testCase "4Sin0Rfwd" testSin0Rfwd
  , testCase "4Sin0RfwdPP1" testSin0RfwdPP1
  , testCase "4Sin0RfwdPP1FullUnsimp" testSin0RfwdPP1FullUnsimp
  , testCase "4Sin0RfwdPP1Full" testSin0RfwdPP1Full
  , testCase "4Sin0Rfwd3" testSin0Rfwd3
  , testCase "4Sin0Rfwd4" testSin0Rfwd4
  , testCase "4Sin0RfwdPP4" testSin0RfwdPP4
--  , testCase "4Sin0RfwdPP4Dual" testSin0RfwdPP4Dual
  , testCase "4Sin0Rfwd5" testSin0Rfwd5
  , testCase "4Sin0RfwdPP5" testSin0RfwdPP5
  , testCase "4Sin0Rfwd3'" testSin0Rfwd3'
  , testCase "4Sin0Rfwd4'" testSin0Rfwd4'
  , testCase "4Sin0Rfwd5'" testSin0Rfwd5'
  , testCase "4Sin0Rrev5S" testSin0Rrev5S
  , testCase "4Sin0RrevPP5S" testSin0RrevPP5S
  , testCase "4Sin0Fold0" testSin0Fold0
  , testCase "4Sin0Fold0ForComparison" testSin0Fold0ForComparison
  , testCase "4Sin0Fold1" testSin0Fold1
  , testCase "4Sin0Fold2" testSin0Fold2
  , testCase "4Sin0FoldForComparison" testSin0FoldForComparison
  , testCase "4Sin0Fold3" testSin0Fold3
  , testCase "4Sin0Fold4" testSin0Fold4
  , testCase "4Sin0Fold5" testSin0Fold5
  , testCase "4Sin0Fold6" testSin0Fold6
  , testCase "4Sin0Fold7" testSin0Fold7
  , testCase "4Sin0Fold8" testSin0Fold8
  , testCase "4Sin0Fold0S" testSin0Fold0S
  , testCase "4Sin0Fold1S" testSin0Fold1S
  , testCase "4Sin0Fold2S" testSin0Fold2S
  , testCase "4Sin0FoldForComparisonS" testSin0FoldForComparisonS
  , testCase "4Sin0Fold3S" testSin0Fold3S
  , testCase "4Sin0Fold4S" testSin0Fold4S
  , testCase "4Sin0Fold5S" testSin0Fold5S
  , testCase "4Sin0Fold6S" testSin0Fold6S
  , testCase "4Sin0Fold7S" testSin0Fold7S
  , testCase "4Sin0Fold8S" testSin0Fold8S
  , testCase "4Sin0Fold8rev" testSin0Fold8rev
  , testCase "4Sin0Fold8rev2" testSin0Fold8rev2
  , testCase "4Sin0Fold8Srev" testSin0Fold8Srev
  , testCase "4Sin0Fold8Srev2" testSin0Fold8Srev2
  , testCase "4Sin0Fold182SrevPP" testSin0Fold182SrevPP
  , testCase "4Sin0Fold18Srev" testSin0Fold18Srev
  , testCase "4Sin0Fold8fwd" testSin0Fold8fwd
  , testCase "4Sin0Fold8fwd2" testSin0Fold8fwd2
  , testCase "4Sin0Fold8Sfwd" testSin0Fold8Sfwd
  , testCase "4Sin0Fold8Sfwd2" testSin0Fold8Sfwd2
  , testCase "4Sin0Fold5Sfwd" testSin0Fold5Sfwd
  , testCase "4Sin0Fold5Sfwds" testSin0Fold5Sfwds
  , testCase "4Sin0Scan0" testSin0Scan0
  , testCase "4Sin0Scan1" testSin0Scan1
  , testCase "4Sin0Scan1ForComparison" testSin0Scan1ForComparison
  , testCase "4Sin0Scan2" testSin0Scan2
  , testCase "4Sin0Scan3" testSin0Scan3
  , testCase "4Sin0Scan4" testSin0Scan4
  , testCase "4Sin0Scan5" testSin0Scan5
  , testCase "4Sin0Scan6" testSin0Scan6
  , testCase "4Sin0Scan7" testSin0Scan7
  , testCase "4Sin0Scan8" testSin0Scan8
  , testCase "4Sin0Scan8rev" testSin0Scan8rev
  , testCase "4Sin0Scan8rev2" testSin0Scan8rev2
  , testCase "4Sin0Scan1RevPP1" testSin0Scan1RevPP1
  , testCase "4Sin0Scan1RevPPForComparison" testSin0Scan1RevPPForComparison
  , testCase "4Sin0ScanFwdPP" testSin0ScanFwdPP
  , testCase "4Sin0ScanFwdPPFull" testSin0ScanFwdPPFull
  , testCase "4Sin0Scan1Rev2PP1" testSin0Scan1Rev2PP1
  , testCase "4Sin0Scan1Rev2PPA" testSin0Scan1Rev2PPA
  , testCase "4Sin0Scan1Rev2PPForComparison" testSin0Scan1Rev2PPForComparison
  , testCase "4Sin0Scan1Fwd2PP" testSin0Scan1Fwd2PP
  , testCase "4Sin0Scan1Rev2" testSin0Scan1Rev2
  , testCase "4Sin0Scan1Rev2ForComparison" testSin0Scan1Rev2ForComparison
  , testCase "4Sin0Scan1Rev3PP" testSin0Scan1Rev3PP
  , testCase "4Sin0Scan1Rev3PPForComparison" testSin0Scan1Rev3PPForComparison
  , testCase "4Sin0ScanFwd3PP" testSin0ScanFwd3PP
  , testCase "4Sin0Scan1Rev3" testSin0Scan1Rev3
  , testCase "4Sin0Scan1Rev3ForComparison" testSin0Scan1Rev3ForComparison
  , testCase "4Sin0Scan0fwd" testSin0Scan0fwd
  , testCase "4Sin0Scan1fwd" testSin0Scan1fwd
  , testCase "4Sin0Scan1FwdForComparison" testSin0Scan1FwdForComparison
  , testCase "4Sin0Scan8fwd" testSin0Scan8fwd
  , testCase "4Sin0Scan8fwd2" testSin0Scan8fwd2
  , testCase "4SinUnitriangular0PP" testUnitriangular0PP
  , testCase "4SinUnitriangular1PP" testUnitriangular1PP
  , testCase "4SinUnitriangular2PP" testUnitriangular2PP
  , testCase "4Sin0ScanD0" testSin0ScanD0
  , testCase "4Sin0rmapAccumRD0SC" testSin0rmapAccumRD0SC
  , testCase "4Sin0rmapAccumRD0S" testSin0rmapAccumRD0S
  , testCase "4Sin0rmapAccumRD00SC" testSin0rmapAccumRD00SC
  , testCase "4Sin0rmapAccumRD00S0" testSin0rmapAccumRD00S0
--  , testCase "4Sin0rmapAccumRD00S" testSin0rmapAccumRD00S
--  , testCase "4Sin0rmapAccumRD00S7" testSin0rmapAccumRD00S7
  , testCase "4Sin0rmapAccumRD00SCacc0" testSin0rmapAccumRD00SCacc0
  , testCase "4Sin0rmapAccumRD00SCacc" testSin0rmapAccumRD00SCacc
  , testCase "4Sin0rmapAccumRD00Sacc0" testSin0rmapAccumRD00Sacc0
  , testCase "4Sin0rmapAccumRD00Sacc" testSin0rmapAccumRD00Sacc
  , testCase "4Sin0rmapAccumRD00SCall0" testSin0rmapAccumRD00SCall0
  , testCase "4Sin0rmapAccumRD00SCall" testSin0rmapAccumRD00SCall
  , testCase "4Sin0rmapAccumRD00Sall0" testSin0rmapAccumRD00Sall0
  , testCase "4Sin0rmapAccumRD00Sall" testSin0rmapAccumRD00Sall
  , testCase "4Sin0rmapAccumRD0RC" testSin0rmapAccumRD0RC
  , testCase "4Sin0rmapAccumRD0R" testSin0rmapAccumRD0R
  , testCase "4Sin0ScanD01" testSin0ScanD01
  , testCase "4Sin0rmapAccumRD01SC" testSin0rmapAccumRD01SC
  , testCase "4Sin0rmapAccumRD01SN" testSin0rmapAccumRD01SN
  , testCase "4Sin0rmapAccumRD01SN2" testSin0rmapAccumRD01SN2
  , testCase "4Sin0rmapAccumRD01SN3" testSin0rmapAccumRD01SN3
  , testCase "4Sin0rmapAccumRD01SN4" testSin0rmapAccumRD01SN4
  , testCase "4Sin0rmapAccumRD01SN51" testSin0rmapAccumRD01SN51
  , testCase "4Sin0rmapAccumRD01SN52" testSin0rmapAccumRD01SN52
  , testCase "4Sin0rmapAccumRD01SN53" testSin0rmapAccumRD01SN53
  , testCase "4Sin0rmapAccumRD01SN531" testSin0rmapAccumRD01SN531
  , testCase "4Sin0rmapAccumRD01SN531a" testSin0rmapAccumRD01SN531a
  , testCase "4Sin0rmapAccumRD01SN531b0" testSin0rmapAccumRD01SN531b0
  , testCase "4Sin0rmapAccumRD01SN531bS" testSin0rmapAccumRD01SN531bS
  , testCase "4Sin0rmapAccumRD01SN531bR" testSin0rmapAccumRD01SN531bR
  , testCase "4Sin0rmapAccumRD01SN531b0PP" testSin0rmapAccumRD01SN531b0PP
  , testCase "4Sin0rmapAccumRD01SN531bSPP" testSin0rmapAccumRD01SN531bSPP
  , testCase "4Sin0rmapAccumRD01SN531bSPPFull" testSin0rmapAccumRD01SN531bSPPFull
  , testCase "4Sin0rmapAccumRD01SN531bRPP" testSin0rmapAccumRD01SN531bRPP
  , testCase "4Sin0rmapAccumRD01SN531b0PPj" testSin0rmapAccumRD01SN531b0PPj
  , testCase "4Sin0rmapAccumRD01SN531bSPPj" testSin0rmapAccumRD01SN531bSPPj
  , testCase "4Sin0rmapAccumRD01SN531bRPPj" testSin0rmapAccumRD01SN531bRPPj
  , testCase "4Sin0rmapAccumRD01SN531c" testSin0rmapAccumRD01SN531c
  , testCase "4Sin0rmapAccumRD01SN531d" testSin0rmapAccumRD01SN531d
--  , testCase "4Sin0rmapAccumRD01SN531Slice" testSin0rmapAccumRD01SN531Slice
  , testCase "4Sin0rmapAccumRD01SN54" testSin0rmapAccumRD01SN54
--  , testCase "4Sin0rmapAccumRD01SN55" testSin0rmapAccumRD01SN55
  , testCase "4Sin0rmapAccumRD01SN55acc" testSin0rmapAccumRD01SN55acc
  , testCase "4Sin0rmapAccumRD01SN56" testSin0rmapAccumRD01SN56
  , testCase "4Sin0rmapAccumRD01SN57" testSin0rmapAccumRD01SN57
  , testCase "4Sin0rmapAccumRD01SN58" testSin0rmapAccumRD01SN58
  , testCase "4Sin0rmapAccumRD01SN59" testSin0rmapAccumRD01SN59
  , testCase "4Sin0rmapAccumRD01SN5" testSin0rmapAccumRD01SN5
  , testCase "4Sin0rmapAccumRD01SN6" testSin0rmapAccumRD01SN6
  , testCase "4Sin0rmapAccumRD01SN7" testSin0rmapAccumRD01SN7
  , testCase "4Sin0ScanD1" testSin0ScanD1
  , testCase "4Sin0ScanD2" testSin0ScanD2
  , testCase "4Sin0ScanD3" testSin0ScanD3
  , testCase "4Sin0ScanD4" testSin0ScanD4
  , testCase "4Sin0ScanD5" testSin0ScanD5
  , testCase "4Sin0ScanD51" testSin0ScanD51
  , testCase "4Sin0ScanD51S" testSin0ScanD51S
  , testCase "4Sin0ScanD6" testSin0ScanD6
  , testCase "4Sin0ScanD7" testSin0ScanD7
  , testCase "4Sin0ScanD8" testSin0ScanD8
  , testCase "4Sin0ScanD8MapAccum" testSin0ScanD8MapAccum
  , testCase "4Sin0ScanD8rev" testSin0ScanD8rev
  , testCase "4Sin0ScanD8rev2" testSin0ScanD8rev2
  , testCase "4Sin0ScanD8rev3" testSin0ScanD8rev3
  , testCase "4Sin0ScanD8rev4" testSin0ScanD8rev4
  , testCase "4Sin0ScanD1RevPP" testSin0ScanD1RevPP
  , testCase "4Sin0ScanDFwdPP" testSin0ScanDFwdPP
  , testCase "4Sin0ScanD1Rev2PP" testSin0ScanD1Rev2PP
  , testCase "4Sin0ScanDFwd2PP" testSin0ScanDFwd2PP
  , testCase "4Sin0ScanD1Rev2" testSin0ScanD1Rev2
  , testCase "4Sin0ScanD1Rev3" testSin0ScanD1Rev3
  , testCase "4Sin0ScanD1Rev3PP" testSin0ScanD1Rev3PP
  , testCase "4Sin0ScanDFwd3PP" testSin0ScanDFwd3PP
  , testCase "4Sin0ScanD0fwd" testSin0ScanD0fwd
  , testCase "4Sin0ScanD1fwd" testSin0ScanD1fwd
  , testCase "4Sin0ScanD8fwd" testSin0ScanD8fwd
  , testCase "4Sin0ScanD8fwdMapAccum" testSin0ScanD8fwdMapAccum
  , testCase "4Sin0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4Sin0FoldNestedS1" testSin0FoldNestedS1
  , testCase "4Sin0FoldNestedS1PP" testSin0FoldNestedS1PP
  , testCase "4Sin0FoldNestedR1PP" testSin0FoldNestedR1PP
  , testCase "4Sin0FoldNestedR1SimpPP" testSin0FoldNestedR1SimpPP
  , testCase "4Sin0FoldNestedR1SimpNestedPP" testSin0FoldNestedR1SimpNestedPP
  , testCase "4Sin0FoldNestedR0LengthPPs" testSin0FoldNestedR0LengthPPs
  , testCase "4Sin0FoldNestedR1LengthPPs" testSin0FoldNestedR1LengthPPs
  , testCase "4Sin0FoldNestedR2LengthPPs" testSin0FoldNestedR2LengthPPs
  , testCase "4Sin0FoldNestedR3LengthPPs" testSin0FoldNestedR3LengthPPs
--  , testCase "4Sin0FoldNestedR4LengthPPs" testSin0FoldNestedR4LengthPPs
--  , testCase "4Sin0FoldNestedR5LengthPPs" testSin0FoldNestedR5LengthPPs
  , testCase "4Sin0MapAccumNestedR1PP" testSin0MapAccumNestedR1PP
  , testCase "4Sin0MapAccumNestedR3LengthPP" testSin0MapAccumNestedR3LengthPP
  , testCase "4Sin0MapAccumNestedR4" testSin0MapAccumNestedR4
--  , testCase "4Sin0MapAccumNestedR5" testSin0MapAccumNestedR5
  , testCase "4Sin0MapAccumNestedR5r" testSin0MapAccumNestedR5r
  , testCase "4Sin0MapAccumNestedR10r" testSin0MapAccumNestedR10r
  , testCase "4Sin0MapAccumNestedR10f" testSin0MapAccumNestedR10f
  , testCase "4Sin0MapAccumNestedR10fN" testSin0MapAccumNestedR10fN
  , testCase "4Sin0MapAccumNestedR10rf" testSin0MapAccumNestedR10rf
  , testCase "4Sin0MapAccumNestedR10rr" testSin0MapAccumNestedR10rr
  , testCase "4Sin0FoldNestedS1FwdFwd0" testSin0FoldNestedS1FwdFwd0
  , testCase "4Sin0FoldNestedS1FwdFwd" testSin0FoldNestedS1FwdFwd
  , testCase "4Sin0FoldNestedS1RevRev" testSin0FoldNestedS1RevRev
  , testCase "4Sin0FoldNestedS2" testSin0FoldNestedS2
  , testCase "4Sin0FoldNestedS3" testSin0FoldNestedS3
  , testCase "4Sin0FoldNestedS4" testSin0FoldNestedS4
--  , testCase "4Sin0FoldNestedS5" testSin0FoldNestedS5
  , testCase "4Sin0FoldNestedS5rev" testSin0FoldNestedS5rev
  , testCase "4Sin0FoldNestedS5fwd" testSin0FoldNestedS5fwd
  , testCase "4Sin0FoldNestedSi" testSin0FoldNestedSi
  , testCase "4Sin0FoldNestedR1" testSin0FoldNestedR1
  , testCase "4Sin0FoldNestedR1RevFwd" testSin0FoldNestedR1RevFwd
  , testCase "4Sin0FoldNestedR2" testSin0FoldNestedR2
  , testCase "4Sin0FoldNestedR2RevFwd" testSin0FoldNestedR2RevFwd
  , testCase "4Sin0FoldNestedR3" testSin0FoldNestedR3
  , testCase "4Sin0FoldNestedR4" testSin0FoldNestedR4
  , testCase "4Sin0FoldNestedR41" testSin0FoldNestedR41
  , testCase "4Sin0FoldNestedR40" testSin0FoldNestedR40
  , testCase "4Sin0FoldNestedR400" testSin0FoldNestedR400
  , testCase "4Sin0FoldNestedRi" testSin0FoldNestedRi
  , testCase "4Sin0FoldNestedR22" testSin0FoldNestedR22
  , testCase "4Sin0FoldNestedR21" testSin0FoldNestedR21
  , testCase "4Sin0FoldNestedR21PP" testSin0FoldNestedR21PP
  , testCase "4Sin0revhV" testSin0revhV
  , testCase "4Sin0revhVPP" testSin0revhVPP
  , testCase "4Sin0revhV2" testSin0revhV2
  , testCase "4Sin0revhV3" testSin0revhV3
  , testCase "4Sin0revhV4" testSin0revhV4
  , testCase "4Sin0revhV5" testSin0revhV5
  , testCase "4Sin0revhV6" testSin0revhV6
  , testCase "4Sin0revhV7" testSin0revhV7
  , testCase "4Sin0revhV8" testSin0revhV8
  , testCase "4Sin0revhFoldZipR" testSin0revhFoldZipR
  , testCase "4Sin0revhFoldZip4R" testSin0revhFoldZip4R
  , testCase "4Sin0revhFoldS" testSin0revhFoldS
  , testCase "4Sin0revhFold2S" testSin0revhFold2S
  , testCase "4Sin0revhFold3S" testSin0revhFold3S
  , testCase "4Sin0revhFold4S" testSin0revhFold4S
  , testCase "4Sin0revhFold5S" testSin0revhFold5S
  ]

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w

fooRrev :: forall g a. (ADReady g, GoodScalar a, Differentiable a)
        => (a, a, a) -> (g a 0, g a 0, g a 0)
fooRrev (x, y, z) =
  let fHVector :: forall f. ADReady f => HVector f -> f a 0
      fHVector v = foo (rfromD $ v V.! 0, rfromD $ v V.! 1, rfromD $ v V.! 2)
      sh = []
      zero = voidFromSh @a @0 sh
      shapes = V.fromList [zero, zero, zero]
      domsOf = rrev @g fHVector shapes
                    (V.fromList
                       [ DynamicRanked $ rconst @g $ OR.scalar x
                       , DynamicRanked $ rconst @g $ OR.scalar y
                       , DynamicRanked $ rconst @g $ OR.scalar z ])
  in ( rletHVectorIn domsOf (\v -> rfromD $ v V.! 0)
     , rletHVectorIn domsOf (\v -> rfromD $ v V.! 1)
     , rletHVectorIn domsOf (\v -> rfromD $ v V.! 2) )

testFooRrev :: Assertion
testFooRrev = do
  assertEqualUpToEpsilon 1e-10
    (2.4396285219055063, -1.953374825727421, 0.9654825811012627)
    (fooRrev @(Flip OR.Array) @Double (1.1, 2.2, 3.3))

testFooRrev2 :: Assertion
testFooRrev2 = do
  assertEqualUpToEpsilon 1e-10
    (2.4396284, -1.9533751, 0.96548253)
    (fooRrev @(Flip OR.Array) @Float (1.1, 2.2, 3.3))

testFooRrevPP1 :: Assertion
testFooRrevPP1 = do
  resetVarCounter
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstPretty IM.empty a1
    @?= "let x12 = sin 2.2 ; x13 = 1.1 * x12 ; x14 = recip (3.3 * 3.3 + x13 * x13) ; x15 = sin 2.2 ; x17 = 3.3 * 1.0 ; x18 = (negate 3.3 * x14) * 1.0 in x12 * x18 + x15 * x17"

-- Disabled, because different variable names with -O1.
_testFooRrevPP2 :: Assertion
_testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rlet (sin (rconstant 2.2)) (\\x39 -> rlet (rconstant 1.1 * x39) (\\x40 -> rlet (recip (rconstant 3.3 * rconstant 3.3 + x40 * x40)) (\\x41 -> rlet (sin (rconstant 2.2)) (\\x42 -> rlet (rconstant 1.1 * x42) (\\x43 -> rlet (rreshape [] (rreplicate 1 (rconstant 1.0))) (\\x44 -> rlet (rconstant 3.3 * x44) (\\x45 -> rlet (negate (rconstant 3.3 * x41) * x44) (\\x46 -> x39 * x46 + x42 * x45))))))))"

testFooRrev3 :: Assertion
testFooRrev3 = do
  let f (D _ a _) =
        let (a1, _, _) = fooRrev @(ADVal (Flip OR.Array)) @Double
                                 (OR.unScalar (runFlip a), 2.2, 3.3)
        in a1
  assertEqualUpToEpsilon 1e-10
    0
    (crev f 1.1)

testSin0Rrev :: Assertion
testSin0Rrev = do
  assertEqualUpToEpsilon 1e-10
    0.4535961214255773
    (rrev1 @(Flip OR.Array) @Double @0 @0 sin 1.1)

testSin0RrevPP1 :: Assertion
testSin0RrevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "cos 1.1 * 1.0"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstSimple IM.empty a1
    @?= "cos (rconstant 1.1) * rconstant 1.0"

testSin0Rrev3 :: Assertion
testSin0Rrev3 = do
  let f = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (-0.8912073600614354)
    (crev f 1.1)

testSin0Rrev4 :: Assertion
testSin0Rrev4 = do
  assertEqualUpToEpsilon 1e-10
    0.8988770945225438
    ((rrev1 sin . rrev1 @(Flip OR.Array) @Double @0 @0 sin) 1.1)

testSin0RrevPP4 :: Assertion
testSin0RrevPP4 = do
  let a1 = (rrev1 sin . rrev1 @(AstRanked FullSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "cos (cos 1.1 * 1.0) * 1.0"

testSin0Rrev5 :: Assertion
testSin0Rrev5 = do
  assertEqualUpToEpsilon 1e-10
    (-0.8912073600614354)
    (rrev1 @(Flip OR.Array) @Double @0 @0 (rrev1 sin) 1.1)

testSin0RrevPP5 :: Assertion
testSin0RrevPP5 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 (rrev1 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "negate (sin 1.1) * (1.0 * 1.0)"

testSin0Rrev3' :: Assertion
testSin0Rrev3' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.8912073600614354 :: OR.Array 0 Double)
    (rev' (rrev1 sin) 1.1)

testSin0Rrev4' :: Assertion
testSin0Rrev4' = do
  assertEqualUpToEpsilon' 1e-10
    (0.39052780643689855 :: OR.Array 0 Double)
    (rev' (rrev1 sin . rrev1 sin) 1.1)

testSin0Rrev5' :: Assertion
testSin0Rrev5' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.4535961214255773 :: OR.Array 0 Double)
    (rev' (rrev1 (rrev1 sin)) 1.1)

testSin0Rfwd :: Assertion
testSin0Rfwd = do
  assertEqualUpToEpsilon 1e-10
    0.4535961214255773  -- agrees with the rrev1 version above
    (rfwd1 @(Flip OR.Array) @Double @0 @0 sin 1.1)

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "1.0 * cos 1.1"  -- agrees with the rrev1 version above

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "let [x4 @Natural @Double @[]] = (\\[x1] [x2] -> [x1 * cos x2]) [[1.0], [1.1]] in x4"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let [x4 @Natural @Double @[]] = (\\[x1] [x2] -> [x1 * cos x2]) [[1.0], [1.1]] in x4"

testSin0Rfwd3 :: Assertion
testSin0Rfwd3 = do
  let f = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (-0.9803280960675791)
    (cfwd f 1.1 1.1)

testSin0Rfwd4 :: Assertion
testSin0Rfwd4 = do
  assertEqualUpToEpsilon 1e-10
    0.8988770945225438  -- agrees with the rrev1 version above
    ((rfwd1 sin . rfwd1 @(Flip OR.Array) @Double @0 @0 sin) 1.1)

testSin0RfwdPP4 :: Assertion
testSin0RfwdPP4 = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "1.0 * cos (1.0 * cos 1.1)"  -- agrees with the rrev1 version above

-- Disabled, because different variable names with -O1.
_testSin0RfwdPP4Dual :: Assertion
_testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let [x20 @Natural @Double @[]] = (\\[x17] [x18] -> [x17 * cos x18]) [[let [x16 @Natural @Double @[]] = (\\[x13] [x14] -> [x13 * cos x14]) [[rdualPart 1.1], [rdualPart 1.1]] in x16], [let [x16 @Natural @Double @[]] = (\\[x13] [x14] -> [x13 * cos x14]) [[rdualPart 1.1], [rdualPart 1.1]] in x16]] in x20"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (-0.8912073600614354)  -- agrees with the rrev1 version above
    (rfwd1 @(Flip OR.Array) @Double @0 @0 (rfwd1 sin) 1.1)

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 (rfwd1 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "(1.0 * negate (sin 1.1)) * 1.0"  -- agrees with the rrev1 version above

testSin0Rfwd3' :: Assertion
testSin0Rfwd3' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.8912073600614354 :: OR.Array 0 Double)
    (rev' (rfwd1 sin) 1.1)

testSin0Rfwd4' :: Assertion
testSin0Rfwd4' = do
  assertEqualUpToEpsilon' 1e-10
    (0.39052780643689855 :: OR.Array 0 Double)
    (rev' (rfwd1 sin . rfwd1 sin) 1.1)

testSin0Rfwd5' :: Assertion
testSin0Rfwd5' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.4535961214255773 :: OR.Array 0 Double)
    (rev' (rfwd1 (rfwd1 sin)) 1.1)

testSin0Rrev5S :: Assertion
testSin0Rrev5S = do
  assertEqualUpToEpsilon 1e-10
    (-0.8912073600614354)
    (srev1 @(Flip OS.Array) @Double @'[] @'[] (srev1 sin) 1.1)

testSin0RrevPP5S :: Assertion
testSin0RrevPP5S = do
  resetVarCounter
  let a1 = srev1 @(AstShaped PrimalSpan) @Double @'[] @'[] (srev1 sin) 1.1
  printAstPrettyS IM.empty (simplifyAst6S a1)
    @?= "negate (sin 1.1) * (1.0 * 1.0)"

testSin0Fold0 :: Assertion
testSin0Fold0 = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = rfold (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) 1.1)

testSin0Fold0ForComparison :: Assertion
testSin0Fold0ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. f Double 0 -> f Double 0
               f = id
           in f) 1.1)

testSin0Fold1 :: Assertion
testSin0Fold1 = do
  assertEqualUpToEpsilon' 1e-10
    (0.4535961214255773 :: OR.Array 0 Double)
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rconst (OR.constant @Double @1 [1] 42))) 1.1)

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rconst (OR.constant @Double @1 [5] 42))) 1.1)

testSin0FoldForComparison :: Assertion
testSin0FoldForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (sin . sin . sin . sin . sin) 1.1)

testSin0Fold3 :: Assertion
testSin0Fold3 = do
  assertEqualUpToEpsilon' 1e-10
    (0.4535961214255773 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\_x a -> sin a)
                        84 (rreplicate 3 a0)) 1.1)

testSin0Fold4 :: Assertion
testSin0Fold4 = do
  assertEqualUpToEpsilon' 1e-10
    (-0.7053476446727861 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x a -> atan2 (sin x) (sin a))
                        (2 * a0) (rreplicate 3 a0)) 1.1)

testSin0Fold5 :: Assertion
testSin0Fold5 = do
  assertEqualUpToEpsilon' 1e-10
    (1.2992412552109085 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7 a))
                        (2 * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0)))) 1.1)

testSin0Fold6 :: Assertion
testSin0Fold6 = do
  assertEqualUpToEpsilon' 1e-10
    (6 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) 1.1)

testSin0Fold7 :: Assertion
testSin0Fold7 = do
  assertEqualUpToEpsilon' 1e-10
    (250 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) 1.1)

testSin0Fold8 :: Assertion
testSin0Fold8 = do
  assertEqualUpToEpsilon' 1e-10
    (-2.200311410593445 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) 1.1)

testSin0Fold0S :: Assertion
testSin0Fold0S = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sfold @_ @f @Double @Double @'[] @'[] @0
                            (\x _a -> sin x)
                            x0 0
           in rfromS . f . sfromR) 1.1)

testSin0Fold1S :: Assertion
testSin0Fold1S = do
  assertEqualUpToEpsilon' 1e-10
    (0.4535961214255773 :: OR.Array 0 Double)
    (rev' ((let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
                f x0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[]
                                   -> f2 Double '[]
                                  g x _a = sin x
                              in g)
                        x0 (sconst (OS.constant @'[1] 42))
            in rfromS . f . sfromR)) 1.1)

testSin0Fold2S :: Assertion
testSin0Fold2S = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sfold (\x _a -> sin x)
                        x0 (sconst (OS.constant @'[5] @Double 42))
           in rfromS . f . sfromR) 1.1)

testSin0FoldForComparisonS :: Assertion
testSin0FoldForComparisonS = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f = sin . sin . sin . sin . sin
          in rfromS . f . sfromR) 1.1)

testSin0Fold3S :: Assertion
testSin0Fold3S = do
  assertEqualUpToEpsilon' 1e-10
    (0.4535961214255773 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\_x a -> sin a)
                        84 (sreplicate @f @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold4S :: Assertion
testSin0Fold4S = do
  assertEqualUpToEpsilon' 1e-10
    (-0.7053476446727861 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a -> atan2 (sin x) (sin a))
                        (2 * a0) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold5S :: Assertion
testSin0Fold5S = do
  assertEqualUpToEpsilon' 1e-10
    (1.2992412552109085 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[2, 5]
                                   -> f2 Double '[]
                                 g x a = ssum
                                   $ atan2 (sin $ sreplicate @f2 @5 x)
                                         (ssum $ sin $ ssum
                                          $ str $ sreplicate @f2 @7 a)
                             in g)
                        (2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in rfromS . f . sfromR) 1.1)

testSin0Fold6S :: Assertion
testSin0Fold6S = do
  assertEqualUpToEpsilon' 1e-10
    (6 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 1]
               f a0 = sfold @_ @f @Double @Double @'[2, 1] @'[] @2
                        (\x a -> str
                                 $ str x + sreplicate @_ @1
                                                      (sreplicate @_ @2 a))
                        (sreplicate @_ @2 (sreplicate @_ @1 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold7S :: Assertion
testSin0Fold7S = do
  assertEqualUpToEpsilon' 1e-10
    (250 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
               f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @2
                        (\x _a -> str $ sreplicate @_ @5 $ ssum (str x))
                        (sreplicate @_ @2 (sreplicate @_ @5 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold8S :: Assertion
testSin0Fold8S = do
  assertEqualUpToEpsilon' 1e-10
    (-2.200311410593445 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
               f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold8rev :: Assertion
testSin0Fold8rev = do
  assertEqualUpToEpsilon 1e-10
    (-2.200311410593445 :: Flip OR.Array Double 0)
    (rrev1 @(Flip OR.Array) @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) 1.1)

testSin0Fold8rev2 :: Assertion
testSin0Fold8rev2 = do
  let h = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @2
        (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    98.72666469795736
    (crev h 1.1)

testSin0Fold8Srev :: Assertion
testSin0Fold8Srev = do
  assertEqualUpToEpsilon 1e-10
    (-2.200311410593445 :: Flip OR.Array Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) 1.1)

testSin0Fold8Srev2 :: Assertion
testSin0Fold8Srev2 = do
  let h = srev1 @(ADVal (Flip OS.Array))
                (let f :: forall f. ADReadyS f
                       => f Double '[] -> f Double '[2, 5]
                     f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @3 a0)
                 in f)
  assertEqualUpToEpsilon 1e-10
    6.182232283434464e-2  -- seems quite unstable
    (crev h 0.0001)

testSin0Fold182SrevPP :: Assertion
testSin0Fold182SrevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan)
           (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
                f a0 = sfold @_ @f @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2 (sreplicate @_ @5 a)
                                        (sreplicate @_ @5
                                         $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) 1.1
  printAstPretty IM.empty a1
    @?= "let [v10 @[Natural] @Double @[5], m11 @[Natural] @Double @[1,5]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1] in let [v12 @[Natural] @Double @[5], v13 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (fromList @[5] [1.0,1.0,1.0,1.0,1.0])] [m11, sreplicate 1.1] in rfromS (sreshape v13) + rfromS (ssum v12)"

testSin0Fold18Srev :: Assertion
testSin0Fold18Srev = do
  assertEqualUpToEpsilon 1e-10
    (-2.4026418024701366 :: Flip OR.Array Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @2
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @2 a0)
            in rfromS . f . sfromR) 1.1)

testSin0Fold8fwd :: Assertion
testSin0Fold8fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.constant [2, 5] (-0.2200311410593445))
    (rfwd1 @(Flip OR.Array) @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) 1.1)

testSin0Fold8fwd2 :: Assertion
testSin0Fold8fwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @2
        (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    98.72666469795735
    (crev h 1.1)

testSin0Fold8Sfwd :: Assertion
testSin0Fold8Sfwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.constant [2, 5] (-0.2200311410593445))
    (rfwd1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) 1.1)

testSin0Fold8Sfwd2 :: Assertion
testSin0Fold8Sfwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array))
                (let f :: forall f. ADReadyS f
                       => f Double '[] -> f Double '[2, 5]
                     f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2 (ssum (str $ sin x))
                                         (sreplicate @_ @2
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (2 * a0)))
                        (sreplicate @_ @3 a0)
                 in rfromS . f . sfromR)
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.constant [2, 5] 10.859933116775313)
    (cfwd h 1.1 1.1)

testSin0Fold5Sfwd :: Assertion
testSin0Fold5Sfwd = do
  assertEqualUpToEpsilon 1e-10
    1.4291653807319993
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[2, 5]
                                   -> f2 Double '[]
                                 g x a = ssum
                                   $ atan2 (sin $ sreplicate @f2 @5 x)
                                         (ssum $ sin $ ssum
                                          $ str $ sreplicate @f2 @7 a)
                             in g)
                        (2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in rfromS . f . sfromR) 1.1 1.1)

testSin0Fold5Sfwds :: Assertion
testSin0Fold5Sfwds = do
  assertEqualUpToEpsilon 1e-10
    1.4291653807319993
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[2, 5]
                                   -> f2 Double '[]
                                 g x a = ssum
                                   $ atan2 (sin $ sreplicate @f2 @5 x)
                                         (ssum $ sin $ ssum
                                          $ str $ sreplicate @f2 @7 a)
                             in g)
                        (2 * a0)
                        (sreplicate @f @3
                                    (sreplicate @f @2
                                                (sreplicate @f @5 a0)))
           in f) 1.1 1.1)

testSin0Scan0 :: Assertion
testSin0Scan0 = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 1
               f x0 = rscan (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) 1.1)

testSin0Scan1 :: Assertion
testSin0Scan1 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rconst (OR.constant @Double @1 [1] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0Scan1ForComparison :: Assertion
testSin0Scan1ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rfromList [x0, sin x0])
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0Scan2 :: Assertion
testSin0Scan2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rconst (OR.constant @Double @1 [5] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0Scan3 :: Assertion
testSin0Scan3 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.360788364276732] :: OR.Array 5 Double)
    (rev' (\a0 -> rscan (\_x a -> sin a)
                        (rreplicate0N [1,1,1,1,1] 84)
                        (rreplicate 3 a0)) (rreplicate0N [1,1,1,1,1] 1.1))

testSin0Scan4 :: Assertion
testSin0Scan4 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [-0.4458209450295252] :: OR.Array 5 Double)
    (rev' (\a0 -> rscan (\x a -> atan2 (sin x) (sin a))
                        (rreplicate0N [1,1,1,1,1] 2 * a0)
                        (rreplicate 3 a0)) (rreplicate0N [1,1,1,1,1] 1.1))

testSin0Scan5 :: Assertion
testSin0Scan5 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [4.126141830000979] :: OR.Array 4 Double)
    (rev' (\a0 -> rscan (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7 a))
                        (rreplicate0N [1,1,1,1] 2 * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0))))
          (rreplicate0N [1,1,1,1] 1.1))

testSin0Scan6 :: Assertion
testSin0Scan6 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [12] :: OR.Array 2 Double)
    (rev' (\a0 -> rscan (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0Scan7 :: Assertion
testSin0Scan7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscan (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0Scan8 :: Assertion
testSin0Scan8 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev' (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rreplicate0N [1,1,1] 2 * a0)))
                        (rreplicate 3 a0)) (rreplicate0N [1,1,1] 1.1))

testSin0Scan8rev :: Assertion
testSin0Scan8rev = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [9.53298735735276])
    (rrev1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) 1.1)

testSin0Scan8rev2 :: Assertion
testSin0Scan8rev2 = do
  let h = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.9579482947575])
    (crev h 1.1)

testSin0Scan1RevPP1 :: Assertion
testSin0Scan1RevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPrettyButNested IM.empty (simplifyAst6 a1)
    @?= "let v12 = rconst (fromList [2] [42.0,42.0]) in let [x13 @Natural @Double @[], v14 @Natural @Double @[2], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x22] [x23] -> let x30 = sin x22 in [x30, x22, x30]) (\\[x35, x36] [x37, x38] -> let x49 = x35 * cos x37 in [x49, x35, x49]) (\\[x55, x56, x57] [x58, x59] -> [cos x58 * (x57 + x55) + x56, 0.0]) [1.1] [v12] in let v16 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x73] [x74, x75, x76] -> [cos x75 * (x74 + x73), 0]) (\\[x90, x91, x92, x93] [x94, x95, x96, x97] -> [(x92 * negate (sin x96)) * (x95 + x94) + (x91 + x90) * cos x96, 0.0]) (\\[x107, x108] [x109, x110, x111, x112] -> let x113 = cos x111 * x107 in [x113, x113, negate (sin x111) * ((x110 + x109) * x107), 0]) [0] [rslice 1 2 v16, v14, v12] in x17 + v16 ! [0]"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v6 = rconst (fromList [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v6 ! [0]) + cos 1.1 * v6 ! [1] + v6 ! [2]"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPrettyButNested IM.empty (simplifyAst6 a1)
    @?= "let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x15] [x16] -> let x20 = sin x15 in [x20, x15, x20]) (\\[x23, x24] [x25, x26] -> let x34 = x23 * cos x25 in [x34, x23, x34]) (\\[x37, x38, x39] [x40, x41] -> [cos x40 * (x39 + x37) + x38, 0.0]) [1.1] [v5] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x50] [x51, x52, x53] -> let x54 = x50 * cos x52 in [x54, x54]) (\\[x55, x57, x59, x61] [x56, x58, x60, x62] -> let x67 = x55 * cos x60 + (x59 * negate (sin x60)) * x56 in [x67, x67]) (\\[x75, x76] [x68, x69, x70, x71] -> let x77 = x76 + x75 in [cos x70 * x77, 0, negate (sin x70) * (x68 * x77), 0]) [1.0] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.0) v10"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPrettyButNested IM.empty (simplifyAst6 a1)
    @?= "let [v14 @Natural @Double @[3]] = (\\[x1] [x2] -> let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x15] [x16] -> let x20 = sin x15 in [x20, x15, x20]) (\\[x23, x24] [x25, x26] -> let x34 = x23 * cos x25 in [x34, x23, x34]) (\\[x37, x38, x39] [x40, x41] -> [cos x40 * (x39 + x37) + x38, 0.0]) [x2] [v5] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x50] [x51, x52, x53] -> let x54 = x50 * cos x52 in [x54, x54]) (\\[x55, x57, x59, x61] [x56, x58, x60, x62] -> let x67 = x55 * cos x60 + (x59 * negate (sin x60)) * x56 in [x67, x67]) (\\[x75, x76] [x68, x69, x70, x71] -> let x77 = x76 + x75 in [cos x70 * x77, 0, negate (sin x70) * (x68 * x77), 0]) [x1] [rreplicate 2 0.0, v7, v5] in [rappend (rreplicate 1 x1) v10]) [[1.0], [1.1]] in v14"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v12 = rconst (fromList [2] [5.0,7.0]) in let [x13 @Natural @Double @[], v14 @Natural @Double @[2], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v16 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v16, v14, v12] in x17 + v16 ! [0]"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7])))
                 1.1
  printGradient6Pretty IM.empty (simplifyArtifactRev art)
    @?= "\\v8 x1 -> let v4 = rconst (fromList [2] [5.0,7.0]) in let [x5 @Natural @Double @[], v6 @Natural @Double @[2], v7 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x1] [v4] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v8, v6, v4] in [x9 + v8 ! [0]]"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0])
                 1.1
  printGradient6Pretty IM.empty (simplifyArtifactRev art)
    @?= "\\v3 x1 -> [cos x1 * (cos (sin x1 - 5.0) * v3 ! [0]) + cos x1 * v3 ! [1] + v3 ! [2]]"

testSin0Scan1Fwd2PP :: Assertion
testSin0Scan1Fwd2PP = do
  resetVarCounter
  let (art, _) =
        fwdArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printArtifactFwdPretty IM.empty (simplifyArtifactFwd art)
    @?= "\\x1 x2 -> let v5 = rconst (fromList [2] [5.0,7.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x2] [v5] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x1] [rreplicate 2 0.0, v7, v5] in [rappend (rreplicate 1 x1) v10]"

testSin0Scan1Rev2 :: Assertion
testSin0Scan1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                    (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1)

testSin0Scan1Rev2ForComparison :: Assertion
testSin0Scan1Rev2ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0]) 1.1)

testSin0Scan1Rev3PP :: Assertion
testSin0Scan1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v12 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x13 @Natural @Double @[], v14 @Natural @Double @[2], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v16 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v16, v14, v12] in 5.0 * v18 ! [0] + 7.0 * v18 ! [1] + x17 + v16 ! [0]"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v9 = rconst (fromList [3] [1.0,1.0,1.0]) ; x10 = v9 ! [1] ; x11 = v9 ! [0] ; x12 = cos (sin 1.1 - 1.1 * 5.0) * x11 in cos 1.1 * x12 + 5.0 * (-1.0 * x12) + 7.0 * (-1.0 * x11) + cos 1.1 * x10 + 5.0 * (-1.0 * x10) + v9 ! [2]"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromList [1.0 * 5.0, 1.0 * 7.0], v7, v5] in rappend (rreplicate 1 1.0) v13"

testSin0Scan1Rev3 :: Assertion
testSin0Scan1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [-10.076255083995068] :: OR.Array 0 Double)
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) 1.1)

testSin0Scan1Rev3ForComparison :: Assertion
testSin0Scan1Rev3ForComparison = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [-10.076255083995068] :: OR.Array 0 Double)
    (rev' (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) 1.1)

testSin0Scan0fwd :: Assertion
testSin0Scan0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.0])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscan (\x _a -> sin x)
                      x0 (rzero @f @Double (0 :$: ZSR))
     in f) 1.1)

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 (rconst (OR.constant @Double @1 [1] 42)))
          1.1)

testSin0Scan1FwdForComparison :: Assertion
testSin0Scan1FwdForComparison = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rfromList [x0, sin x0]) 1.1)

testSin0Scan8fwd :: Assertion
testSin0Scan8fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) 1.1)

testSin0Scan8fwd2 :: Assertion
testSin0Scan8fwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.95794829475744])
    (crev h 1.1)

testUnitriangular0PP :: Assertion
testUnitriangular0PP = do
  resetVarCounter
  let k = 1000000
      a1 = rbuild1 @(AstRanked FullSpan) @Double @1 k
           $ \i -> rbuild1 k
           $ \j -> ifF (i <=. j) 0 1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rgather [1000000,1000000] (rconst (fromList [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1])"

unitriangular1 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> ShapeInt k -> ranked rk (2 + k)
unitriangular1 k sh =
  rbuild1 k $ \i ->
    rbuild1 k $ \j ->
      ifF (i <=. j) (rreplicate0N sh 0) (rreplicate0N sh 1)

testUnitriangular1PP :: Assertion
testUnitriangular1PP = do
  resetVarCounter
  let sh = 200 :$: 300 :$: 600 :$: ZSR
      k = 1000000
      a1 = unitriangular1 @3 @Double @(AstRanked FullSpan) k sh
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))]) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6])"

unitriangular2 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> ShapeInt k -> ranked rk (2 + k)
unitriangular2 k sh =
  rgather @_ @_ @_ @_ @1 (k :$: k :$: sh)
          (rfromList [ rreplicate0N sh 0
                     , rreplicate0N sh 1 ])
          (\(i :.: j :.: ZIR) -> ifF (i <. j) 0 1 :.: ZIR)

testUnitriangular2PP :: Assertion
testUnitriangular2PP = do
  resetVarCounter
  let sh = 200 :$: 300 :$: 600 :$: ZSR
      k = 1000000
      a1 = unitriangular2 @3 @Double @(AstRanked FullSpan) k sh
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))]) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4])"

rscanZip :: forall rn n ranked.
            ( GoodScalar rn, KnownNat n, RankedTensor ranked
            , HVectorTensor ranked (ShapedOf ranked) )
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector  -- shapes of the HVector above, not below
         -> ranked rn n
         -> HVector ranked  -- one rank higher than above
         -> ranked rn (1 + n)
rscanZip f eShs acc0 es =
  let width = case V.unsnoc es of
        Nothing -> error "rscanZip: can't determine argument width"
        Just (_, d) -> case shapeDynamicF (shapeToList . rshape) d of
          [] -> error "rscanZip: wrong rank of argument"
          w : _shm -> w
      sh = rshape acc0
  in withSNat width $ \snat ->
    rletHVectorIn
      (dmapAccumL Proxy
         snat
         (V.singleton $ voidFromSh @rn sh)
         (V.singleton $ voidFromSh @rn sh)
         eShs
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> HVectorOf f
              g acc e =
                rletInHVector
                  (f (rfromD $ acc V.! 0) e)
                  (\res -> dmkHVector
                           $ V.fromList
                               [ DynamicRanked @rn @n @f res
                               , DynamicRanked @rn @n @f res ])
          in g)
         (dmkHVector $ V.singleton $ DynamicRanked acc0)
         (dmkHVector es))
      (\res -> rappend (rfromList [acc0]) (rfromD $ res V.! 1))

sscanZip :: forall rn sh k ranked shaped.
            ( GoodScalar rn, Sh.Shape sh, KnownNat k, ShapedTensor shaped
            , HVectorTensor ranked shaped
            , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
       => (forall f. ADReadyS f
           => f rn sh -> HVector (RankedOf f) -> f rn sh)
       -> VoidHVector
       -> shaped rn sh
       -> HVector ranked
       -> shaped rn (1 + k ': sh)
sscanZip f eShs acc0 es =
  sletHVectorIn
    (dmapAccumL Proxy
       (SNat @k)
       (V.singleton $ voidFromShS @rn @sh)
       (V.singleton $ voidFromShS @rn @sh)
       eShs
       (let g :: forall f. ADReady f
              => HVector f -> HVector f -> HVectorOf f
            g acc e =
              sletInHVector
                (f (sfromD $ acc V.! 0) e)
                (\res -> dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res
                             , DynamicShaped @rn @sh @f res ])
        in g)
       (dmkHVector $ V.singleton $ DynamicShaped acc0)
       (dmkHVector es))
    (\res -> sappend @_ @_ @1 (sfromList [acc0]) (sfromD $ res V.! 1))

testSin0ScanD0 :: Assertion
testSin0ScanD0 = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 1
               f x0 = rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZSR])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$: ZSR))
           in f) 1.1)

testSin0rmapAccumRD0SC :: Assertion
testSin0rmapAccumRD0SC = do
  assertEqualUpToEpsilon 1e-10
    1
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] 0)
           in f) 1.1)

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    1
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] 0)
           in f) 1.1)

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    1
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) 1.1)

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    1
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) 1.1)

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    1
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) 1.1)

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    1
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[7]
              f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x
                                          , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) 1.1)

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    0
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] 0))
                       $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    0
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0))
                       $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    0
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] 0))
                       $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    0
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0))
                       $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    0
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [])) $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    0
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [])) $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    0
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [])) $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    0
    (rev @_ @_ @(AstShaped FullSpan)
         (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (V.fromList [])
                          (V.fromList [])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [])) $ \_ -> 3
           in f) 1.1)

testSin0rmapAccumRD0RC :: Assertion
testSin0rmapAccumRD0RC = do
  assertEqualUpToEpsilon 1e-10
    1
    (crev (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [voidFromSh @Double ZSR])
                          (V.fromList [voidFromSh @Double ZSR])
                          (V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) 1.1)

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [voidFromSh @Double ZSR])
                          (V.fromList [voidFromSh @Double ZSR])
                          (V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) 1.1)

testSin0ScanD01 :: Assertion
testSin0ScanD01 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = flip rindex0 [1]
                      $ rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZSR])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (1 :$: ZSR))
           in f) 1.1)

testSin0rmapAccumRD01SC :: Assertion
testSin0rmapAccumRD01SC = do
  assertEqualUpToEpsilon 1e-10
    0.4535961214255773
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = flip (sindex0 @_ @_ @'[1]) [0] $ (sfromD . (V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.fromList [DynamicShaped x0, DynamicShaped x0])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] 0)
           in f) 1.1)

testSin0rmapAccumRD01SN :: Assertion
testSin0rmapAccumRD01SN = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 1
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[] 3
                                      , DynamicShaped x0 ])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] 0)
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN2 :: Assertion
testSin0rmapAccumRD01SN2 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] 0)
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN3 :: Assertion
testSin0rmapAccumRD01SN3 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1, 3]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[3]])
                          (V.fromList [voidFromShS @Double @'[2]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1, 2] 0)
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN4 :: Assertion
testSin0rmapAccumRD01SN4 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1, 3]
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0 ])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN5 :: Assertion
testSin0rmapAccumRD01SN5 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1, 3]
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             ((sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1])
                                               / sin x / 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0 ])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN51 :: Assertion
testSin0rmapAccumRD01SN51 = do
  assertEqualUpToEpsilon' 1e-10
    (-69.90586521651421)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (\res -> ssum @_ @_ @6 (sfromD (res V.! 0))
                               + ssum0 @_ @_ @'[6, 5, 4, 3]
                                   (sfromD (res V.! 2)))
                      $ dunHVector
                      $ dbuild1 @(RankedOf f) @f (SNat @6) $ \j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[4, 3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                    x1 = sfromD @Double @'[3] $ xh V.! 1
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             ((sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1])
                                               / sin x / 3)
                                       , DynamicShaped
                                         $ sbuild1 @_ @_ @4 $ \i ->
                                             sfromD (a V.! 1)
                                             - sin x1 / sreplicate @_ @3
                                                          (1 + sfromIndex0 i) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped $ x0 / (1 + sfromIntegral (sconstant (sfromR j)))
                                      , DynamicShaped $ sreplicate @_ @3 x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] 1
                                         , DynamicShaped @Double @'[5, 3]
                                           $ sreplicate0N @_ @_ @'[5, 3]
                                               (sfromIntegral (sconstant (sfromR j)))
                                         , DynamicShaped @Double @'[5, 2] 3
                                         , DynamicShaped @Double @'[5, 2] 4 ]))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN52 :: Assertion
testSin0rmapAccumRD01SN52 = do
  assertEqualUpToEpsilon' 1e-10
    1.2207726343670955
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5, 3]
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             ((sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1])
                                               / sin x / 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] 1
                                         , DynamicShaped @Double @'[5, 2] 2
                                         , DynamicShaped @Double @'[5, 2] 3
                                         , DynamicShaped @Double @'[5, 2] 4 ])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN53 :: Assertion
testSin0rmapAccumRD01SN53 = do
  assertEqualUpToEpsilon' 1e-10
    6.529656272211302
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5, 3]
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (V.fromList [voidFromShS @Double @'[3]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 2)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[4]
                                                       (sfromD (a V.! 3)) [1]
                                              - smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sfromD (a V.! 2)
                                                   / sin x / 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1)))
                                           + sin x / 3 ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] 1
                                      , DynamicShaped @Double @'[5, 2] 2
                                      , DynamicShaped @Double @'[5, 3] 3
                                      , DynamicShaped @Double @'[5, 4] 4 ])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN531 :: Assertion
testSin0rmapAccumRD01SN531 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3]
       [-0.4284609293514655,0.2047077016162759,0.9242422110631052])
    (rev' (let f :: forall f. ADReadyS f => f Double '[3] -> f Double '[2, 3]
               f x0 = (\res -> 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [voidFromShS @Double @'[3]])
                          (V.fromList [ voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - (smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sin x / 3))) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [0.4, -0.01, -0.3, 0.2, 0.5, 1.3]) ])
           in rfromS . f . sfromR) (Flip $ OR.fromList [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531a :: Assertion
testSin0rmapAccumRD01SN531a = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3]
       [1.8478609886246988,-22.194216099801963,-40.72162125038692])
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[3] -> f Double '[2, 2, 2, 3]
               f x0 = (\res -> 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[6] ])
                          (V.fromList [ voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    x2 = sfromD @Double @'[6] $ xh V.! 1
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList
                                             [0.01, ssum @_ @_ @6 x2, 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - sfromD (a V.! 1)))
                                       , DynamicShaped
                                         $ 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - (smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sin x / 3))) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sreplicate @_ @3 (sfromIntegral (sconstant (sfromR j))))
                                      , DynamicShaped
                                        $ sreplicate @_ @6 (sfromIntegral (sconstant (sfromR i)))
                                          - sflatten (sappend x0 x0) ] )
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [-0.1, sreshape @_ @_ @'[] @'[1] $ sfromIntegral (sconstant (sfromR j))])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [0.4, -0.01, -0.3, sfromIntegral (sconstant (sfromR i)), 0.5, 1.3]) ])))
           in rfromS . f . sfromR) (Flip $ OR.fromList [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531b0 :: Assertion
testSin0rmapAccumRD01SN531b0 = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReady f
                 => f Double 0 -> f Double 2
               f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromR x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [0] [] ]))))
                        $ \d -> rfromD $ d V.! 0
           in f) 1.1)

testSin0rmapAccumRD01SN531bS :: Assertion
testSin0rmapAccumRD01SN531bS = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2]
               f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] 0 ]))))
                        $ \d -> sfromD $ d V.! 0
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN531bR :: Assertion
testSin0rmapAccumRD01SN531bR = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReady f
                 => f Double 0 -> f Double 2
               f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @f) (SNat @1)
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList [ DynamicRanked x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [1] [0] ]))))
                        $ \d -> rfromD $ d V.! 0
           in f) 1.1)

testSin0rmapAccumRD01SN531b0PP :: Assertion
testSin0rmapAccumRD01SN531b0PP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromD (x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [0] [] ]))))
                        $ \d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x14 @[Natural] @Double @[], v15 @[Natural] @Double @[0]] = dmapAccumRDer (SNat @0) (\\[x20] [x21] -> [x20, x20]) (\\[x29, x30] [x31, x32] -> [x29, x29]) (\\[x42, x43] [x44, x45] -> [0.0 + x43 + x42, 0.0]) [1.1] [rconst (fromList [0] [])] in let [x16 @[Natural] @Double @[], v17 @Natural @Double @[0]] = dmapAccumLDer (SNat @0) (\\[x54] [x55, x56] -> [x54, 0]) (\\[x63, x64, x65] [x66, x67, x68] -> [x63, 0.0]) (\\[x74, x75] [x76, x77, x78] -> [x74, 0, 0]) [4.0] [v15, rconst (fromList [0] [])] in [rfromS x16]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] 0 ]))))
                        $ \d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (fromList @[1] [0.0])] in let [x11 @[Natural] @Double @[], v12 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] [v9, sconst @[1] (fromList @[1] [0.0])] in [x11]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] 0 ]))))
                        $ \d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "(\\[m10] [x1] -> let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [x1] [sconst @[1] (fromList @[1] [0.0])] in let [x11 @[Natural] @Double @[], v12 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum m10)] [v9, sconst @[1] (fromList @[1] [0.0])] in [x11]) [[sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])], [1.1]]"

testSin0rmapAccumRD01SN531bRPP :: Assertion
testSin0rmapAccumRD01SN531bRPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @f) (SNat @1)
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector x0)
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [1] [0] ]))))
                        $ \d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorSimple
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "dletHVectorInHVector (dmapAccumRDer (SNat @1) (\\[x20 @Natural @Double @[]] [x21 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x20, DynamicRanked x20])) (\\[x29 @Natural @Double @[], x30 @Natural @Double @[]] [x31 @Natural @Double @[], x32 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x29, DynamicRanked x29])) (\\[x42 @Natural @Double @[], x43 @Natural @Double @[]] [x44 @Natural @Double @[], x45 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (x42 + x43), DynamicRanked 0.0])) dmkHVector (fromList [DynamicRanked (rconstant 1.1)]) dmkHVector (fromList [DynamicRanked (rconstant (rconst (fromList [1] [0.0])))])) (\\[x14 @Natural @Double @[], v15 @Natural @Double @[1]] -> dletHVectorInHVector (dmapAccumLDer (SNat @1) (\\[x54 @Natural @Double @[]] [x55 @Natural @Double @[], x56 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x54, DynamicRankedDummy])) (\\[x63 @Natural @Double @[], x64 @Natural @Double @[], x65 @Natural @Double @[]] [x66 @Natural @Double @[], x67 @Natural @Double @[], x68 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x63, DynamicRanked 0.0])) (\\[x74 @Natural @Double @[], x75 @Natural @Double @[]] [x76 @Natural @Double @[], x77 @Natural @Double @[], x78 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x74, DynamicRankedDummy, DynamicRankedDummy])) dmkHVector (fromList [DynamicRanked (rconstant 4.0)]) dmkHVector (fromList [DynamicRanked v15, DynamicRanked (rconstant (rconst (fromList [1] [0.0])))])) (\\[x16 @Natural @Double @[], v17 @Natural @Double @[1]] -> dmkHVector (fromList [DynamicRanked x16])))"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [0] [] ]))))
                        $ \d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [m21 @[Natural] @Double @[2,2], t22 @[Natural] @Double @[0,2,2]] = dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))) + sreplicate (sreplicate 1.1) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [0] []))))] in let [m24 @[Natural] @Double @[2,2], t25 @Natural @Double @[0,2,2]] = dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])) (\\[i23] -> [i23])] [t22, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [0] []))))] in [rfromS (ssum (ssum m24))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] 0 ]))))
                        $ \d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "let [m13 @[Natural] @Double @[2,2], t14 @[Natural] @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (fromList @[1] [0.0]))))] in let [m18 @[Natural] @Double @[2,2], t19 @[Natural] @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])) (\\[i17] -> [i17])] [t14, stranspose (sreplicate (sreplicate (sconst @[1] (fromList @[1] [0.0]))))] in [ssum (ssum m18)]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @f) (SNat @1)
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (dmkHVector $ V.fromList
                             [ DynamicRanked @Double @0
                               $ rfromIntegral (rconstant (i + j))
                                 + rfromD (x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ OR.fromList [1] [0] ]))))
                        $ \d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [m19 @Natural @Double @[2,2], t20 @Natural @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [1] [0.0]))))] in let [m21 @Natural @Double @[2,2], t22 @Natural @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (fromList [2,2] [1.0,1.0,1.0,1.0])] [t20, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [1] [0.0]))))] in [rsum (rreshape [4] m21)]"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (-1.8866871148429984)
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2, 2]
               f x0 = (\res -> 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 1))
                      $ dunHVector
                      $ dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0)
                                       , DynamicShaped
                                         $ 1 - sin x / 3 - sfromD (a V.! 0) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sconstant (sfromR j))) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [0.4, sfromIntegral (sconstant (sfromR i))]) ])))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN531d :: Assertion
testSin0rmapAccumRD01SN531d = do
  assertEqualUpToEpsilon 1e-10
    V.empty
    ((let f :: forall f. ADReadyS f
            => f Double '[] -> HVector (RankedOf f)
          f x0 = dunHVector
                      $ dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @0) $ \j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0)
                                       , DynamicShaped
                                         $ 1 - sin x / 3 - sfromD (a V.! 0) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sconstant (sfromR j))) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [0.4, sfromIntegral (sconstant (sfromR i))]) ])))
      in f . sfromR) (1.1 :: Flip OR.Array Double 0))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN531Slice :: Assertion
_testSin0rmapAccumRD01SN531Slice = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2]
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList [ DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [])))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN54 :: Assertion
testSin0rmapAccumRD01SN54 = do
  assertEqualUpToEpsilon' 1e-10
    1.538239371140263
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5, 3]
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0)))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (V.fromList [voidFromShS @Double @'[3]])
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                 let x = sfromD @Double @'[3] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sin x - sfromD (a V.! 2) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] 1
                                      , DynamicShaped @Double @'[5, 2] 2
                                      , DynamicShaped @Double @'[5, 3] 3
                                      , DynamicShaped @Double @'[5, 4] 4 ])
           in rfromS . f . sfromR) 1.1)

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN55 :: Assertion
_testSin0rmapAccumRD01SN55 = do
  assertEqualUpToEpsilon' 1e-10
    6.529656272211302
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5, 3]
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                         (V.fromList [voidFromShS @Double @'[3]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    a = xh
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[4]
                                                       (sfromD (a V.! 0)) [1]
                                              - smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sfromD (a V.! 0)
                                                   / sin x / 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 0)))
                                           + sin x / 3 ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN55acc :: Assertion
testSin0rmapAccumRD01SN55acc = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3] [-21.0,-42.0,-21.0])
    (rev' (let f :: forall f. ADReadyS f => f Double '[3] -> f Double '[2, 3]
               f x0 = (\res -> 2 - str (sreplicate @_ @3
                                         $ ssum @_ @_ @7
                                         $ str (sfromD (res V.! 1)))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g _xh a =
                                let x = sreplicate @g @3 2
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - (smaxIndex
                                                  @_ @Double @Double @'[] @3
                                                  (sin x / 3))) ]
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sindex0 x0 [1], -0.01, -0.3, ssum x0, 0.5, 1.3]) ])
           in rfromS . f . sfromR) (Flip $ OR.fromList [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN56 :: Assertion
testSin0rmapAccumRD01SN56 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] 1
                                        , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] 0])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[2] [0.4989557335681351,1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] 0])
           in f) 1.1 1.1)

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[5] [0,0,0,0,1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] 1
                                        , DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[5] 0])
           in f) 1.1 1.1)

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OS.fromList @'[1] [1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] 1
                                        , DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[1] 0])
           in f) 1.1 1.1)

testSin0rmapAccumRD01SN6 :: Assertion
testSin0rmapAccumRD01SN6 = do
  assertEqualUpToEpsilon 1e-10
    0.4535961214255773
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> HVector (RankedOf f)
               f x0 = dunHVector
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           `atan2` smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             ((sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1])
                                               / sin x / 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0 ])
           in hVectorADValToADVal . f) 1.1)

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    0.4535961214255773
    (crev (let f :: forall f. ADReadyS f
                 => f Double '[] -> HVectorOf (RankedOf f)
               f x0 = dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (V.fromList [voidFromShS @Double @'[]])
                          (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           ** smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (sin x / 6
                                              + (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1])
                                                 / sin x / 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / 6) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0
                                         , DynamicShaped @Double @'[1, 2] 0 ])
           in hVectorADValToADVal . f @(ADVal (Flip OS.Array))) 1.1)

testSin0ScanD1 :: Assertion
testSin0ScanD1 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [1] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [5] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD3 :: Assertion
testSin0ScanD3 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.360788364276732] :: OR.Array 5 Double)
    (rev' (\a0 -> rscanZip (\_x a ->
                            sin $ rfromD @Double @5
                                    (a V.! 0))
                         (V.fromList [ voidFromSh @Double (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)
                                     , voidFromSh @Double (4 :$: 5 :$: 6 :$: 7 :$: 8 :$: ZSR) ])
                         (rreplicate0N [1,1,1,1,1] 84)
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 a0
                            , DynamicRanked
                              $ rconst (OR.constant @Double @6
                                          [3, 4, 5, 6, 7, 8] 32) ]))
                         (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD4 :: Assertion
testSin0ScanD4 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [-0.4458209450295252] :: OR.Array 5 Double)
    (rev' (\a0 -> rscanZip (\x a -> atan2 (sin x)
                                        (sin $ rfromD (a V.! 0)))
                         (V.fromList [voidFromSh @Double
                                        (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                         (rreplicate0N [1,1,1,1,1] 2 * a0)
                         (V.singleton $ DynamicRanked
                          $ rreplicate 3 a0)) (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD5 :: Assertion
testSin0ScanD5 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [4.126141830000979] :: OR.Array 4 Double)
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rfromD (a V.! 0)))
                         (V.fromList [ voidFromSh @Double
                                         (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)
                                     , voidFromSh @Double
                                         (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR) ])
                         (rreplicate0N [1,1,1,1] 2 * a0)
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 (rreplicate 2 (rreplicate 5 a0))
                            , DynamicRanked
                              $ rreplicate 3 (rreplicate 8 (rreplicate 3 a0)) ]
                         ))
          (rreplicate0N [1,1,1,1] 1.1))

testSin0ScanD51 :: Assertion
testSin0ScanD51 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [319.68688158967257] :: OR.Array 4 Double)
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rreplicate 2 $ rreplicate 5
                                          $ rsum $ rsum
                                          $ rfromD (a V.! 1)))
                         (V.fromList [ voidFromSh @Double
                                         (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)
                                     , voidFromSh @Double
                                         (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR) ])
                         (rreplicate0N [1,1,1,1] 2 * a0)
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 (rreplicate 2 (rreplicate 5 a0))
                            , DynamicRanked
                              $ rreplicate 3 (rreplicate 8 (rreplicate 3 a0)) ]
                         ))
          (rreplicate0N [1,1,1,1] 1.1))

testSin0ScanD51S :: Assertion
testSin0ScanD51S = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [319.68688158967257] :: OR.Array 4 Double)
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[1,1,1,1] -> f Double '[4,1,1,1,1]
               f a0 =
                 sscanZip
                   (let g :: forall f2. ADReadyS f2
                          => f2 Double '[1,1,1,1] -> HVector (RankedOf f2)
                          -> f2 Double '[1,1,1,1]
                        g x a =
                          ssum
                          $ atan2 (sin $ sreplicate @f2 @5 x)
                                  (ssum $ sin $ ssum
                                   $ str $ sreplicate @f2 @7
                                   $ sreplicate @f2 @2 $ sreplicate @f2 @5
                                   $ ssum @_ @_ @3 $ ssum @_ @_ @8
                                   $ sfromD $ a V.! 1)
                    in g)
                   (V.fromList [ voidFromShS @Double
                                                                             @'[2, 5, 1, 1, 1, 1]
                                                                           , voidFromSh @Double
                                                                             (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR) ])
                   (sreplicate0N @_ @_ @[1,1,1,1] 2 * a0)
                   (V.fromList
                      [ DynamicShaped
                        $ sreplicate @f @3 (sreplicate @f @2 (sreplicate @f @5 a0))
                      , DynamicRanked $ rfromS
                        $ sreplicate @f @3 (sreplicate @f @8 (sreplicate @f @3 a0)) ]
                   )
           in rfromS . f . sfromR) (rreplicate0N [1,1,1,1] 1.1))

testSin0ScanD6 :: Assertion
testSin0ScanD6 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [12] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x a -> rtr
                                 $ rtr x + rreplicate 1
                                             (rreplicate 2
                                                (rfromD (a V.! 0))))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZSR)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZSR)])
                         (rreplicate 2 (rreplicate 5 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD8 :: Assertion
testSin0ScanD8 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev' (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] 2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
                       (rreplicate0N [1,1,1] 1.1))

testSin0ScanD8MapAccum :: Assertion
testSin0ScanD8MapAccum = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev'
       (\a0 -> (rfromD @_ @6 . (V.! 1))
               $ dunHVector
               $ dmapAccumR Proxy (SNat @4)
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                   (let g :: forall g. ADReady g
                          => HVector g -> HVector g -> HVectorOf g
                        g xh a =
                         let x = rfromD @Double @5 $ xh V.! 0
                         in dmkHVector
                          $ V.fromList
                            [ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a))
                           , DynamicRanked x ]
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5
                                      (rreplicate0N [1,1,1] 2 * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0))
       (rreplicate0N [1,1,1] 1.1))

testSin0ScanD8rev :: Assertion
testSin0ScanD8rev = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [9.53298735735276])
    (rrev1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8rev2 :: Assertion
testSin0ScanD8rev2 = do
  let h = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.9579482947575])
    (crev h 1.1)

testSin0ScanD8rev3 :: Assertion
testSin0ScanD8rev3 = do
  let h :: forall f. ADReady f => f Double 0 -> f Double 0
      h = rrev1 @f @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [285.95794829475744])
    (rev' h 1.1)

testSin0ScanD8rev4 :: Assertion
testSin0ScanD8rev4 = do
  let h :: forall f. ADReady f => f Double 0 -> f Double 0
      h = rrev1 @f @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [ voidFromSh @Double ZSR
                                   , voidFromShS @Double @'[] ])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.fromList [ DynamicRanked $ rreplicate 3 a0
                                   , DynamicShaped
                                     $ sreplicate @_ @3
                                         (sfromR @_ @_ @'[] a0) ]))
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [285.95794829475744])
    (rev' h 1.1)

testSin0ScanD1RevPP :: Assertion
testSin0ScanD1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v12 = rconst (fromList [2] [42.0,42.0]) in let [x13 @Natural @Double @[], v14 @Natural @Double @[2], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v16 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v16, v14, v12] in x17 + v16 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.0) v10"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v12 = rconst (fromList [2] [5.0,7.0]) in let [x13 @Natural @Double @[], v14 @Natural @Double @[2], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v16 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v16, v14, v12] in x17 + v16 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rconst (fromList [2] [5.0,7.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.0) v10"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [2.417297824578748] :: OR.Array 0 Double)
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconst (OS.fromList @'[2, 2] @Double [5, 7, 3, 4])
                      !$ (k :.$ ZIS) ))
          1.1)

testSin0ScanD1Rev3 :: Assertion
testSin0ScanD1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [47.150000000000006] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZSR])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1)

testSin0ScanD1Rev3PP :: Assertion
testSin0ScanD1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZSR])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1
  length (printAstSimple IM.empty (simplifyAst6 a1))
    @?= 4421

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromList [1.0 * 5.0, 1.0 * 7.0], v7, v5] in rappend (rreplicate 1 1.0) v13"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.0])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [voidFromSh @Double ZSR])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$: ZSR))
     in f) 1.1)

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (V.fromList [ voidFromSh @Double ZSR
                               , voidFromSh @Double (3 :$: 4 :$: ZSR)])
                   x0 (V.fromList
                         [ DynamicRanked
                           $ rconst (OR.constant @Double @1 [1] 42)
                         , DynamicRanked
                           $ rconst (OR.constant @Double @3 [1, 3, 4] 32) ]))
          1.1)

testSin0ScanD8fwd :: Assertion
testSin0ScanD8fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                      (V.fromList [voidFromSh @Double ZSR])
                      (rreplicate 2 (rreplicate 5 (2 * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8fwdMapAccum :: Assertion
testSin0ScanD8fwdMapAccum = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @(Flip OR.Array) @Double @0 @3 @Double
       (\a0 -> rreverse $ (rfromD . (V.! 1))
               $ dunHVector
               $ dmapAccumR Proxy (SNat @4)
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (V.fromList [voidFromSh @Double ZSR])
                   (let g :: forall g. ADReady g
                          => HVector g -> HVector g -> HVectorOf g
                        g xh a =
                         let x = rfromD @Double @2 $ xh V.! 0
                         in dmkHVector
                          $ V.fromList
                            [ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a))
                           , DynamicRanked x ]
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5 (2 * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0)) 1.1)

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.95794829475744])
    (crev h 1.1)

testSin0FoldNestedS1 :: Assertion
testSin0FoldNestedS1 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedS1PP :: Assertion
testSin0FoldNestedS1PP = do
  resetVarCounter
  let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
      f z = sfold (\x a ->
               sfold (\x2 a2 -> x2 + tan a2)
                     a (sreplicate @_ @22 x))
                  z (sreplicate @_ @11 z)
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g x = srev (\v -> f (sfromD $ v V.! 0))
                 (V.singleton (voidFromShS @Double @'[]))
                 x
  printAstHVectorPretty
    IM.empty
    (g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "let [x4 @[Natural] @Double @[], v5 @[Natural] @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1] in let [x7 @[Natural] @Double @[], v8 @[Natural] @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v5, sreplicate 1.1] in [ssum v8 + x7]"

testSin0FoldNestedR1PP :: Assertion
testSin0FoldNestedR1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPretty
    IM.empty
    (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v11, rreplicate 11 1.1] in [rsum v13 + x12]"

testSin0FoldNestedR1SimpPP :: Assertion
testSin0FoldNestedR1SimpPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v11, rreplicate 11 1.1] in [rsum v13 + x12]"

testSin0FoldNestedR1SimpNestedPP :: Assertion
testSin0FoldNestedR1SimpNestedPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) (\\[x16] [x17] -> [let [x25 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\[x31] [x32] -> [x31 + tan x32]) (\\[x49, x50] [x51, x52] -> let x54 = cos x52 in [x49 + x50 * recip (x54 * x54)]) (\\[x64] [x65, x66] -> let x68 = cos x66 in [x64, recip (x68 * x68) * x64]) [x17] [rreplicate 22 x16] in x25, x16]) (\\[x73, x74] [x75, x76] -> let [x95 @Natural @Double @[]] = let [x92 @Natural @Double @[], v93 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x100] [x101] -> [x100 + tan x101, x100]) (\\[x115, x116] [x117, x118] -> let x131 = cos x118 in [x115 + x116 * recip (x131 * x131), x115]) (\\[x140, x141] [x142, x143] -> let x154 = cos x143 in [x140 + x141, recip (x154 * x154) * x140]) [x76] [rreplicate 22 x75] in let [x94 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\[x163] [x164, x165, x166] -> let x169 = cos x166 in [x163 + x164 * recip (x169 * x169)]) (\\[x195, x196, x197, x198] [x199, x200, x201, x202] -> let x206 = cos x202 ; x207 = x206 * x206 ; x208 = x198 * negate (sin x202) in [x195 + x196 * recip x207 + ((x208 * x206 + x208 * x206) * negate (recip (x207 * x207))) * x200]) (\\[x224] [x225, x226, x227, x228] -> let x232 = cos x228 ; x233 = x232 * x232 ; x234 = negate (recip (x233 * x233)) * (x226 * x224) in [x224, recip x233 * x224, 0, negate (sin x228) * (x232 * x234 + x232 * x234)]) [x74] [rreplicate 22 x73, v93, rreplicate 22 x75] in [x94] in [x95, x73]) (\\[x239, x240] [x241, x242] -> let [x263 @Natural @Double @[], x264 @Natural @Double @[]] = let [x259 @Natural @Double @[], v260 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x269] [x270] -> [x269 + tan x270, x269]) (\\[x284, x285] [x286, x287] -> let x300 = cos x287 in [x284 + x285 * recip (x300 * x300), x284]) (\\[x309, x310] [x311, x312] -> let x323 = cos x312 in [x309 + x310, recip (x323 * x323) * x309]) [x242] [rreplicate 22 x241] in let [x261 @Natural @Double @[], v262 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x330] [x331, x332] -> let x335 = cos x332 in [x330, recip (x335 * x335) * x330]) (\\[x356, x357, x358] [x359, x360, x361] -> let x365 = cos x361 ; x366 = x365 * x365 ; x367 = x358 * negate (sin x361) in [x356, ((x367 * x365 + x367 * x365) * negate (recip (x366 * x366))) * x359 + x356 * recip x366]) (\\[x383, x384] [x385, x386, x387] -> let x391 = cos x387 ; x392 = x391 * x391 ; x393 = negate (recip (x392 * x392)) * (x385 * x384) in [recip x392 * x384 + x383, 0, negate (sin x387) * (x391 * x393 + x391 * x393)]) [x239] [v260, rreplicate 22 x241] in [rsum v262, x261] in [x263 + x240, x264]) [1.1] [rreplicate 11 1.1] in let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) (\\[x397] [x398, x399] -> let [x404 @Natural @Double @[], v405 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x410] [x411] -> [x410 + tan x411, x410]) (\\[x416, x417] [x418, x419] -> let x421 = cos x419 in [x416 + x417 * recip (x421 * x421), x416]) (\\[x426, x427] [x428, x429] -> let x431 = cos x429 in [x426 + x427, recip (x431 * x431) * x426]) [x399] [rreplicate 22 x398] in let [x406 @Natural @Double @[], v407 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x435] [x436, x437] -> let x439 = cos x437 in [x435, recip (x439 * x439) * x435]) (\\[x446, x447, x448] [x449, x450, x451] -> let x455 = cos x451 ; x456 = x455 * x455 ; x457 = x448 * negate (sin x451) in [x446, ((x457 * x455 + x457 * x455) * negate (recip (x456 * x456))) * x449 + x446 * recip x456]) (\\[x463, x464] [x465, x466, x467] -> let x471 = cos x467 ; x472 = x471 * x471 ; x473 = negate (recip (x472 * x472)) * (x465 * x464) in [recip x472 * x464 + x463, 0, negate (sin x467) * (x471 * x473 + x471 * x473)]) [x397] [v405, rreplicate 22 x398] in [rsum v407, x406]) (\\[x504, x505, x506] [x507, x508, x509] -> let [x510 @Natural @Double @[], v511 @Natural @Double @[22], v512 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x522] [x523] -> [x522 + tan x523, x522, x522]) (\\[x532, x533] [x534, x535] -> let x544 = cos x535 in [x532 + x533 * recip (x544 * x544), x532, x532]) (\\[x550, x551, x552] [x553, x554] -> let x563 = cos x554 in [x551 + x550 + x552, recip (x563 * x563) * x550]) [x509] [rreplicate 22 x508] in let [x513 @Natural @Double @[], v514 @Natural @Double @[22], v515 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x567] [x568, x569] -> let x577 = cos x569 in [x567, x567, recip (x577 * x577) * x567]) (\\[x584, x585, x586] [x587, x588, x589] -> let x604 = cos x589 ; x605 = x604 * x604 ; x606 = x586 * negate (sin x589) in [x584, x584, ((x606 * x604 + x606 * x604) * negate (recip (x605 * x605))) * x587 + x584 * recip x605]) (\\[x613, x614, x615] [x616, x617, x618] -> let x633 = cos x618 ; x634 = x633 * x633 ; x635 = negate (recip (x634 * x634)) * (x616 * x615) in [x614 + recip x634 * x615 + x613, 0.0, negate (sin x618) * (x633 * x635 + x633 * x635)]) [x507] [v512, rreplicate 22 x508] in let [x516 @Natural @Double @[], v517 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x640] [x641, x642, x643] -> let x645 = cos x643 in [x640 + x641 * recip (x645 * x645), x640]) (\\[x663, x664, x665, x666] [x667, x668, x669, x670] -> let x671 = cos x670 ; x672 = x671 * x671 ; x673 = x666 * negate (sin x670) in [x663 + x664 * recip x672 + ((x673 * x671 + x673 * x671) * negate (recip (x672 * x672))) * x668, x663]) (\\[x685, x686] [x687, x688, x689, x690] -> let x691 = cos x690 ; x692 = x691 * x691 ; x693 = negate (recip (x692 * x692)) * (x688 * x685) in [x685 + x686, recip x692 * x685, 0, negate (sin x690) * (x691 * x693 + x691 * x693)]) [x506] [rreplicate 22 x505, v511, rreplicate 22 x508] in let [x518 @Natural @Double @[], v519 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x700] [x701, x702, x703, x704, x705] -> let x709 = cos x705 ; x710 = x709 * x709 ; x711 = x702 * negate (sin x705) in [x700, ((x711 * x709 + x711 * x709) * negate (recip (x710 * x710))) * x703 + x700 * recip x710]) (\\[x752, x753, x754, x755, x756, x757] [x758, x759, x760, x761, x762, x763] -> let x764 = cos x763 ; x765 = x764 * x764 ; x766 = negate (sin x763) ; x767 = x760 * x766 ; x768 = x765 * x765 ; x769 = x767 * x764 + x767 * x764 ; x770 = negate (recip x768) ; x771 = x754 * x766 + ((x757 * cos x763) * -1.0) * x760 ; x772 = x757 * negate (sin x763) ; x773 = x772 * x764 + x772 * x764 in [x752, ((x771 * x764 + x772 * x767 + x771 * x764 + x772 * x767) * x770 + (((x773 * x765 + x773 * x765) * negate (recip (x768 * x768))) * -1.0) * x769) * x761 + x755 * (x769 * x770) + x752 * recip x765 + (x773 * negate (recip (x765 * x765))) * x758]) (\\[x799, x800] [x801, x802, x803, x804, x805, x806] -> let x807 = cos x806 ; x808 = x807 * x807 ; x809 = negate (sin x806) ; x810 = x803 * x809 ; x811 = x808 * x808 ; x812 = x810 * x807 + x810 * x807 ; x813 = negate (recip x811) ; x814 = x804 * x800 ; x815 = negate (recip (x811 * x811)) * (-1.0 * (x812 * x814)) ; x816 = x813 * x814 ; x817 = x807 * x816 + x807 * x816 ; x818 = x808 * x815 + x808 * x815 + negate (recip (x808 * x808)) * (x801 * x800) in [recip x808 * x800 + x799, 0, x809 * x817, (x812 * x813) * x800, 0, negate (sin x806) * (x807 * x818 + x807 * x818 + x810 * x816 + x810 * x816) + cos x806 * (-1.0 * (x803 * x817))]) [x504] [v517, rreplicate 22 x505, v514, v512, rreplicate 22 x508] in [rsum v519, x518]) (\\[x842, x843] [x844, x845, x846] -> let [x847 @Natural @Double @[], v848 @Natural @Double @[22], v849 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x860] [x861] -> [x860 + tan x861, x860, x860]) (\\[x870, x871] [x872, x873] -> let x882 = cos x873 in [x870 + x871 * recip (x882 * x882), x870, x870]) (\\[x888, x889, x890] [x891, x892] -> let x901 = cos x892 in [x889 + x888 + x890, recip (x901 * x901) * x888]) [x846] [rreplicate 22 x845] in let [x850 @Natural @Double @[], v851 @Natural @Double @[22], v852 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x905] [x906, x907] -> let x915 = cos x907 in [x905, x905, recip (x915 * x915) * x905]) (\\[x922, x923, x924] [x925, x926, x927] -> let x942 = cos x927 ; x943 = x942 * x942 ; x944 = x924 * negate (sin x927) in [x922, x922, ((x944 * x942 + x944 * x942) * negate (recip (x943 * x943))) * x925 + x922 * recip x943]) (\\[x951, x952, x953] [x954, x955, x956] -> let x971 = cos x956 ; x972 = x971 * x971 ; x973 = negate (recip (x972 * x972)) * (x954 * x953) in [x952 + recip x972 * x953 + x951, 0.0, negate (sin x956) * (x971 * x973 + x971 * x973)]) [x844] [v849, rreplicate 22 x845] in let [x853 @Natural @Double @[], v854 @Natural @Double @[22], v855 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x979] [x980, x981, x982, x983] -> let x987 = cos x983 ; x988 = x987 * x987 ; x989 = negate (recip (x988 * x988)) * (x981 * x980) in [recip x988 * x980 + x979, 0, negate (sin x983) * (x987 * x989 + x987 * x989)]) (\\[x1028, x1029, x1030, x1031, x1032] [x1033, x1034, x1035, x1036, x1037] -> let x1038 = cos x1037 ; x1039 = x1038 * x1038 ; x1040 = x1039 * x1039 ; x1041 = negate (recip x1040) ; x1042 = x1035 * x1034 ; x1043 = x1041 * x1042 ; x1044 = x1032 * negate (sin x1037) ; x1045 = x1044 * x1038 + x1044 * x1038 ; x1046 = (((x1045 * x1039 + x1045 * x1039) * negate (recip (x1040 * x1040))) * -1.0) * x1042 + (x1030 * x1034 + x1029 * x1035) * x1041 in [x1028 + (x1045 * negate (recip (x1039 * x1039))) * x1034 + x1029 * recip x1039, 0.0, ((x1032 * cos x1037) * -1.0) * (x1038 * x1043 + x1038 * x1043) + (x1044 * x1043 + x1046 * x1038 + x1044 * x1043 + x1046 * x1038) * negate (sin x1037)]) (\\[x1072, x1073, x1074] [x1075, x1076, x1077, x1078, x1079] -> let x1080 = cos x1079 ; x1081 = x1080 * x1080 ; x1082 = x1081 * x1081 ; x1083 = negate (recip x1082) ; x1084 = x1077 * x1076 ; x1085 = x1083 * x1084 ; x1086 = negate (sin x1079) * x1074 ; x1087 = x1080 * x1086 + x1080 * x1086 ; x1088 = x1083 * x1087 ; x1089 = negate (recip (x1082 * x1082)) * (-1.0 * (x1084 * x1087)) ; x1090 = x1081 * x1089 + x1081 * x1089 + negate (recip (x1081 * x1081)) * (x1076 * x1072) in [x1072, x1077 * x1088 + recip x1081 * x1072, x1076 * x1088, 0, negate (sin x1079) * (x1080 * x1090 + x1080 * x1090 + x1085 * x1086 + x1085 * x1086) + cos x1079 * (-1.0 * ((x1080 * x1085 + x1080 * x1085) * x1074))]) [x843] [rreplicate 22 x842, v851, v849, rreplicate 22 x845] in let [x856 @Natural @Double @[], v857 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x1095] [x1096, x1097, x1098] -> let x1100 = cos x1098 in [x1095 + x1096, recip (x1100 * x1100) * x1095]) (\\[x1118, x1119, x1120, x1121] [x1122, x1123, x1124, x1125] -> let x1126 = cos x1125 ; x1127 = x1126 * x1126 ; x1128 = x1121 * negate (sin x1125) in [x1118 + x1119, ((x1128 * x1126 + x1128 * x1126) * negate (recip (x1127 * x1127))) * x1122 + x1118 * recip x1127]) (\\[x1140, x1141] [x1142, x1143, x1144, x1145] -> let x1146 = cos x1145 ; x1147 = x1146 * x1146 ; x1148 = negate (recip (x1147 * x1147)) * (x1142 * x1141) in [x1140 + recip x1147 * x1141, x1140, 0, negate (sin x1145) * (x1146 * x1148 + x1146 * x1148)]) [0] [v854, v848, rreplicate 22 x845] in [x853, rsum v857 + rsum v855, x856]) [1.0] [v11, rreplicate 11 1.1] in [rsum v13 + x12]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyAstHVector5
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 2_202

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyAstHVector5
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 23_013

testSin0FoldNestedR2LengthPPs :: Assertion
testSin0FoldNestedR2LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 -> x3 + tan a3)
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector5
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 281_403

testSin0FoldNestedR3LengthPPs :: Assertion
testSin0FoldNestedR3LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 ->
                   rfold (\x4 a4 -> x4 + tan a4)
                         a3 (rreplicate 2 x3))
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector5
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 4_089_691

-- Takes 45s.
_testSin0FoldNestedR4LengthPPs :: Assertion
_testSin0FoldNestedR4LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
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
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector5
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 0

--- Uses 30G in GHC 9.8.1 with -O1 and patchy specialization.
_testSin0FoldNestedR5LengthPPs :: Assertion
_testSin0FoldNestedR5LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
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
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector5
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 0

testSin0MapAccumNestedR1PP :: Assertion
testSin0MapAccumNestedR1PP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 -> let y = rfromD @Double @0 $ x2 V.! 0
                                    w = rfromD @Double @0 $ a2 V.! 0
                                in dmkHVector $ V.singleton
                                   $ DynamicRanked $ y + tan w)
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector5
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x16] [x17] -> let [x21 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\[x26] [x27] -> [x26 + tan x27]) (\\[x39, x40] [x41, x42] -> let x44 = cos x42 in [x39 + x40 * recip (x44 * x44)]) (\\[x52] [x53, x54] -> let x56 = cos x54 in [x52, recip (x56 * x56) * x52]) [x17] [rreplicate 2 x16] in [x21, x16]) (\\[x61, x62] [x63, x64] -> let [x81 @Natural @Double @[]] = let [x78 @Natural @Double @[], v79 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x86] [x87] -> [x86 + tan x87, x86]) (\\[x99, x100] [x101, x102] -> let x113 = cos x102 in [x99 + x100 * recip (x113 * x113), x99]) (\\[x122, x123] [x124, x125] -> let x134 = cos x125 in [x122 + x123, recip (x134 * x134) * x122]) [x64] [rreplicate 2 x63] in let [x80 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\[x143] [x144, x145, x146] -> let x149 = cos x146 in [x143 + x144 * recip (x149 * x149)]) (\\[x175, x176, x177, x178] [x179, x180, x181, x182] -> let x186 = cos x182 ; x187 = x186 * x186 ; x188 = x178 * negate (sin x182) in [x175 + x176 * recip x187 + ((x188 * x186 + x188 * x186) * negate (recip (x187 * x187))) * x180]) (\\[x204] [x205, x206, x207, x208] -> let x212 = cos x208 ; x213 = x212 * x212 ; x214 = negate (recip (x213 * x213)) * (x206 * x204) in [x204, recip x213 * x204, 0, negate (sin x208) * (x212 * x214 + x212 * x214)]) [x62] [rreplicate 2 x61, v79, rreplicate 2 x63] in [x80] in [x81, x61]) (\\[x219, x220] [x221, x222] -> let [x241 @Natural @Double @[], x242 @Natural @Double @[]] = let [x237 @Natural @Double @[], v238 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x247] [x248] -> [x247 + tan x248, x247]) (\\[x260, x261] [x262, x263] -> let x274 = cos x263 in [x260 + x261 * recip (x274 * x274), x260]) (\\[x283, x284] [x285, x286] -> let x295 = cos x286 in [x283 + x284, recip (x295 * x295) * x283]) [x222] [rreplicate 2 x221] in let [x239 @Natural @Double @[], v240 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x302] [x303, x304] -> let x307 = cos x304 in [x302, recip (x307 * x307) * x302]) (\\[x328, x329, x330] [x331, x332, x333] -> let x337 = cos x333 ; x338 = x337 * x337 ; x339 = x330 * negate (sin x333) in [x328, ((x339 * x337 + x339 * x337) * negate (recip (x338 * x338))) * x331 + x328 * recip x338]) (\\[x355, x356] [x357, x358, x359] -> let x363 = cos x359 ; x364 = x363 * x363 ; x365 = negate (recip (x364 * x364)) * (x357 * x356) in [recip x364 * x356 + x355, 0, negate (sin x359) * (x363 * x365 + x363 * x365)]) [x219] [v238, rreplicate 2 x221] in [rsum v240, x239] in [x241 + x220, x242]) [1.1] [rreplicate 2 1.1] in let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x369] [x370, x371] -> let [x376 @Natural @Double @[], v377 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x382] [x383] -> [x382 + tan x383, x382]) (\\[x388, x389] [x390, x391] -> let x393 = cos x391 in [x388 + x389 * recip (x393 * x393), x388]) (\\[x398, x399] [x400, x401] -> let x403 = cos x401 in [x398 + x399, recip (x403 * x403) * x398]) [x371] [rreplicate 2 x370] in let [x378 @Natural @Double @[], v379 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x407] [x408, x409] -> let x411 = cos x409 in [x407, recip (x411 * x411) * x407]) (\\[x418, x419, x420] [x421, x422, x423] -> let x427 = cos x423 ; x428 = x427 * x427 ; x429 = x420 * negate (sin x423) in [x418, ((x429 * x427 + x429 * x427) * negate (recip (x428 * x428))) * x421 + x418 * recip x428]) (\\[x435, x436] [x437, x438, x439] -> let x443 = cos x439 ; x444 = x443 * x443 ; x445 = negate (recip (x444 * x444)) * (x437 * x436) in [recip x444 * x436 + x435, 0, negate (sin x439) * (x443 * x445 + x443 * x445)]) [x369] [v377, rreplicate 2 x370] in [rsum v379, x378]) (\\[x476, x477, x478] [x479, x480, x481] -> let [x482 @Natural @Double @[], v483 @Natural @Double @[2], v484 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x494] [x495] -> [x494 + tan x495, x494, x494]) (\\[x504, x505] [x506, x507] -> let x516 = cos x507 in [x504 + x505 * recip (x516 * x516), x504, x504]) (\\[x522, x523, x524] [x525, x526] -> let x535 = cos x526 in [x523 + x522 + x524, recip (x535 * x535) * x522]) [x481] [rreplicate 2 x480] in let [x485 @Natural @Double @[], v486 @Natural @Double @[2], v487 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x539] [x540, x541] -> let x549 = cos x541 in [x539, x539, recip (x549 * x549) * x539]) (\\[x556, x557, x558] [x559, x560, x561] -> let x576 = cos x561 ; x577 = x576 * x576 ; x578 = x558 * negate (sin x561) in [x556, x556, ((x578 * x576 + x578 * x576) * negate (recip (x577 * x577))) * x559 + x556 * recip x577]) (\\[x585, x586, x587] [x588, x589, x590] -> let x605 = cos x590 ; x606 = x605 * x605 ; x607 = negate (recip (x606 * x606)) * (x588 * x587) in [x586 + recip x606 * x587 + x585, 0.0, negate (sin x590) * (x605 * x607 + x605 * x607)]) [x479] [v484, rreplicate 2 x480] in let [x488 @Natural @Double @[], v489 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x612] [x613, x614, x615] -> let x617 = cos x615 in [x612 + x613 * recip (x617 * x617), x612]) (\\[x635, x636, x637, x638] [x639, x640, x641, x642] -> let x643 = cos x642 ; x644 = x643 * x643 ; x645 = x638 * negate (sin x642) in [x635 + x636 * recip x644 + ((x645 * x643 + x645 * x643) * negate (recip (x644 * x644))) * x640, x635]) (\\[x657, x658] [x659, x660, x661, x662] -> let x663 = cos x662 ; x664 = x663 * x663 ; x665 = negate (recip (x664 * x664)) * (x660 * x657) in [x657 + x658, recip x664 * x657, 0, negate (sin x662) * (x663 * x665 + x663 * x665)]) [x478] [rreplicate 2 x477, v483, rreplicate 2 x480] in let [x490 @Natural @Double @[], v491 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x672] [x673, x674, x675, x676, x677] -> let x681 = cos x677 ; x682 = x681 * x681 ; x683 = x674 * negate (sin x677) in [x672, ((x683 * x681 + x683 * x681) * negate (recip (x682 * x682))) * x675 + x672 * recip x682]) (\\[x724, x725, x726, x727, x728, x729] [x730, x731, x732, x733, x734, x735] -> let x736 = cos x735 ; x737 = x736 * x736 ; x738 = negate (sin x735) ; x739 = x732 * x738 ; x740 = x737 * x737 ; x741 = x739 * x736 + x739 * x736 ; x742 = negate (recip x740) ; x743 = x726 * x738 + ((x729 * cos x735) * -1.0) * x732 ; x744 = x729 * negate (sin x735) ; x745 = x744 * x736 + x744 * x736 in [x724, ((x743 * x736 + x744 * x739 + x743 * x736 + x744 * x739) * x742 + (((x745 * x737 + x745 * x737) * negate (recip (x740 * x740))) * -1.0) * x741) * x733 + x727 * (x741 * x742) + x724 * recip x737 + (x745 * negate (recip (x737 * x737))) * x730]) (\\[x771, x772] [x773, x774, x775, x776, x777, x778] -> let x779 = cos x778 ; x780 = x779 * x779 ; x781 = negate (sin x778) ; x782 = x775 * x781 ; x783 = x780 * x780 ; x784 = x782 * x779 + x782 * x779 ; x785 = negate (recip x783) ; x786 = x776 * x772 ; x787 = negate (recip (x783 * x783)) * (-1.0 * (x784 * x786)) ; x788 = x785 * x786 ; x789 = x779 * x788 + x779 * x788 ; x790 = x780 * x787 + x780 * x787 + negate (recip (x780 * x780)) * (x773 * x772) in [recip x780 * x772 + x771, 0, x781 * x789, (x784 * x785) * x772, 0, negate (sin x778) * (x779 * x790 + x779 * x790 + x782 * x788 + x782 * x788) + cos x778 * (-1.0 * (x775 * x789))]) [x476] [v489, rreplicate 2 x477, v486, v484, rreplicate 2 x480] in [rsum v491, x490]) (\\[x814, x815] [x816, x817, x818] -> let [x819 @Natural @Double @[], v820 @Natural @Double @[2], v821 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x832] [x833] -> [x832 + tan x833, x832, x832]) (\\[x842, x843] [x844, x845] -> let x854 = cos x845 in [x842 + x843 * recip (x854 * x854), x842, x842]) (\\[x860, x861, x862] [x863, x864] -> let x873 = cos x864 in [x861 + x860 + x862, recip (x873 * x873) * x860]) [x818] [rreplicate 2 x817] in let [x822 @Natural @Double @[], v823 @Natural @Double @[2], v824 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x877] [x878, x879] -> let x887 = cos x879 in [x877, x877, recip (x887 * x887) * x877]) (\\[x894, x895, x896] [x897, x898, x899] -> let x914 = cos x899 ; x915 = x914 * x914 ; x916 = x896 * negate (sin x899) in [x894, x894, ((x916 * x914 + x916 * x914) * negate (recip (x915 * x915))) * x897 + x894 * recip x915]) (\\[x923, x924, x925] [x926, x927, x928] -> let x943 = cos x928 ; x944 = x943 * x943 ; x945 = negate (recip (x944 * x944)) * (x926 * x925) in [x924 + recip x944 * x925 + x923, 0.0, negate (sin x928) * (x943 * x945 + x943 * x945)]) [x816] [v821, rreplicate 2 x817] in let [x825 @Natural @Double @[], v826 @Natural @Double @[2], v827 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x951] [x952, x953, x954, x955] -> let x959 = cos x955 ; x960 = x959 * x959 ; x961 = negate (recip (x960 * x960)) * (x953 * x952) in [recip x960 * x952 + x951, 0, negate (sin x955) * (x959 * x961 + x959 * x961)]) (\\[x1000, x1001, x1002, x1003, x1004] [x1005, x1006, x1007, x1008, x1009] -> let x1010 = cos x1009 ; x1011 = x1010 * x1010 ; x1012 = x1011 * x1011 ; x1013 = negate (recip x1012) ; x1014 = x1007 * x1006 ; x1015 = x1013 * x1014 ; x1016 = x1004 * negate (sin x1009) ; x1017 = x1016 * x1010 + x1016 * x1010 ; x1018 = (((x1017 * x1011 + x1017 * x1011) * negate (recip (x1012 * x1012))) * -1.0) * x1014 + (x1002 * x1006 + x1001 * x1007) * x1013 in [x1000 + (x1017 * negate (recip (x1011 * x1011))) * x1006 + x1001 * recip x1011, 0.0, ((x1004 * cos x1009) * -1.0) * (x1010 * x1015 + x1010 * x1015) + (x1016 * x1015 + x1018 * x1010 + x1016 * x1015 + x1018 * x1010) * negate (sin x1009)]) (\\[x1044, x1045, x1046] [x1047, x1048, x1049, x1050, x1051] -> let x1052 = cos x1051 ; x1053 = x1052 * x1052 ; x1054 = x1053 * x1053 ; x1055 = negate (recip x1054) ; x1056 = x1049 * x1048 ; x1057 = x1055 * x1056 ; x1058 = negate (sin x1051) * x1046 ; x1059 = x1052 * x1058 + x1052 * x1058 ; x1060 = x1055 * x1059 ; x1061 = negate (recip (x1054 * x1054)) * (-1.0 * (x1056 * x1059)) ; x1062 = x1053 * x1061 + x1053 * x1061 + negate (recip (x1053 * x1053)) * (x1048 * x1044) in [x1044, x1049 * x1060 + recip x1053 * x1044, x1048 * x1060, 0, negate (sin x1051) * (x1052 * x1062 + x1052 * x1062 + x1057 * x1058 + x1057 * x1058) + cos x1051 * (-1.0 * ((x1052 * x1057 + x1052 * x1057) * x1046))]) [x815] [rreplicate 2 x814, v823, v821, rreplicate 2 x817] in let [x828 @Natural @Double @[], v829 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x1067] [x1068, x1069, x1070] -> let x1072 = cos x1070 in [x1067 + x1068, recip (x1072 * x1072) * x1067]) (\\[x1090, x1091, x1092, x1093] [x1094, x1095, x1096, x1097] -> let x1098 = cos x1097 ; x1099 = x1098 * x1098 ; x1100 = x1093 * negate (sin x1097) in [x1090 + x1091, ((x1100 * x1098 + x1100 * x1098) * negate (recip (x1099 * x1099))) * x1094 + x1090 * recip x1099]) (\\[x1112, x1113] [x1114, x1115, x1116, x1117] -> let x1118 = cos x1117 ; x1119 = x1118 * x1118 ; x1120 = negate (recip (x1119 * x1119)) * (x1114 * x1113) in [x1112 + recip x1119 * x1113, x1112, 0, negate (sin x1117) * (x1118 * x1120 + x1118 * x1120)]) [0] [v826, v820, rreplicate 2 x817] in [x825, rsum v829 + rsum v827, x828]) [1.0] [v11, rreplicate 2 1.1] in [rsum v13 + x12]"

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 -> let y = rfromD @Double @0 $ x4 V.! 0
                                        w = rfromD @Double @0 $ a4 V.! 0
                                    in dmkHVector $ V.singleton
                                       $ DynamicRanked $ y + tan w)
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector5
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 4093136

testSin0MapAccumNestedR4 :: Assertion
testSin0MapAccumNestedR4 = do
 assertEqualUpToEpsilon' 1e-10
  (1.0410225027528066 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 -> let y = rfromD @Double @0 $ x5 V.! 0
                                          w = rfromD @Double @0 $ a5 V.! 0
                                      in dmkHVector $ V.singleton
                                         $ DynamicRanked $ 0.01 * y + tan w)
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001)

-- Takes 200s, probably due to some of the pipelines forcing all derivs.
_testSin0MapAccumNestedR5 :: Assertion
_testSin0MapAccumNestedR5 = do
 assertEqualUpToEpsilon' 1e-10
  (2.2173831481990922e20 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in dmkHVector $ V.singleton
                                           $ DynamicRanked $ y + tan w)
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 1.1)

testSin0MapAccumNestedR5r :: Assertion
testSin0MapAccumNestedR5r = do
 assertEqualUpToEpsilon 1e-10
  (1.0837278549794862 :: Flip OR.Array Double 0)
  (rev @_ @_ @(AstRanked FullSpan)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in dmkHVector $ V.singleton
                                           $ DynamicRanked $ 0.01 * y + tan w)
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001)

testSin0MapAccumNestedR10r :: Assertion
testSin0MapAccumNestedR10r = do
 assertEqualUpToEpsilon 1e-10
  (1.379370673816781 :: Flip OR.Array Double 0)
  (rev @_ @_ @(AstRanked FullSpan)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ 0.01 * y + tan w)
                                       (dmkHVector a10) (mkreplicate1HVector (SNat @2) x10))
                                     (dmkHVector a9) (mkreplicate1HVector (SNat @2) x9))
                                   (dmkHVector a8) (mkreplicate1HVector (SNat @2) x8))
                                 (dmkHVector a7) (mkreplicate1HVector (SNat @2) x7))
                               (dmkHVector a6) (mkreplicate1HVector (SNat @2) x6))
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001)

testSin0MapAccumNestedR10f :: Assertion
testSin0MapAccumNestedR10f = do
 assertEqualUpToEpsilon 1e-10
  (1.379370673816781e-4 :: Flip OR.Array Double 0)
  (fwd @(AstRanked FullSpan Double 0)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ 0.01 * y + tan w)
                                       (dmkHVector a10) (mkreplicate1HVector (SNat @2) x10))
                                     (dmkHVector a9) (mkreplicate1HVector (SNat @2) x9))
                                   (dmkHVector a8) (mkreplicate1HVector (SNat @2) x8))
                                 (dmkHVector a7) (mkreplicate1HVector (SNat @2) x7))
                               (dmkHVector a6) (mkreplicate1HVector (SNat @2) x6))
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001 0.0001)

testSin0MapAccumNestedR10fN :: Assertion
testSin0MapAccumNestedR10fN = do
 assertEqualUpToEpsilon 1e-10
  ( 1.379370673816781e-4 :: Flip OS.Array Float '[1]
  , 1.379370673816781e-4 :: Flip OR.Array Double 0)
  (fwd @(AstShaped FullSpan Float '[1], AstRanked FullSpan Double 0)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      g :: forall f. ADReady f => f Double 0 -> f Double 0
      g z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ 0.01 * y + tan w)
                                       (dmkHVector a10) (mkreplicate1HVector (SNat @2) x10))
                                     (dmkHVector a9) (mkreplicate1HVector (SNat @2) x9))
                                   (dmkHVector a8) (mkreplicate1HVector (SNat @2) x8))
                                 (dmkHVector a7) (mkreplicate1HVector (SNat @2) x7))
                               (dmkHVector a6) (mkreplicate1HVector (SNat @2) x6))
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      f :: forall f. ADReady f => f Double 0
        -> (ShapedOf f Float '[1], f Double 0)
      f x = (sfromList [scast $ sfromR $ g x], g x + 0.2)
    in f) 0.0001 0.0001)

testSin0MapAccumNestedR10rf :: Assertion
testSin0MapAccumNestedR10rf = do
 assertEqualUpToEpsilon 1e-10
  (1.2264611684496617e-2 :: Flip OR.Array Double 0)
  (rev @_ @_ @(AstRanked FullSpan)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ 0.01 * y + tan w)
                                       (dmkHVector a10) (mkreplicate1HVector (SNat @2) x10))
                                     (dmkHVector a9) (mkreplicate1HVector (SNat @2) x9))
                                   (dmkHVector a8) (mkreplicate1HVector (SNat @2) x8))
                                 (dmkHVector a7) (mkreplicate1HVector (SNat @2) x7))
                               (dmkHVector a6) (mkreplicate1HVector (SNat @2) x6))
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rfwd1 f) 0.0001)

testSin0MapAccumNestedR10rr :: Assertion
testSin0MapAccumNestedR10rr = do
 assertEqualUpToEpsilon 1e-10
  (1.2264611684496617e-2 :: Flip OR.Array Double 0)
  (rev @_ @_ @(AstRanked FullSpan)
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = V.singleton sh1
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ dmapAccumL (Proxy @f) (SNat @2) shs1 V.empty shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                         (\x4 a4 ->
                     dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                           (\x5 a5 ->
                       dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                             (\x6 a6 ->
                         dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                               (\x7 a7 ->
                           dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                 (\x8 a8 ->
                             dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                   (\x9 a9 ->
                               dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                     (\x10 a10 ->
                                 dmapAccumL Proxy (SNat @2) shs1 V.empty shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ 0.01 * y + tan w)
                                       (dmkHVector a10) (mkreplicate1HVector (SNat @2) x10))
                                     (dmkHVector a9) (mkreplicate1HVector (SNat @2) x9))
                                   (dmkHVector a8) (mkreplicate1HVector (SNat @2) x8))
                                 (dmkHVector a7) (mkreplicate1HVector (SNat @2) x7))
                               (dmkHVector a6) (mkreplicate1HVector (SNat @2) x6))
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rrev1 f) 0.0001)

testSin0FoldNestedS1FwdFwd0 :: Assertion
testSin0FoldNestedS1FwdFwd0 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . sfwd1 f . sfromR) 1.1)

testSin0FoldNestedS1FwdFwd :: Assertion
testSin0FoldNestedS1FwdFwd = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * sfwd1 (sfwd1 (\b2 -> 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfwd1 $ rfromS . sfwd1 f . sfromR) 1.1)

testSin0FoldNestedS1RevRev :: Assertion
testSin0FoldNestedS1RevRev = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * srev1 (srev1 (\b2 -> 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rrev1 $ rfromS . srev1 f . sfromR) 1.1)

testSin0FoldNestedS2 :: Assertion
testSin0FoldNestedS2 = do
  assertEqualUpToEpsilon' 1e-10
    (3.175389686661287e-207 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 -> 0.7 * x3 * a3)
                                a2 (sreplicate @_ @4 x2))
                              a (sreplicate @_ @3 x))
                            a0 (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedS3 :: Assertion
testSin0FoldNestedS3 = do
  assertEqualUpToEpsilon' 1e-10
    (7.320500000000004e-4 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 -> 0.1 * x4 * a4)
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @2 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedS4 :: Assertion
testSin0FoldNestedS4 = do
  assertEqualUpToEpsilon' 1e-10
    (1.2400927000000009e-5 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 -> 0.1 * x5 * a5)
                                    a4 (sreplicate @_ @2 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @2 x))
                            a0 (sreplicate @_ @1 a0)
           in rfromS . f . sfromR) 1.1)

-- Takes at least 60G of RAM.
_testSin0FoldNestedS5 :: Assertion
_testSin0FoldNestedS5 = do
  assertEqualUpToEpsilon' 1e-10
    (0.22000000000000003 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)

           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedS5rev :: Assertion
testSin0FoldNestedS5rev = do
  let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
      f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)
  assertEqualUpToEpsilon 1e-10
    0.22000000000000003
    (srev1 @(Flip OS.Array) @Double @'[] @'[] f 1.1)

testSin0FoldNestedS5fwd :: Assertion
testSin0FoldNestedS5fwd = do
  let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
      f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                          sfold (\x3 a3 ->
                            sfold (\x4 a4 ->
                              sfold (\x5 a5 ->
                                sfold (\x6 a6 -> 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)
  assertEqualUpToEpsilon 1e-10
    0.22000000000000003
    (sfwd1 @(Flip OS.Array) @Double @'[] @'[] f 1.1)

testSin0FoldNestedSi :: Assertion
testSin0FoldNestedSi = do
  assertEqualUpToEpsilon' 1e-10
    (-0.20775612781643243 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[3]
               f a0 = sfold (\x a -> atan2
                                       (sscan (+) (ssum x)
                                          (sscan (*) 2
                                                 (sreplicate @_ @1 a)))
                                       (sscan (\x1 a1 ->
                                          sfold (\x2 a2 ->
                                            sfold (\x3 a3 ->
                                                     0.001 * (x3 * a3 - x3))
                                                  a2 (sscan (+) x2
                                                        (sreplicate @_ @3 a2)))
                                                x1 (sreplicate @_ @1 a1))
                                              a (sscan (-) 0
                                                   (sslice (Proxy @0)
                                                           (Proxy @1) x))))
                            (sreplicate @_ @3 $ 2 * a0) (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedR1 :: Assertion
testSin0FoldNestedR1 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 -> 0.7 * x2 * a2)
                              a (rreplicate 7 x))
                            a0 (rreplicate 3 a0)
           in f) 1.1)

testSin0FoldNestedR1RevFwd :: Assertion
testSin0FoldNestedR1RevFwd = do
  assertEqualUpToEpsilon' 1e-10
    (3.175389686661287e-207 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                                 x2 * rfwd1 (rrev1 (\b2 -> 0.7 * b2)) a2)
                              a (rreplicate 4 x))
                            a0 (rreplicate 2 a0)
           in rrev1 $ rfwd1 f) 1.1)

testSin0FoldNestedR2 :: Assertion
testSin0FoldNestedR2 = do
  assertEqualUpToEpsilon' 1e-10
    (3.175389686661287e-207 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 -> 0.7 * x3 * a3)
                                a2 (rreplicate 4 x2))
                              a (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR2RevFwd :: Assertion
testSin0FoldNestedR2RevFwd = do
  assertEqualUpToEpsilon' 1e-10
    (3.175389686661287e-207 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                                   x3 * rrev1 (rfwd1 (rrev1 (\b3 ->
                                                               0.7 * b3))) a3)
                                a2 (rreplicate 4 x2))
                              a (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in rfwd1 $ rrev1 $ rfwd1 f) 1.1)

testSin0FoldNestedR3 :: Assertion
testSin0FoldNestedR3 = do
  assertEqualUpToEpsilon' 1e-10
    (7.320500000000004e-4 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 -> 0.1 * x4 * a4)
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 2 x2))
                              a (rreplicate 1 x))
                            a0 (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR4 :: Assertion
testSin0FoldNestedR4 = do
  assertEqualUpToEpsilon' 1e-10
    (1.2400927000000009e-5 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> 0.1 * x5 * a5)
                                    a4 (rreplicate 2 x4))
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 1 x2))
                              a (rreplicate 2 x))
                            a0 (rreplicate 1 a0)
           in f) 1.1)

testSin0FoldNestedR41 :: Assertion
testSin0FoldNestedR41 = do
  assertEqualUpToEpsilon' 1e-10
    (0.22000000000000003 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> 0.1 * x5 * a5)
                                    a4 (rreplicate 1 x4))
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 1 x2))
                              a (rreplicate 1 x))
                            a0 (rreplicate 1 a0)
           in f) 1.1)

testSin0FoldNestedR40 :: Assertion
testSin0FoldNestedR40 = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 ->
                            rfold (\x4 a4 ->
                              rfold (\x5 a5 -> 0.1 * x5 * a5)
                                    a4 (rreplicate 0 x4))
                                  a3 (rreplicate 0 x3))
                                a2 (rreplicate 0 x2))
                              a (rreplicate 0 x))
                            a0 (rreplicate 0 a0)
           in f) 1.1)

testSin0FoldNestedR400 :: Assertion
testSin0FoldNestedR400 = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
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
           in f) 1.1)

testSin0FoldNestedRi :: Assertion
testSin0FoldNestedRi = do
  assertEqualUpToEpsilon' 1e-10
    (-0.20775612781643243 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 1
               f a0 = rfold (\x a -> atan2
                                       (rscan (+) (rsum x)
                                          (rscan (*) 2
                                                 (rreplicate 1 a)))
                                       (rscan (\x1 a1 ->
                                          rfold (\x2 a2 ->
                                            rfold (\x3 a3 ->
                                                     0.001 * (x3 * a3 - x3))
                                                  a2 (rscan (+) x2
                                                            (rreplicate 3 a2)))
                                                x1 (rreplicate 1 a1))
                                              a (rscan (-) 0 (rslice 0 1 x))))
                            (rreplicate 3 $ 2 * a0) (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR22 :: Assertion
testSin0FoldNestedR22 = do
  assertEqualUpToEpsilon' 1e-10
    (2.877421010384167e-5 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 -> 0.44 * x3 * a3)
                                a2 (rscan (\x4 a4 -> x4 + a4) x2
                                          (rreplicate 2 a2)))
                              (rfold (\x4 a4 -> x4 * a4) a
                                     (rreplicate 2 x)) (rreplicate 3 x))
                            a0 (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR21 :: Assertion
testSin0FoldNestedR21 = do
  assertEqualUpToEpsilon' 1e-10
    (7.667553331540788e-3 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a -> rlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR21PP :: Assertion
testSin0FoldNestedR21PP = do
  resetVarCounter
  let a1 =
        rrev1 @(AstRanked FullSpan) @Double @0 @0
          (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a -> rlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) 1.1
  length (printAstSimple IM.empty (simplifyAst6 a1))
    @?= 52643

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZSR))
             x
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 0.4535961214255773)
    (f @(Flip OR.Array) (V.singleton $ DynamicRanked @Double @0 1.1))

testSin0revhVPP :: Assertion
testSin0revhVPP = do
  resetVarCounter
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZSR))
             x
  printAstHVectorSimple IM.empty (f @(AstRanked FullSpan)
                                    (V.singleton
                                     $ DynamicRanked @Double @0 1.1))
    @?= "dmkHVector (fromList [DynamicRanked (cos (rconstant 1.1) * rconstant 1.0)])"

testSin0revhV2 :: Assertion
testSin0revhV2 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZSR))
             x
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (-0.8912073600614354))
    (crev (h @(Flip OR.Array)) (V.singleton $ DynamicRanked @Double @0 1.1))

testSin0revhV3 :: Assertion
testSin0revhV3 = do
  let f :: forall g. ADReady g
        => HVector g -> HVectorOf g
      f x =
        srev @g @_ @Double @'[] (\v -> sin (sfromD $ v V.! 0))
             (V.singleton (voidFromShS @Double @'[]))
             x
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[] (-0.8912073600614354))
    (crev (h @(Flip OR.Array)) (V.singleton $ DynamicShaped @Double @'[] 1.1))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (HVectorTensor g (ShapedOf g), RankedTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1 (rscanZip const doms 5)
               doms3 x (rfromList [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [0, 0, 0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 1.1))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (HVectorTensor g (ShapedOf g), ShapedTensor (ShapedOf g))
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4] (sscanZip const doms 5)
               doms3 x (sfromList [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList [0, 0, 0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (HVectorTensor g (ShapedOf g), RankedTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1
               (\v -> rscanZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 v)
                doms3 x (rfromList [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [4.0,6.0,8.0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 1.1))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (HVectorTensor g (ShapedOf g), ShapedTensor (ShapedOf g))
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4]
               (\v -> sscanZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms 5 v)
               doms3 x (sfromList [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList [4.0,6.0,8.0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1))

testSin0revhV8 :: Assertion
testSin0revhV8 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f = dmkHVector
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList @(Flip OS.Array) [1, 1, 1])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3]
           $ sreplicate @(Flip OS.Array) @3 1.1))

fFoldZipR
  :: forall n r ranked.
     (KnownNat n, GoodScalar r, ADReady ranked)
  => VoidHVector
  -> ranked r (1 + n)
  -> HVector ranked
  -> (forall f. ADReady f
      => f r n -> f r n -> HVector f
      -> HVectorOf f)
  -> ShapeInt n
  -> ranked r n
  -> HVectorOf ranked
fFoldZipR domsOD p as rf shn cShared =
  let width = case V.unsnoc as of
        Nothing ->
          error "testSin0FoldZipR: can't determine argument width"
        Just (_, d) -> case shapeDynamic d of
          [] -> error "testSin0FoldZipR: wrong rank of argument"
          w : _shm -> w
      !_A1 = assert (rlength p == width + 1) ()
      odShn = voidFromSh @r shn
      domsF = V.cons odShn domsOD
      domsToPair :: forall f. ADReady f
                 => HVector f -> (f r n, HVector f)
      domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
      domsTo3 :: ADReady f
              => HVector f -> (f r n, f r n, HVector f)
      domsTo3 doms = ( rfromD $ doms V.! 0
                     , rfromD $ doms V.! 1
                     , V.drop 2 doms )
      lp = rreverse $ rslice 0 width p
      las :: HVector ranked
      las = mapHVectorRanked11 rreverse as
      crsr :: ranked r (1 + n)
      crsr =
        rscanZip
          (\cr doms ->
              let (x, a) = domsToPair doms
              in rletHVectorIn (rf cr x a) $ \rfRes ->
                   fst (domsToPair rfRes))
          domsF
          cShared
          (V.cons (DynamicRanked lp) las)
      crs = rreverse crsr
      rg :: ranked r (1 + n) -> ranked r (1 + n)
         -> HVector ranked
         -> HVectorOf ranked
      rg cr2 x2 a2 = withSNat width $ \k ->
        dzipWith1 k
                  (\doms ->
                     let (cr, x, a) = domsTo3 doms
                     in dletHVectorInHVector
                          (rf cr x a) $ \rfRes ->
                            dmkHVector $ snd $ domsToPair rfRes)
                  (V.cons (DynamicRanked cr2)
                   $ V.cons (DynamicRanked x2) a2)
      cas = rg (rslice 1 width crs)
               (rslice 0 width p)
               as
  in cas

fFoldZipRX :: forall ranked. ADReady ranked
  => HVector ranked
  -> HVectorOf ranked
fFoldZipRX as =
  let f :: forall f. ADReady f => f Double 0 -> HVector f -> f Double 0
      f _t v = sin (rfromD (v V.! 1)) * rfromD (v V.! 1)
      doms = V.fromList [ voidFromSh @Double ZSR
                        , voidFromSh @Double ZSR ]
      p :: ranked Double 1
      p = rscanZip f doms 7 as
      rf :: forall f. ADReady f
         => f Double 0 -> f Double 0 -> HVector f -> HVectorOf f
      rf _x _y = rrev @f (f 42) doms  -- not exactly the rev of f
  in fFoldZipR doms p as rf ZSR 26

testSin0revhFoldZipR :: Assertion
testSin0revhFoldZipR = do
  let h :: ranked ~ Flip OR.Array
        => HVector (ADVal ranked)
        -> ADVal (HVectorPseudoTensor ranked) Float '()
      h = hVectorADValToADVal . fFoldZipRX @(ADVal (Flip OR.Array))
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [0, 0, 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (-7.313585321642452e-2) ])
    (crev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 1.1
                        , DynamicRanked @Double @1 $ rreplicate 3 1.1 ]))

testSin0revhFoldZip4R :: Assertion
testSin0revhFoldZip4R = do
  let g :: ADReady ranked
        => HVector ranked
        -> HVectorPseudoTensor ranked Float '()
      g = HVectorPseudoTensor . fFoldZipRX
      h :: HVector (AstRanked FullSpan)
        -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
      h = g @(AstRanked FullSpan)
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [0, 0, 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (-7.313585321642452e-2) ])
    (rev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 1.1
                       , DynamicRanked @Double @1 $ rreplicate 3 1.1 ]))

fFoldS
  :: forall m k rm shm r sh shaped.
     ( KnownNat k, GoodScalar rm, Sh.Shape shm, GoodScalar r, Sh.Shape sh
     , ADReadyS shaped, KnownNat m, OS.Rank shm ~ m)
  => shaped r (1 + k ': sh)
  -> shaped rm (k ': shm)
  -> (forall f. ADReadyS f
      => f r sh -> f r sh -> f rm shm -> HVectorOf (RankedOf f))
  -> shaped r sh
  -> shaped rm (k ': shm)
fFoldS p as rf cShared =
  let domsF = V.fromList [voidFromShS @r @sh, voidFromShS @rm @shm]
      domsToPair :: ADReadyS f
                 => HVector (RankedOf f) -> (f r sh, f rm shm)
      domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
      crsr :: shaped r (1 + k ': sh)
      crsr =
        sscanZip (\cr doms ->
                    let (x, a) = domsToPair doms
                    in sletHVectorIn
                         (rf cr x a) $ \rfRes ->
                           fst (domsToPair rfRes))
               domsF
               cShared
               (V.fromList
                  [ DynamicShaped $ sreverse
                    $ sslice @_ @_ @_ @_ @1
                             (Proxy @0) (Proxy @k) p
                  , DynamicRanked $ rfromS $ sreverse as ])
      crs = sreverse crsr
      rg :: shaped r (k ': sh) -> shaped r (k ': sh)
         -> shaped rm (k ': shm)
         -> shaped rm (k ': shm)
      rg = szipWith31 (\cr x a ->
                         sletHVectorIn (rf cr x a) $ \rfRes ->
                           snd $ domsToPair rfRes)
      cas = rg (sslice @_ @_ @_ @_ @0
                       (Proxy @1) (Proxy @k) crs)
               (sslice @_ @_ @_ @_ @1
                       (Proxy @0) (Proxy @k) p)
               as
  in cas

fFoldSX
  :: forall shaped. ADReadyS shaped
  => shaped Double '[3] -> shaped Double '[3]
fFoldSX as =
  let f :: forall f. ADReadyS f
        => f Double '[] -> f Double '[] -> f Double '[]
      f _t v = sin v * v
      doms = V.fromList [ voidFromShS @Double @'[]
                        , voidFromShS @Double @'[] ]
      p :: shaped Double '[4]
      p = sscan f 7 as
      rf :: forall f. ADReadyS f
         => f Double '[] -> f Double '[] -> f Double '[]
         -> HVectorOf (RankedOf f)
      rf _x _y z = srev @_ @f (\v -> f 42 (sfromD (v V.! 1)))
                        doms (V.fromList [ DynamicShaped @Double @'[] z
                                         , DynamicShaped @Double @'[] z ])
                     -- not exactly the rev of f
  in fFoldS @0 p as rf 26

testSin0revhFoldS :: Assertion
testSin0revhFoldS = do
  assertEqualUpToEpsilon 1e-10
    (sreplicate @_ @3 (-7.313585321642452e-2))
    (rev (fFoldSX @(AstShaped FullSpan))
         (sreplicate @_ @3 1.1))

testSin0revhFold2S :: Assertion
testSin0revhFold2S = do
  assertEqualUpToEpsilon' 1e-10
    (runFlip $ rreplicate 3 (-7.313585321642452e-2))
    (rev' (rfromS . fFoldSX . sfromR)
          (rreplicate 3 1.1))

testSin0revhFold3S :: Assertion
testSin0revhFold3S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ sfromList [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ sreplicate @_ @3 (-7.313585321642452e-2) ])
    (crev (\(asD :: HVector (ADVal (Flip OR.Array))) ->
             fFoldSX (sfromD (asD V.! 1)))
          (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1
                      , DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1 ]))

testSin0revhFold4S :: Assertion
testSin0revhFold4S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ sfromList [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ sreplicate @_ @3 (-7.313585321642452e-2) ])
    (rev (\(asD :: HVector (AstRanked FullSpan)) ->
             fFoldSX (sfromD (asD V.! 1)))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1 ]))

testSin0revhFold5S :: Assertion
testSin0revhFold5S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ sfromList [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ sreplicate @_ @3 (-7.313585321642452e-2) ])
    (rev @_ @_ @(AstShaped FullSpan)
         (\(asD :: AstHVector FullSpan) ->
            sletHVectorIn asD (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1 ]))
