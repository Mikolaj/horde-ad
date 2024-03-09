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
import HordeAd.Util.ShapedList (ShapedList (..))

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
    @?= "let x13 = sin 2.2 ; x14 = 1.1 * x13 ; x15 = recip (3.3 * 3.3 + x14 * x14) ; x16 = sin 2.2 ; x17 = 1.1 * x16 ; x19 = 3.3 * 1.0 ; x20 = (negate 3.3 * x15) * 1.0 in x13 * x20 + x16 * x19"

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
    0.4989557335681351
    (rfwd1 @(Flip OR.Array) @Double @0 @0 sin 1.1)

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "1.1 * cos 1.1"

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "let [x4 @Natural @Double @[]] = (\\[x1] [x2] -> let x3 = x1 * cos x2 in [x3]) [[1.1], [1.1]] in x4"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let [x4 @Natural @Double @[]] = (\\[x1] [x2] -> [x1 * cos x2]) [[1.1], [1.1]] in x4"

testSin0Rfwd3 :: Assertion
testSin0Rfwd3 = do
  let f = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (-0.5794051721062019)
    (cfwd f 1.1 1.1)

testSin0Rfwd4 :: Assertion
testSin0Rfwd4 = do
  assertEqualUpToEpsilon 1e-10
    0.43812441332801516
    ((rfwd1 sin . rfwd1 @(Flip OR.Array) @Double @0 @0 sin) 1.1)

testSin0RfwdPP4 :: Assertion
testSin0RfwdPP4 = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "(1.1 * cos 1.1) * cos (1.1 * cos 1.1)"

-- Disabled, because different variable names with -O1.
_testSin0RfwdPP4Dual :: Assertion
_testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let [x20 @Natural @Double @[]] = (\\[x17] [x18] -> [x17 * cos x18]) [[let [x16 @Natural @Double @[]] = (\\[x13] [x14] -> [x13 * cos x14]) [[rdualPart 1.1], [rdualPart 1.1]] in x16], [let [x16 @Natural @Double @[]] = (\\[x13] [x14] -> [x13 * cos x14]) [[rdualPart 1.1], [rdualPart 1.1]] in x16]] in x20"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (-0.5794051721062019)
    (rfwd1 @(Flip OR.Array) @Double @0 @0 (rfwd1 sin) 1.1)

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 (rfwd1 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "1.1 * cos 1.1 + (1.1 * negate (sin 1.1)) * 1.1"

testSin0Rfwd3' :: Assertion
testSin0Rfwd3' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.5267319746420018 :: OR.Array 0 Double)
    (rev' (rfwd1 sin) 1.1)

testSin0Rfwd4' :: Assertion
testSin0Rfwd4' = do
  assertEqualUpToEpsilon' 1e-10
    (-0.336754499012933 :: OR.Array 0 Double)
    (rev' (rfwd1 sin . rfwd1 sin) 1.1)

testSin0Rfwd5' :: Assertion
testSin0Rfwd5' = do
  assertEqualUpToEpsilon' 1e-10
    (-3.036239473702109 :: OR.Array 0 Double)
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
                            x0 (rzero @f @Double (0 :$: ZS))
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
    @?= "let [v12 @[Natural] @Double @[5], m13 @[Natural] @Double @[1,5]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1] in let v14 = rconst (fromList [5] [1.0,1.0,1.0,1.0,1.0]) in let [v16 @[Natural] @Double @[5], v17 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sfromR v14] [m13, sreplicate 1.1] in rfromS (sreshape v17) + rfromS (ssum v16)"

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
    (Flip $ OR.constant [2, 5] (-0.242034255165279))
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
    106.39901975715969
    (crev h 1.1)

testSin0Fold8Sfwd :: Assertion
testSin0Fold8Sfwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.constant [2, 5] (-0.242034255165279))
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
    (Flip $ OR.constant [2, 5] 11.703892173287567)
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
                            x0 (rzero @f @Double (0 :$: ZS))
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
    @?= "let v14 = rconst (fromList [2] [42.0,42.0]) in let [x15 @Natural @Double @[], v16 @Natural @Double @[2], v17 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x26] [x27] -> let x34 = sin x26 in [x34, x26, x34]) (\\[x39, x40] [x41, x42] -> let x55 = x39 * cos x41 in [x55, x39, x55]) (\\[x61, x62, x63] [x64, x65] -> [cos x64 * (x63 + x61) + x62, 0.0]) [1.1] [v14] in let v18 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x85] [x86, x87, x88] -> [cos x87 * (x86 + x85), 0]) (\\[x110, x111, x112, x113] [x114, x115, x116, x117] -> [(x112 * negate (sin x116)) * (x115 + x114) + (x111 + x110) * cos x116, 0.0]) (\\[x138, x139] [x140, x141, x142, x143] -> let x148 = cos x142 * x138 in [x148, x148, negate (sin x142) * ((x141 + x140) * x138), 0]) [0.0] [rslice 1 2 v18, v16, v14] in x21 + v18 ! [0]"

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
    @?= "let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x16] [x17] -> let x21 = sin x16 in [x21, x16, x21]) (\\[x24, x25] [x26, x27] -> let x36 = x24 * cos x26 in [x36, x24, x36]) (\\[x39, x40, x41] [x42, x43] -> [cos x42 * (x41 + x39) + x40, 0.0]) [1.1] [v5] in let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x57] [x58, x59, x60] -> let x62 = x57 * cos x59 in [x62, x62]) (\\[x63, x65, x67, x69] [x64, x66, x68, x70] -> let x77 = x63 * cos x68 + (x67 * negate (sin x68)) * x64 in [x77, x77]) (\\[x87, x88] [x78, x79, x80, x81] -> let x91 = x88 + x87 in [cos x80 * x91, 0, negate (sin x80) * (x78 * x91), 0]) [1.1] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.1) v11"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPrettyButNested IM.empty (simplifyAst6 a1)
    @?= "let [v15 @Natural @Double @[3]] = (\\[x1] [x2] -> let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x16] [x17] -> let x21 = sin x16 in [x21, x16, x21]) (\\[x24, x25] [x26, x27] -> let x36 = x24 * cos x26 in [x36, x24, x36]) (\\[x39, x40, x41] [x42, x43] -> [cos x42 * (x41 + x39) + x40, 0.0]) [x2] [v5] in let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x57] [x58, x59, x60] -> let x62 = x57 * cos x59 in [x62, x62]) (\\[x63, x65, x67, x69] [x64, x66, x68, x70] -> let x77 = x63 * cos x68 + (x67 * negate (sin x68)) * x64 in [x77, x77]) (\\[x87, x88] [x78, x79, x80, x81] -> let x91 = x88 + x87 in [cos x80 * x91, 0, negate (sin x80) * (x78 * x91), 0]) [x1] [rreplicate 2 0.0, v7, v5] in [rappend (rreplicate 1 x1) v11]) [[1.1], [1.1]] in v15"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v14 = rconst (fromList [2] [5.0,7.0]) in let [x15 @Natural @Double @[], v16 @Natural @Double @[2], v17 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v14] in let v18 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v18, v16, v14] in x21 + v18 ! [0]"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let ((_, a1, _), _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstHVectorPretty IM.empty (simplifyAstHVector6 a1)
    @?= "let v4 = rconst (fromList [2] [5.0,7.0]) in let [x5 @Natural @Double @[], v6 @Natural @Double @[2], v7 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x1] [v4] in let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v8, v6, v4] in [x12 + v8 ! [0]]"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let ((_, a1, _), _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0]) 1.1
  printAstHVectorPretty IM.empty (simplifyAstHVector6 a1)
    @?= "[cos x1 * (cos (sin x1 - 5.0) * v3 ! [0]) + cos x1 * v3 ! [1] + v3 ! [2]]"

testSin0Scan1Fwd2PP :: Assertion
testSin0Scan1Fwd2PP = do
  resetVarCounter
  let ((_, HVectorPseudoTensor a1, _), _) =
        fwdArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstHVectorPretty IM.empty (simplifyAstHVector6 a1)
    @?= "let v5 = rconst (fromList [2] [5.0,7.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x2] [v5] in let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x1] [rreplicate 2 0.0, v7, v5] in [rappend (rreplicate 1 x1) v11]"

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
    @?= "let v14 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x15 @Natural @Double @[], v16 @Natural @Double @[2], v17 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v14] in let v18 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v18, v16, v14] in 5.0 * v22 ! [0] + 7.0 * v22 ! [1] + x21 + v18 ! [0]"

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
    @?= "let v5 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x13 @Natural @Double @[], v14 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [rfromList [1.1 * 5.0, 1.1 * 7.0], v7, v5] in rappend (rreplicate 1 1.1) v14"

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
    (Flip $ OR.fromList [1] [1.1])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscan (\x _a -> sin x)
                      x0 (rzero @f @Double (0 :$: ZS))
     in f) 1.1)

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 (rconst (OR.constant @Double @1 [1] 42)))
          1.1)

testSin0Scan1FwdForComparison :: Assertion
testSin0Scan1FwdForComparison = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rfromList [x0, sin x0]) 1.1)

testSin0Scan8fwd :: Assertion
testSin0Scan8fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279])
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
    (Flip $ OR.fromList [] [324.086730481586])
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
  let sh = 200 :$: 300 :$: 600 :$: ZS
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
          (\(i :. j :. ZI) -> ifF (i <. j) 0 1 :. ZI)

testUnitriangular2PP :: Assertion
testUnitriangular2PP = do
  resetVarCounter
  let sh = 200 :$: 300 :$: 600 :$: ZS
      k = 1000000
      a1 = unitriangular2 @3 @Double @(AstRanked FullSpan) k sh
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))]) (\\[i9, i10] -> [ifF (i9 <. i10) 0 1, i9, i10])"

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
                             (V.fromList [voidFromSh @Double ZS])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$: ZS))
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
                          (V.fromList [voidFromSh @Double ZS])
                          (V.fromList [voidFromSh @Double ZS])
                          (V.fromList [voidFromSh @Double ZS])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZS))
           in f) 1.1)

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ dmapAccumR (Proxy @f) (SNat @0)
                          (V.fromList [voidFromSh @Double ZS])
                          (V.fromList [voidFromSh @Double ZS])
                          (V.fromList [voidFromSh @Double ZS])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZS))
           in f) 1.1)

testSin0ScanD01 :: Assertion
testSin0ScanD01 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = flip rindex0 [1]
                      $ rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZS])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (1 :$: ZS))
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
                          (V.fromList [ voidFromSh @Double ZS ])
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
                          (V.fromList [ voidFromSh @Double ZS ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZS ])
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
                          (V.fromList [ voidFromSh @Double ZS ])
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
      g = rrev f (V.singleton (voidFromSh @Double ZS))
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x16 @[Natural] @Double @[], v17 @[Natural] @Double @[0]] = dmapAccumRDer (SNat @0) (\\[x24] [x25] -> [x24, x24]) (\\[x33, x34] [x35, x36] -> [x33, x33]) (\\[x46, x47] [x48, x49] -> [0.0 + x46 + x47, 0.0]) [1.1] [rconst (fromList [0] [])] in let [x20 @[Natural] @Double @[], v21 @Natural @Double @[0]] = dmapAccumLDer (SNat @0) (\\[x60] [x61, x62] -> [x60, 0]) (\\[x71, x72, x73] [x74, x75, x76] -> [x71, 0.0]) (\\[x85, x86] [x87, x88, x89] -> [x85, 0, 0]) [4.0] [v17, rconst (fromList [0] [])] in [rfromS x20]"

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
    (simplifyAstHVector6
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (fromList @[1] [0.0])] in let [x13 @[Natural] @Double @[], v14 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] [v9, sconst @[1] (fromList @[1] [0.0])] in [x13]"

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
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "(\\[m10] [x1] -> let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [x1] [sconst @[1] (fromList @[1] [0.0])] in let [x13 @[Natural] @Double @[], v14 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum m10)] [v9, sconst @[1] (fromList @[1] [0.0])] in [x13]) [[sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])], [1.1]]"

testSin0rmapAccumRD01SN531bRPP :: Assertion
testSin0rmapAccumRD01SN531bRPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (dmapAccumR (Proxy @f) (SNat @1)
                          (V.fromList [ voidFromSh @Double ZS ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZS ])
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
      g = rrev f (V.singleton (voidFromSh @Double ZS))
  printAstHVectorSimple
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "dletHVectorInHVector (dmapAccumRDer (SNat @1) (\\[x24 @Natural @Double @[]] [x25 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x24, DynamicRanked x24])) (\\[x33 @Natural @Double @[], x34 @Natural @Double @[]] [x35 @Natural @Double @[], x36 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x33, DynamicRanked x33])) (\\[x46 @Natural @Double @[], x47 @Natural @Double @[]] [x48 @Natural @Double @[], x49 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (x46 + x47), DynamicRanked 0.0])) dmkHVector (fromList [DynamicRanked (rconstant 1.1)]) dmkHVector (fromList [DynamicRanked (rconstant (rconst (fromList [1] [0.0])))])) (\\[x16 @Natural @Double @[], v17 @Natural @Double @[1]] -> dletHVectorInHVector (dmapAccumLDer (SNat @1) (\\[x60 @Natural @Double @[]] [x61 @Natural @Double @[], x62 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x60, DynamicRankedDummy])) (\\[x71 @Natural @Double @[], x72 @Natural @Double @[], x73 @Natural @Double @[]] [x74 @Natural @Double @[], x75 @Natural @Double @[], x76 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x71, DynamicRanked 0.0])) (\\[x85 @Natural @Double @[], x86 @Natural @Double @[]] [x87 @Natural @Double @[], x88 @Natural @Double @[], x89 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x85, DynamicRankedDummy, DynamicRankedDummy])) dmkHVector (fromList [DynamicRanked (rconstant 4.0)]) dmkHVector (fromList [DynamicRanked v17, DynamicRanked (rconstant (rconst (fromList [1] [0.0])))])) (\\[x20 @Natural @Double @[], v21 @Natural @Double @[1]] -> dmkHVector (fromList [DynamicRanked x20])))"

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
                          (V.fromList [ voidFromSh @Double ZS ])
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
      g = rrev f (V.singleton (voidFromSh @Double ZS))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [m23 @[Natural] @Double @[2,2], t24 @[Natural] @Double @[0,2,2]] = dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sconst @[2] (fromList @[2] [0.0,0.0])) + sreplicate (sreplicate 0.0) + sreplicate (sconst @[2] (fromList @[2] [0.0,0.0])) + sreplicate (sreplicate 1.1) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [0] []))))] in let [m28 @[Natural] @Double @[2,2], t29 @Natural @Double @[0,2,2]] = dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])) (\\[i26] -> [i26])] [t24, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [0] []))))] in [rfromS (ssum (ssum m28))]"

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
    (simplifyAstHVector6
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1))
    @?= "let [m13 @[Natural] @Double @[2,2], t14 @[Natural] @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (fromList @[2,2] [0.0,0.0,0.0,0.0]) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1])))) + sreplicate (sconst @[2] (fromList @[2] [0.0,0.0])) + sreplicate (sreplicate 0.0) + sreplicate (sconst @[2] (fromList @[2] [0.0,0.0])) + sreplicate (sreplicate 1.1)] [stranspose (sreplicate (sreplicate (sconst @[1] (fromList @[1] [0.0]))))] in let [m20 @[Natural] @Double @[2,2], t21 @[Natural] @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (fromList @[2,2] [1.0,1.0,1.0,1.0])) (\\[i18] -> [i18])] [t14, stranspose (sreplicate (sreplicate (sconst @[1] (fromList @[1] [0.0]))))] in [ssum (ssum m20)]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (dmapAccumR (Proxy @f) (SNat @1)
                          (V.fromList [ voidFromSh @Double ZS ])
                          (V.fromList [])
                          (V.fromList [ voidFromSh @Double ZS ])
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
      g = rrev f (V.singleton (voidFromSh @Double ZS))
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [m21 @Natural @Double @[2,2], t22 @Natural @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rconst (fromList [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [1] [0.0]))))] in let [m25 @Natural @Double @[2,2], t26 @Natural @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (fromList [2,2] [1.0,1.0,1.0,1.0])] [t22, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (fromList [1] [0.0]))))] in [rsum (rreshape [4] m25)]"

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
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [1] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZS])
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
                         (V.fromList [ voidFromSh @Double (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS)
                                     , voidFromSh @Double (4 :$: 5 :$: 6 :$: 7 :$: 8 :$: ZS) ])
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
                                        (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS)])
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
                                         (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS)
                                     , voidFromSh @Double
                                         (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS) ])
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
                                         (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS)
                                     , voidFromSh @Double
                                         (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS) ])
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
                                                                             (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZS) ])
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
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZS)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZS)])
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
                       (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZS)])
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
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZS)])
                   (V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZS)])
                   (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZS)])
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
                       (V.fromList [voidFromSh @Double ZS])
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
                       (V.fromList [voidFromSh @Double ZS])
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
                       (V.fromList [voidFromSh @Double ZS])
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
                       (V.fromList [ voidFromSh @Double ZS
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
                           (V.fromList [voidFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v14 = rconst (fromList [2] [42.0,42.0]) in let [x15 @Natural @Double @[], v16 @Natural @Double @[2], v17 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v14] in let v18 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v18, v16, v14] in x21 + v18 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rconst (fromList [2] [42.0,42.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.1) v11"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v14 = rconst (fromList [2] [5.0,7.0]) in let [x15 @Natural @Double @[], v16 @Natural @Double @[2], v17 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v14] in let v18 = rconst (fromList [3] [1.0,1.0,1.0]) in let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v18, v16, v14] in x21 + v18 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rconst (fromList [2] [5.0,7.0]) in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x10 @Natural @Double @[], v11 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [rreplicate 2 0.0, v7, v5] in rappend (rreplicate 1 1.1) v11"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [2.417297824578748] :: OR.Array 0 Double)
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconst (OS.fromList @'[2, 2] @Double [5, 7, 3, 4])
                      !$ (k :!!!$ ZSH) ))
          1.1)

testSin0ScanD1Rev3 :: Assertion
testSin0ScanD1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [47.150000000000006] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZS])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1)

testSin0ScanD1Rev3PP :: Assertion
testSin0ScanD1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZS])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1
  length (printAstSimple IM.empty (simplifyAst6 a1))
    @?= 4454

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZS])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v5 = rfromList [1.1 * 5.0, 1.1 * 7.0] in let [x6 @Natural @Double @[], v7 @Natural @Double @[2], v8 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v5] in let [x13 @Natural @Double @[], v14 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [rfromList [1.1 * 5.0, 1.1 * 7.0], v7, v5] in rappend (rreplicate 1 1.1) v14"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.1])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [voidFromSh @Double ZS])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$: ZS))
     in f) 1.1)

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (V.fromList [ voidFromSh @Double ZS
                               , voidFromSh @Double (3 :$: 4 :$: ZS)])
                   x0 (V.fromList
                         [ DynamicRanked
                           $ rconst (OR.constant @Double @1 [1] 42)
                         , DynamicRanked
                           $ rconst (OR.constant @Double @3 [1, 3, 4] 32) ]))
          1.1)

testSin0ScanD8fwd :: Assertion
testSin0ScanD8fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279])
    (rfwd1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                      (V.fromList [voidFromSh @Double ZS])
                      (rreplicate 2 (rreplicate 5 (2 * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8fwdMapAccum :: Assertion
testSin0ScanD8fwdMapAccum = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [4,2,5] [2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,2.2,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.6450465372542022,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.2642905982717151,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279,-0.242034255165279])
    (rfwd1 @(Flip OR.Array) @Double @0 @3 @Double
       (\a0 -> rreverse $ (rfromD . (V.! 1))
               $ dunHVector
               $ dmapAccumR Proxy (SNat @4)
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: ZS)])
                   (V.fromList [voidFromSh @Double (2 :$: 5 :$: ZS)])
                   (V.fromList [voidFromSh @Double ZS])
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
                       (V.fromList [voidFromSh @Double ZS])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [324.086730481586])
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
    @?= "let [x4 @[Natural] @Double @[], v5 @[Natural] @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1] in let [x9 @[Natural] @Double @[], v10 @[Natural] @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v5, sreplicate 1.1] in [ssum v10 + x9]"

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  printAstHVectorPretty
    IM.empty
    (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v13, rreplicate 11 1.1] in [rsum v17 + x16]"

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  printAstHVectorPretty
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v13, rreplicate 11 1.1] in [rsum v17 + x16]"

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) (\\[x20] [x21] -> [let [x29 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\[x35] [x36] -> [x35 + tan x36]) (\\[x53, x54] [x55, x56] -> let x61 = cos x56 in [x53 + x54 * recip (x61 * x61)]) (\\[x75] [x76, x77] -> let x81 = cos x77 in [x75, recip (x81 * x81) * x75]) [x21] [rreplicate 22 x20] in x29, x20]) (\\[x87, x88] [x89, x90] -> let [x110 @Natural @Double @[]] = let [x107 @Natural @Double @[], v108 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x115] [x116] -> [x115 + tan x116, x115]) (\\[x132, x133] [x134, x135] -> let x154 = cos x135 in [x132 + x133 * recip (x154 * x154), x132]) (\\[x166, x167] [x168, x169] -> let x185 = cos x169 in [x166 + x167, recip (x185 * x185) * x166]) [x90] [rreplicate 22 x89] in let [x109 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\[x196] [x197, x198, x199] -> let x208 = cos x199 in [x196 + x197 * recip (x208 * x208)]) (\\[x244, x245, x246, x247] [x248, x249, x250, x251] -> let x262 = cos x251 ; x263 = x262 * x262 ; x267 = x247 * negate (sin x251) in [x244 + x245 * recip x263 + ((x267 * x262 + x267 * x262) * negate (recip (x263 * x263))) * x249]) (\\[x295] [x296, x297, x298, x299] -> let x307 = cos x299 ; x308 = x307 * x307 ; x312 = negate (recip (x308 * x308)) * (x297 * x295) in [x295, recip x308 * x295, 0, negate (sin x299) * (x307 * x312 + x307 * x312)]) [x88] [rreplicate 22 x87, v108, rreplicate 22 x89] in [x109] in [x110, x87]) (\\[x317, x318] [x319, x320] -> let [x346 @Natural @Double @[], x347 @Natural @Double @[]] = let [x342 @Natural @Double @[], v343 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x352] [x353] -> [x352 + tan x353, x352]) (\\[x369, x370] [x371, x372] -> let x391 = cos x372 in [x369 + x370 * recip (x391 * x391), x369]) (\\[x403, x404] [x405, x406] -> let x422 = cos x406 in [x403 + x404, recip (x422 * x422) * x403]) [x320] [rreplicate 22 x319] in let [x344 @Natural @Double @[], v345 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x431] [x432, x433] -> let x439 = cos x433 in [x431, recip (x439 * x439) * x431]) (\\[x465, x466, x467] [x468, x469, x470] -> let x478 = cos x470 ; x479 = x478 * x478 ; x481 = x467 * negate (sin x470) in [x465, ((x481 * x478 + x481 * x478) * negate (recip (x479 * x479))) * x468 + x465 * recip x479]) (\\[x506, x507] [x508, x509, x510] -> let x517 = cos x510 ; x518 = x517 * x517 ; x520 = negate (recip (x518 * x518)) * (x508 * x507) in [recip x518 * x507 + x506, 0, negate (sin x510) * (x517 * x520 + x517 * x520)]) [x317] [v343, rreplicate 22 x319] in [rsum v345, x344] in [x346 + x318, x347]) [1.1] [rreplicate 11 1.1] in let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) (\\[x524] [x525, x526] -> let [x534 @Natural @Double @[], v535 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x540] [x541] -> [x540 + tan x541, x540]) (\\[x548, x549] [x550, x551] -> let x556 = cos x551 in [x548 + x549 * recip (x556 * x556), x548]) (\\[x564, x565] [x566, x567] -> let x571 = cos x567 in [x564 + x565, recip (x571 * x571) * x564]) [x526] [rreplicate 22 x525] in let [x536 @Natural @Double @[], v537 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x577] [x578, x579] -> let x582 = cos x579 in [x577, recip (x582 * x582) * x577]) (\\[x590, x591, x592] [x593, x594, x595] -> let x603 = cos x595 ; x604 = x603 * x603 ; x606 = x592 * negate (sin x595) in [x590, ((x606 * x603 + x606 * x603) * negate (recip (x604 * x604))) * x593 + x590 * recip x604]) (\\[x615, x616] [x617, x618, x619] -> let x626 = cos x619 ; x627 = x626 * x626 ; x629 = negate (recip (x627 * x627)) * (x617 * x616) in [recip x627 * x616 + x615, 0, negate (sin x619) * (x626 * x629 + x626 * x629)]) [x524] [v535, rreplicate 22 x525] in [rsum v537, x536]) (\\[x663, x664, x665] [x666, x667, x668] -> let [x670 @Natural @Double @[], v671 @Natural @Double @[22], v672 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x685] [x686] -> [x685 + tan x686, x685, x685]) (\\[x698, x699] [x700, x701] -> let x716 = cos x701 in [x698 + x699 * recip (x716 * x716), x698, x698]) (\\[x725, x726, x727] [x728, x729] -> let x742 = cos x729 in [x726 + x725 + x727, recip (x742 * x742) * x725]) [x668] [rreplicate 22 x667] in let [x675 @Natural @Double @[], v676 @Natural @Double @[22], v677 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x749] [x750, x751] -> let x761 = cos x751 in [x749, x749, recip (x761 * x761) * x749]) (\\[x770, x771, x772] [x773, x774, x775] -> let x798 = cos x775 ; x799 = x798 * x798 ; x801 = x772 * negate (sin x775) in [x770, x770, ((x801 * x798 + x801 * x798) * negate (recip (x799 * x799))) * x773 + x770 * recip x799]) (\\[x811, x812, x813] [x814, x815, x816] -> let x835 = cos x816 ; x836 = x835 * x835 ; x838 = negate (recip (x836 * x836)) * (x814 * x813) in [x812 + recip x836 * x813 + x811, 0.0, negate (sin x816) * (x835 * x838 + x835 * x838)]) [x666] [v672, rreplicate 22 x667] in let [x678 @Natural @Double @[], v679 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x845] [x846, x847, x848] -> let x853 = cos x848 in [x845 + x846 * recip (x853 * x853), x845]) (\\[x881, x882, x883, x884] [x885, x886, x887, x888] -> let x889 = cos x888 ; x890 = x889 * x889 ; x894 = x884 * negate (sin x888) in [x881 + x882 * recip x890 + ((x894 * x889 + x894 * x889) * negate (recip (x890 * x890))) * x886, x881]) (\\[x919, x920] [x921, x922, x923, x924] -> let x925 = cos x924 ; x926 = x925 * x925 ; x932 = negate (recip (x926 * x926)) * (x922 * x919) in [x919 + x920, recip x926 * x919, 0, negate (sin x924) * (x925 * x932 + x925 * x932)]) [x665] [rreplicate 22 x664, v671, rreplicate 22 x667] in let [x680 @Natural @Double @[], v681 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x939] [x940, x941, x942, x943, x944] -> let x952 = cos x944 ; x953 = x952 * x952 ; x955 = x941 * negate (sin x944) in [x939, ((x955 * x952 + x955 * x952) * negate (recip (x953 * x953))) * x942 + x939 * recip x953]) (\\[x1004, x1005, x1006, x1007, x1008, x1009] [x1010, x1011, x1012, x1013, x1014, x1015] -> let x1016 = cos x1015 ; x1017 = x1016 * x1016 ; x1019 = negate (sin x1015) ; x1020 = x1012 * x1019 ; x1021 = x1020 * x1016 + x1020 * x1016 ; x1022 = x1017 * x1017 ; x1023 = negate (recip x1022) ; x1028 = x1006 * x1019 + ((x1009 * cos x1015) * -1.0) * x1012 ; x1029 = x1009 * negate (sin x1015) ; x1033 = x1029 * x1016 + x1029 * x1016 in [x1004, ((x1028 * x1016 + x1029 * x1020 + x1028 * x1016 + x1029 * x1020) * x1023 + (((x1033 * x1017 + x1033 * x1017) * negate (recip (x1022 * x1022))) * -1.0) * x1021) * x1013 + x1007 * (x1021 * x1023) + x1004 * recip x1017 + (x1033 * negate (recip (x1017 * x1017))) * x1010]) (\\[x1074, x1075] [x1076, x1077, x1078, x1079, x1080, x1081] -> let x1082 = cos x1081 ; x1083 = x1082 * x1082 ; x1085 = negate (sin x1081) ; x1086 = x1078 * x1085 ; x1087 = x1086 * x1082 + x1086 * x1082 ; x1088 = x1083 * x1083 ; x1089 = negate (recip x1088) ; x1094 = x1079 * x1075 ; x1095 = negate (recip (x1088 * x1088)) * (-1.0 * (x1087 * x1094)) ; x1096 = x1089 * x1094 ; x1097 = x1082 * x1096 + x1082 * x1096 ; x1098 = negate (recip (x1083 * x1083)) * (x1076 * x1075) + x1083 * x1095 + x1083 * x1095 in [recip x1083 * x1075 + x1074, 0, x1085 * x1097, (x1087 * x1089) * x1075, 0, negate (sin x1081) * (x1082 * x1098 + x1082 * x1098 + x1086 * x1096 + x1086 * x1096) + cos x1081 * (-1.0 * (x1078 * x1097))]) [x663] [v679, rreplicate 22 x664, v676, v672, rreplicate 22 x667] in [rsum v681, x680]) (\\[x1131, x1132] [x1133, x1134, x1135] -> let [x1137 @Natural @Double @[], v1138 @Natural @Double @[22], v1139 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x1158] [x1159] -> [x1158 + tan x1159, x1158, x1158]) (\\[x1171, x1172] [x1173, x1174] -> let x1189 = cos x1174 in [x1171 + x1172 * recip (x1189 * x1189), x1171, x1171]) (\\[x1198, x1199, x1200] [x1201, x1202] -> let x1215 = cos x1202 in [x1199 + x1198 + x1200, recip (x1215 * x1215) * x1198]) [x1135] [rreplicate 22 x1134] in let [x1142 @Natural @Double @[], v1143 @Natural @Double @[22], v1144 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x1222] [x1223, x1224] -> let x1234 = cos x1224 in [x1222, x1222, recip (x1234 * x1234) * x1222]) (\\[x1243, x1244, x1245] [x1246, x1247, x1248] -> let x1271 = cos x1248 ; x1272 = x1271 * x1271 ; x1274 = x1245 * negate (sin x1248) in [x1243, x1243, ((x1274 * x1271 + x1274 * x1271) * negate (recip (x1272 * x1272))) * x1246 + x1243 * recip x1272]) (\\[x1284, x1285, x1286] [x1287, x1288, x1289] -> let x1308 = cos x1289 ; x1309 = x1308 * x1308 ; x1311 = negate (recip (x1309 * x1309)) * (x1287 * x1286) in [x1285 + recip x1309 * x1286 + x1284, 0.0, negate (sin x1289) * (x1308 * x1311 + x1308 * x1311)]) [x1133] [v1139, rreplicate 22 x1134] in let [x1149 @Natural @Double @[], v1150 @Natural @Double @[22], v1151 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\[x1319] [x1320, x1321, x1322, x1323] -> let x1328 = cos x1323 ; x1329 = x1328 * x1328 ; x1331 = negate (recip (x1329 * x1329)) * (x1321 * x1320) in [recip x1329 * x1320 + x1319, 0, negate (sin x1323) * (x1328 * x1331 + x1328 * x1331)]) (\\[x1371, x1372, x1373, x1374, x1375] [x1376, x1377, x1378, x1379, x1380] -> let x1381 = cos x1380 ; x1382 = x1381 * x1381 ; x1384 = x1382 * x1382 ; x1385 = negate (recip x1384) ; x1386 = x1378 * x1377 ; x1387 = x1385 * x1386 ; x1390 = x1375 * negate (sin x1380) ; x1391 = x1390 * x1381 + x1390 * x1381 ; x1401 = (((x1391 * x1382 + x1391 * x1382) * negate (recip (x1384 * x1384))) * -1.0) * x1386 + (x1373 * x1377 + x1372 * x1378) * x1385 in [x1371 + (x1391 * negate (recip (x1382 * x1382))) * x1377 + x1372 * recip x1382, 0.0, ((x1375 * cos x1380) * -1.0) * (x1381 * x1387 + x1381 * x1387) + (x1390 * x1387 + x1401 * x1381 + x1390 * x1387 + x1401 * x1381) * negate (sin x1380)]) (\\[x1435, x1436, x1437] [x1438, x1439, x1440, x1441, x1442] -> let x1443 = cos x1442 ; x1444 = x1443 * x1443 ; x1446 = x1444 * x1444 ; x1447 = negate (recip x1446) ; x1448 = x1440 * x1439 ; x1449 = x1447 * x1448 ; x1455 = negate (sin x1442) * x1437 ; x1456 = x1443 * x1455 + x1443 * x1455 ; x1457 = x1447 * x1456 ; x1458 = negate (recip (x1446 * x1446)) * (-1.0 * (x1448 * x1456)) ; x1459 = negate (recip (x1444 * x1444)) * (x1439 * x1435) + x1444 * x1458 + x1444 * x1458 in [x1435, x1440 * x1457 + recip x1444 * x1435, x1439 * x1457, 0, negate (sin x1442) * (x1443 * x1459 + x1443 * x1459 + x1449 * x1455 + x1449 * x1455) + cos x1442 * (-1.0 * ((x1443 * x1449 + x1443 * x1449) * x1437))]) [x1132] [rreplicate 22 x1131, v1143, v1139, rreplicate 22 x1134] in let [x1154 @Natural @Double @[], v1155 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\[x1464] [x1465, x1466, x1467] -> let x1471 = cos x1467 in [x1464 + x1465, recip (x1471 * x1471) * x1464]) (\\[x1496, x1497, x1498, x1499] [x1500, x1501, x1502, x1503] -> let x1504 = cos x1503 ; x1505 = x1504 * x1504 ; x1509 = x1499 * negate (sin x1503) in [x1496 + x1497, ((x1509 * x1504 + x1509 * x1504) * negate (recip (x1505 * x1505))) * x1500 + x1496 * recip x1505]) (\\[x1531, x1532] [x1533, x1534, x1535, x1536] -> let x1537 = cos x1536 ; x1538 = x1537 * x1537 ; x1543 = negate (recip (x1538 * x1538)) * (x1533 * x1532) in [recip x1538 * x1532 + x1531, x1531, 0, negate (sin x1536) * (x1537 * x1543 + x1537 * x1543)]) [0.0] [v1150, v1138, rreplicate 22 x1134] in [x1149, rsum v1155 + rsum v1151, x1154]) [1.0] [v13, rreplicate 11 1.1] in [rsum v17 + x16]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyAstHVector6
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 2_226

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyAstHVector6
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 23_312

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 284_763

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 4_128_567

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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector6
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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 0

testSin0MapAccumNestedR1PP :: Assertion
testSin0MapAccumNestedR1PP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZS
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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x20] [x21] -> let [x25 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\[x30] [x31] -> [x30 + tan x31]) (\\[x43, x44] [x45, x46] -> let x50 = cos x46 in [x43 + x44 * recip (x50 * x50)]) (\\[x61] [x62, x63] -> let x66 = cos x63 in [x61, recip (x66 * x66) * x61]) [x21] [rreplicate 2 x20] in [x25, x20]) (\\[x71, x72] [x73, x74] -> let [x92 @Natural @Double @[]] = let [x89 @Natural @Double @[], v90 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x97] [x98] -> [x97 + tan x98, x97]) (\\[x112, x113] [x114, x115] -> let x130 = cos x115 in [x112 + x113 * recip (x130 * x130), x112]) (\\[x141, x142] [x143, x144] -> let x156 = cos x144 in [x141 + x142, recip (x156 * x156) * x141]) [x74] [rreplicate 2 x73] in let [x91 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\[x166] [x167, x168, x169] -> let x176 = cos x169 in [x166 + x167 * recip (x176 * x176)]) (\\[x208, x209, x210, x211] [x212, x213, x214, x215] -> let x226 = cos x215 ; x227 = x226 * x226 ; x231 = x211 * negate (sin x215) in [x208 + x209 * recip x227 + ((x231 * x226 + x231 * x226) * negate (recip (x227 * x227))) * x213]) (\\[x256] [x257, x258, x259, x260] -> let x268 = cos x260 ; x269 = x268 * x268 ; x273 = negate (recip (x269 * x269)) * (x258 * x256) in [x256, recip x269 * x256, 0, negate (sin x260) * (x268 * x273 + x268 * x273)]) [x72] [rreplicate 2 x71, v90, rreplicate 2 x73] in [x91] in [x92, x71]) (\\[x278, x279] [x280, x281] -> let [x305 @Natural @Double @[], x306 @Natural @Double @[]] = let [x301 @Natural @Double @[], v302 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x311] [x312] -> [x311 + tan x312, x311]) (\\[x326, x327] [x328, x329] -> let x344 = cos x329 in [x326 + x327 * recip (x344 * x344), x326]) (\\[x355, x356] [x357, x358] -> let x370 = cos x358 in [x355 + x356, recip (x370 * x370) * x355]) [x281] [rreplicate 2 x280] in let [x303 @Natural @Double @[], v304 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x378] [x379, x380] -> let x384 = cos x380 in [x378, recip (x384 * x384) * x378]) (\\[x406, x407, x408] [x409, x410, x411] -> let x419 = cos x411 ; x420 = x419 * x419 ; x422 = x408 * negate (sin x411) in [x406, ((x422 * x419 + x422 * x419) * negate (recip (x420 * x420))) * x409 + x406 * recip x420]) (\\[x444, x445] [x446, x447, x448] -> let x455 = cos x448 ; x456 = x455 * x455 ; x458 = negate (recip (x456 * x456)) * (x446 * x445) in [recip x456 * x445 + x444, 0, negate (sin x448) * (x455 * x458 + x455 * x458)]) [x278] [v302, rreplicate 2 x280] in [rsum v304, x303] in [x305 + x279, x306]) [1.1] [rreplicate 2 1.1] in let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x462] [x463, x464] -> let [x472 @Natural @Double @[], v473 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x478] [x479] -> [x478 + tan x479, x478]) (\\[x486, x487] [x488, x489] -> let x493 = cos x489 in [x486 + x487 * recip (x493 * x493), x486]) (\\[x500, x501] [x502, x503] -> let x506 = cos x503 in [x500 + x501, recip (x506 * x506) * x500]) [x464] [rreplicate 2 x463] in let [x474 @Natural @Double @[], v475 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x511] [x512, x513] -> let x515 = cos x513 in [x511, recip (x515 * x515) * x511]) (\\[x522, x523, x524] [x525, x526, x527] -> let x535 = cos x527 ; x536 = x535 * x535 ; x538 = x524 * negate (sin x527) in [x522, ((x538 * x535 + x538 * x535) * negate (recip (x536 * x536))) * x525 + x522 * recip x536]) (\\[x547, x548] [x549, x550, x551] -> let x558 = cos x551 ; x559 = x558 * x558 ; x561 = negate (recip (x559 * x559)) * (x549 * x548) in [recip x559 * x548 + x547, 0, negate (sin x551) * (x558 * x561 + x558 * x561)]) [x462] [v473, rreplicate 2 x463] in [rsum v475, x474]) (\\[x595, x596, x597] [x598, x599, x600] -> let [x602 @Natural @Double @[], v603 @Natural @Double @[2], v604 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x617] [x618] -> [x617 + tan x618, x617, x617]) (\\[x630, x631] [x632, x633] -> let x646 = cos x633 in [x630 + x631 * recip (x646 * x646), x630, x630]) (\\[x654, x655, x656] [x657, x658] -> let x669 = cos x658 in [x655 + x654 + x656, recip (x669 * x669) * x654]) [x600] [rreplicate 2 x599] in let [x607 @Natural @Double @[], v608 @Natural @Double @[2], v609 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x675] [x676, x677] -> let x685 = cos x677 in [x675, x675, recip (x685 * x685) * x675]) (\\[x693, x694, x695] [x696, x697, x698] -> let x721 = cos x698 ; x722 = x721 * x721 ; x724 = x695 * negate (sin x698) in [x693, x693, ((x724 * x721 + x724 * x721) * negate (recip (x722 * x722))) * x696 + x693 * recip x722]) (\\[x734, x735, x736] [x737, x738, x739] -> let x758 = cos x739 ; x759 = x758 * x758 ; x761 = negate (recip (x759 * x759)) * (x737 * x736) in [x735 + recip x759 * x736 + x734, 0.0, negate (sin x739) * (x758 * x761 + x758 * x761)]) [x598] [v604, rreplicate 2 x599] in let [x610 @Natural @Double @[], v611 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x768] [x769, x770, x771] -> let x775 = cos x771 in [x768 + x769 * recip (x775 * x775), x768]) (\\[x799, x800, x801, x802] [x803, x804, x805, x806] -> let x807 = cos x806 ; x808 = x807 * x807 ; x812 = x802 * negate (sin x806) in [x799 + x800 * recip x808 + ((x812 * x807 + x812 * x807) * negate (recip (x808 * x808))) * x804, x799]) (\\[x834, x835] [x836, x837, x838, x839] -> let x840 = cos x839 ; x841 = x840 * x840 ; x847 = negate (recip (x841 * x841)) * (x837 * x834) in [x834 + x835, recip x841 * x834, 0, negate (sin x839) * (x840 * x847 + x840 * x847)]) [x597] [rreplicate 2 x596, v603, rreplicate 2 x599] in let [x612 @Natural @Double @[], v613 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x854] [x855, x856, x857, x858, x859] -> let x867 = cos x859 ; x868 = x867 * x867 ; x870 = x856 * negate (sin x859) in [x854, ((x870 * x867 + x870 * x867) * negate (recip (x868 * x868))) * x857 + x854 * recip x868]) (\\[x919, x920, x921, x922, x923, x924] [x925, x926, x927, x928, x929, x930] -> let x931 = cos x930 ; x932 = x931 * x931 ; x934 = negate (sin x930) ; x935 = x927 * x934 ; x936 = x935 * x931 + x935 * x931 ; x937 = x932 * x932 ; x938 = negate (recip x937) ; x943 = x921 * x934 + ((x924 * cos x930) * -1.0) * x927 ; x944 = x924 * negate (sin x930) ; x948 = x944 * x931 + x944 * x931 in [x919, ((x943 * x931 + x944 * x935 + x943 * x931 + x944 * x935) * x938 + (((x948 * x932 + x948 * x932) * negate (recip (x937 * x937))) * -1.0) * x936) * x928 + x922 * (x936 * x938) + x919 * recip x932 + (x948 * negate (recip (x932 * x932))) * x925]) (\\[x989, x990] [x991, x992, x993, x994, x995, x996] -> let x997 = cos x996 ; x998 = x997 * x997 ; x1000 = negate (sin x996) ; x1001 = x993 * x1000 ; x1002 = x1001 * x997 + x1001 * x997 ; x1003 = x998 * x998 ; x1004 = negate (recip x1003) ; x1009 = x994 * x990 ; x1010 = negate (recip (x1003 * x1003)) * (-1.0 * (x1002 * x1009)) ; x1011 = x1004 * x1009 ; x1012 = x997 * x1011 + x997 * x1011 ; x1013 = negate (recip (x998 * x998)) * (x991 * x990) + x998 * x1010 + x998 * x1010 in [recip x998 * x990 + x989, 0, x1000 * x1012, (x1002 * x1004) * x990, 0, negate (sin x996) * (x997 * x1013 + x997 * x1013 + x1001 * x1011 + x1001 * x1011) + cos x996 * (-1.0 * (x993 * x1012))]) [x595] [v611, rreplicate 2 x596, v608, v604, rreplicate 2 x599] in [rsum v613, x612]) (\\[x1046, x1047] [x1048, x1049, x1050] -> let [x1052 @Natural @Double @[], v1053 @Natural @Double @[2], v1054 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x1073] [x1074] -> [x1073 + tan x1074, x1073, x1073]) (\\[x1086, x1087] [x1088, x1089] -> let x1102 = cos x1089 in [x1086 + x1087 * recip (x1102 * x1102), x1086, x1086]) (\\[x1110, x1111, x1112] [x1113, x1114] -> let x1125 = cos x1114 in [x1111 + x1110 + x1112, recip (x1125 * x1125) * x1110]) [x1050] [rreplicate 2 x1049] in let [x1057 @Natural @Double @[], v1058 @Natural @Double @[2], v1059 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x1131] [x1132, x1133] -> let x1141 = cos x1133 in [x1131, x1131, recip (x1141 * x1141) * x1131]) (\\[x1149, x1150, x1151] [x1152, x1153, x1154] -> let x1177 = cos x1154 ; x1178 = x1177 * x1177 ; x1180 = x1151 * negate (sin x1154) in [x1149, x1149, ((x1180 * x1177 + x1180 * x1177) * negate (recip (x1178 * x1178))) * x1152 + x1149 * recip x1178]) (\\[x1190, x1191, x1192] [x1193, x1194, x1195] -> let x1214 = cos x1195 ; x1215 = x1214 * x1214 ; x1217 = negate (recip (x1215 * x1215)) * (x1193 * x1192) in [x1191 + recip x1215 * x1192 + x1190, 0.0, negate (sin x1195) * (x1214 * x1217 + x1214 * x1217)]) [x1048] [v1054, rreplicate 2 x1049] in let [x1064 @Natural @Double @[], v1065 @Natural @Double @[2], v1066 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\[x1225] [x1226, x1227, x1228, x1229] -> let x1234 = cos x1229 ; x1235 = x1234 * x1234 ; x1237 = negate (recip (x1235 * x1235)) * (x1227 * x1226) in [recip x1235 * x1226 + x1225, 0, negate (sin x1229) * (x1234 * x1237 + x1234 * x1237)]) (\\[x1277, x1278, x1279, x1280, x1281] [x1282, x1283, x1284, x1285, x1286] -> let x1287 = cos x1286 ; x1288 = x1287 * x1287 ; x1290 = x1288 * x1288 ; x1291 = negate (recip x1290) ; x1292 = x1284 * x1283 ; x1293 = x1291 * x1292 ; x1296 = x1281 * negate (sin x1286) ; x1297 = x1296 * x1287 + x1296 * x1287 ; x1307 = (((x1297 * x1288 + x1297 * x1288) * negate (recip (x1290 * x1290))) * -1.0) * x1292 + (x1279 * x1283 + x1278 * x1284) * x1291 in [x1277 + (x1297 * negate (recip (x1288 * x1288))) * x1283 + x1278 * recip x1288, 0.0, ((x1281 * cos x1286) * -1.0) * (x1287 * x1293 + x1287 * x1293) + (x1296 * x1293 + x1307 * x1287 + x1296 * x1293 + x1307 * x1287) * negate (sin x1286)]) (\\[x1341, x1342, x1343] [x1344, x1345, x1346, x1347, x1348] -> let x1349 = cos x1348 ; x1350 = x1349 * x1349 ; x1352 = x1350 * x1350 ; x1353 = negate (recip x1352) ; x1354 = x1346 * x1345 ; x1355 = x1353 * x1354 ; x1361 = negate (sin x1348) * x1343 ; x1362 = x1349 * x1361 + x1349 * x1361 ; x1363 = x1353 * x1362 ; x1364 = negate (recip (x1352 * x1352)) * (-1.0 * (x1354 * x1362)) ; x1365 = negate (recip (x1350 * x1350)) * (x1345 * x1341) + x1350 * x1364 + x1350 * x1364 in [x1341, x1346 * x1363 + recip x1350 * x1341, x1345 * x1363, 0, negate (sin x1348) * (x1349 * x1365 + x1349 * x1365 + x1355 * x1361 + x1355 * x1361) + cos x1348 * (-1.0 * ((x1349 * x1355 + x1349 * x1355) * x1343))]) [x1047] [rreplicate 2 x1046, v1058, v1054, rreplicate 2 x1049] in let [x1069 @Natural @Double @[], v1070 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\[x1370] [x1371, x1372, x1373] -> let x1376 = cos x1373 in [x1370 + x1371, recip (x1376 * x1376) * x1370]) (\\[x1397, x1398, x1399, x1400] [x1401, x1402, x1403, x1404] -> let x1405 = cos x1404 ; x1406 = x1405 * x1405 ; x1410 = x1400 * negate (sin x1404) in [x1397 + x1398, ((x1410 * x1405 + x1410 * x1405) * negate (recip (x1406 * x1406))) * x1401 + x1397 * recip x1406]) (\\[x1429, x1430] [x1431, x1432, x1433, x1434] -> let x1435 = cos x1434 ; x1436 = x1435 * x1435 ; x1441 = negate (recip (x1436 * x1436)) * (x1431 * x1430) in [recip x1436 * x1430 + x1429, x1429, 0, negate (sin x1434) * (x1435 * x1441 + x1435 * x1441)]) [0.0] [v1065, v1053, rreplicate 2 x1049] in [x1064, rsum v1070 + rsum v1066, x1069]) [1.0] [v13, rreplicate 2 1.1] in [rsum v17 + x16]"

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZS
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
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 4129277

testSin0MapAccumNestedR4 :: Assertion
testSin0MapAccumNestedR4 = do
 assertEqualUpToEpsilon' 1e-10
  (1.0410225027528066 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
  (1.3793719002779494 :: Flip OR.Array Double 0)
  (rev @_ @_ @(AstRanked FullSpan)
   (let
      sh1 = voidFromSh @Double ZS
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
      sh1 = voidFromSh @Double ZS
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
    0.24200000000000005
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
    @?= 52832

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZS))
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
             (V.singleton (voidFromSh @Double ZS))
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
             (V.singleton (voidFromSh @Double ZS))
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
  let doms = V.singleton (voidFromSh @Double ZS)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZS))
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
  let doms = V.singleton (voidFromSh @Double ZS)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZS))
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
      doms = V.fromList [ voidFromSh @Double ZS
                        , voidFromSh @Double ZS ]
      p :: ranked Double 1
      p = rscanZip f doms 7 as
      rf :: forall f. ADReady f
         => f Double 0 -> f Double 0 -> HVector f -> HVectorOf f
      rf _x _y = rrev @f (f 42) doms  -- not exactly the rev of f
  in fFoldZipR doms p as rf ZS 26

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
