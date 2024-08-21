{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.RankedS qualified as OR
import Data.IntMap.Strict qualified as IM
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, type (+))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Mixed.Shape qualified as X
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), RealFloatF (..))
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
  , testCase "4Sin0RfwdPP0" testSin0RfwdPP0
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
  , testCase "4Sin0rmapAccumRD01SN5" testSin0rmapAccumRD01SN5
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
-- TODO: takes too long ATM:  , testCase "4Sin0FoldNestedR41" testSin0FoldNestedR41
  , testCase "4Sin0FoldNestedR40" testSin0FoldNestedR40
-- TODO: OOMs (only together with others, so via heap fragmentation?) ATM:  , testCase "4Sin0FoldNestedR400" testSin0FoldNestedR400
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

foo :: RealFloatF a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

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
                       [ DynamicRanked $ rconst @g $ Nested.rscalar x
                       , DynamicRanked $ rconst @g $ Nested.rscalar y
                       , DynamicRanked $ rconst @g $ Nested.rscalar z ])
  in ( rletHVectorIn domsOf (\v -> rfromD $ v V.! 0)
     , rletHVectorIn domsOf (\v -> rfromD $ v V.! 1)
     , rletHVectorIn domsOf (\v -> rfromD $ v V.! 2) )

testFooRrev :: Assertion
testFooRrev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396285219055063, rscalar (-1.953374825727421), rscalar 0.9654825811012627)
    (fooRrev @ORArray @Double (1.1, 2.2, 3.3))

testFooRrev2 :: Assertion
testFooRrev2 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 2.4396284, rscalar (-1.9533751), rscalar 0.96548253)
    (fooRrev @ORArray @Float (1.1, 2.2, 3.3))

testFooRrevPP1 :: Assertion
testFooRrevPP1 = do
  resetVarCounter
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstPretty IM.empty a1
    @?= "let x13 = sin 2.2 ; x17 = 1.1 * x13 ; x24 = recip (3.3 * 3.3 + x17 * x17) ; x28 = sin 2.2 ; x36 = 3.3 * 1.0 ; x40 = (negate 3.3 * x24) * 1.0 in x13 * x40 + x28 * x36"

-- Disabled, because different variable names with -O1.
_testFooRrevPP2 :: Assertion
_testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rlet (sin (rconstant 2.2)) (\\x39 -> rlet (rconstant 1.1 * x39) (\\x40 -> rlet (recip (rconstant 3.3 * rconstant 3.3 + x40 * x40)) (\\x41 -> rlet (sin (rconstant 2.2)) (\\x42 -> rlet (rconstant 1.1 * x42) (\\x43 -> rlet (rreshape [] (rreplicate 1 (rconstant 1.0))) (\\x44 -> rlet (rconstant 3.3 * x44) (\\x45 -> rlet (negate (rconstant 3.3 * x41) * x44) (\\x46 -> x39 * x46 + x42 * x45))))))))"

testFooRrev3 :: Assertion
testFooRrev3 = do
  let f (D a _) =
        let (a1, _, _) = fooRrev @(ADVal ORArray) @Double
                                 (Nested.runScalar (runFlipR a), 2.2, 3.3)
        in a1
  assertEqualUpToEpsilon 1e-10
    0
    (crev f (rscalar 1.1))

testSin0Rrev :: Assertion
testSin0Rrev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.4535961214255773)
    (rrev1 @ORArray @Double @0 @0 sin (rscalar 1.1))

testSin0RrevPP1 :: Assertion
testSin0RrevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "cos 1.1 * 1.0"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstSimple IM.empty a1
    @?= "cos (rconstant 1.1) * rconstant 1.0"

testSin0Rrev3 :: Assertion
testSin0Rrev3 = do
  let f = rrev1 @(ADVal ORArray) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (crev f (rscalar 1.1))

testSin0Rrev4 :: Assertion
testSin0Rrev4 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.8988770945225438)
    ((rrev1 sin . rrev1 @ORArray @Double @0 @0 sin) (rscalar 1.1))

testSin0RrevPP4 :: Assertion
testSin0RrevPP4 = do
  let a1 = (rrev1 sin . rrev1 @(AstRanked FullSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "cos (cos 1.1 * 1.0) * 1.0"

testSin0Rrev5 :: Assertion
testSin0Rrev5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (rrev1 @ORArray @Double @0 @0 (rrev1 sin) (rscalar 1.1))

testSin0RrevPP5 :: Assertion
testSin0RrevPP5 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 (rrev1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "negate (sin 1.1) * 1.0"

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
    (rscalar 0.4535961214255773)  -- agrees with the rrev1 version above
    (rfwd1 @ORArray @Double @0 @0 sin (rscalar 1.1))

testSin0RfwdPP0 :: Assertion
testSin0RfwdPP0 = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "1.0 * cos 1.1"

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "1.0 * cos 1.1"  -- agrees with the rrev1 version above

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rproject ((\\h1 -> let h2 = tproject1 h1 ; h3 = tproject2 h1 in [rproject h2 0 * cos (rproject h3 0)]) (ttuple ([1.0], [1.1]))) 0"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rproject ((\\h1 -> [rproject (tproject1 h1) 0 * cos (rproject (tproject2 h1) 0)]) (ttuple ([1.0], [1.1]))) 0"

testSin0Rfwd3 :: Assertion
testSin0Rfwd3 = do
  let f = rfwd1 @(ADVal ORArray) @Double @0 @0 sin
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.9803280960675791))
    (cfwd f (rscalar 1.1) (rscalar 1.1))

testSin0Rfwd4 :: Assertion
testSin0Rfwd4 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0.8988770945225438)  -- agrees with the rrev1 version above
    ((rfwd1 sin . rfwd1 @ORArray @Double @0 @0 sin) (rscalar 1.1))

testSin0RfwdPP4 :: Assertion
testSin0RfwdPP4 = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "1.0 * cos (1.0 * cos 1.1)"  -- agrees with the rrev1 version above

-- Disabled, because different variable names with -O1.
_testSin0RfwdPP4Dual :: Assertion
_testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rproject (\\[x13] [x14] -> [x13 * cos x14]) [[rdualPart 1.0], [rproject (\\[x10] [x11] -> [x10 * cos x11]) [[rdualPart 1.0], [rdualPart 1.1]] 0]] 0"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))  -- agrees with the rrev1 version above
    (rfwd1 @ORArray @Double @0 @0 (rfwd1 sin) (rscalar 1.1))

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 (rfwd1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
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
    (srepl (-0.8912073600614354))
    (srev1 @OSArray @Double @'[] @'[] (srev1 sin) (srepl 1.1))

testSin0RrevPP5S :: Assertion
testSin0RrevPP5S = do
  resetVarCounter
  let a1 = srev1 @(AstShaped PrimalSpan) @Double @'[] @'[] (srev1 sin) (srepl 1.1)
  printAstPrettyS IM.empty (simplifyInlineAstS a1)
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
                        x0 ((rrepl @Double @1 [1] 42))) 1.1)

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 ((rrepl @Double @1 [5] 42))) 1.1)

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
    (rev' (\a0 -> rfold (\x a -> atan2F (sin x) (sin a))
                        (rscalar 2 * a0) (rreplicate 3 a0)) 1.1)

testSin0Fold5 :: Assertion
testSin0Fold5 = do
  assertEqualUpToEpsilon' 1e-10
    (1.2992412552109085 :: OR.Array 0 Double)
    (rev' (\a0 -> rfold (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                          (rsum $ sin $ rsum
                                           $ rtr $ rreplicate 7 a))
                        (rscalar 2 * a0)
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
                                 $ atan2F (rsum (rtr $ sin x))
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
                            x0 (srepl 0)
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
                        x0 ((srepl @'[1] 42))
            in rfromS . f . sfromR)) 1.1)

testSin0Fold2S :: Assertion
testSin0Fold2S = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sfold (\x _a -> sin x)
                        x0 ((srepl @'[5] @Double 42))
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
                        (srepl 84) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold4S :: Assertion
testSin0Fold4S = do
  assertEqualUpToEpsilon' 1e-10
    (-0.7053476446727861 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a -> atan2F (sin x) (sin a))
                        (srepl 2 * a0) (sreplicate @f @3 a0)
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
                                   $ atan2F (sin $ sreplicate @f2 @5 x)
                                            (ssum $ sin $ ssum
                                             $ str $ sreplicate @f2 @7 a)
                             in g)
                        (srepl 2 * a0)
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
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold8rev :: Assertion
testSin0Fold8rev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.200311410593445) :: ORArray Double 0)
    (rrev1 @ORArray @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rscalar 2 * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold8rev2 :: Assertion
testSin0Fold8rev2 = do
  let h = rrev1 @(ADVal ORArray) @Double @0 @2
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
    (rscalar (-2.200311410593445) :: ORArray Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8Srev2 :: Assertion
testSin0Fold8Srev2 = do
  let h = srev1 @(ADVal OSArray)
                (let f :: forall f. ADReadyS f
                       => f Double '[] -> f Double '[2, 5]
                     f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (sscalar 2 * a0)))
                        (sreplicate @_ @3 a0)
                 in f)
  assertEqualUpToEpsilon 1e-10
    (FlipS $ Nested.sscalar 6.182232283434464e-2)  -- seems quite unstable
    (crev h (srepl 0.0001))

testSin0Fold182SrevPP :: Assertion
testSin0Fold182SrevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan)
           (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
                f a0 = sfold @_ @f @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "let h15 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])] [let [v12 @[Natural] @Double @[5], m13 @[Natural] @Double @[1,5]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1] in m13, sreplicate 1.1] in rfromS (sreshape (let [v16 @[Natural] @Double @[5], v17 @[Natural] @Double @[1]] = h15 in v17)) + rfromS (ssum (let [v18 @[Natural] @Double @[5], v19 @[Natural] @Double @[1]] = h15 in v18))"

testSin0Fold18Srev :: Assertion
testSin0Fold18Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.4026418024701366) :: ORArray Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @2
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @2 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8fwd :: Assertion
testSin0Fold8fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.constant [2, 5] (-0.2200311410593445))
    (rfwd1 @ORArray @Double @0 @2
       (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold8fwd2 :: Assertion
testSin0Fold8fwd2 = do
  let h = rfwd1 @(ADVal ORArray) @Double @0 @2
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
  assertEqualUpToEpsilon1 1e-10
    (OR.constant [2, 5] (-0.2200311410593445))
    (rfwd1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8Sfwd2 :: Assertion
testSin0Fold8Sfwd2 = do
  let h = rfwd1 @(ADVal ORArray)
                (let f :: forall f. ADReadyS f
                       => f Double '[] -> f Double '[2, 5]
                     f a0 = sfold @_ @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (srepl 2 * a0)))
                        (sreplicate @_ @3 a0)
                 in rfromS . f . sfromR)
  assertEqualUpToEpsilon1 1e-10
    (OR.constant [2, 5] 10.859933116775313)
    (cfwd h (rscalar 1.1) (rscalar 1.1))

testSin0Fold5Sfwd :: Assertion
testSin0Fold5Sfwd = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 1.4291653807319993)
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[2, 5]
                                   -> f2 Double '[]
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
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (let g :: forall f2. ADReadyS f2
                                   => f2 Double '[] -> f2 Double '[2, 5]
                                   -> f2 Double '[]
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
                        x0 ((rrepl @Double @1 [1] 42)))
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0Scan1ForComparison :: Assertion
testSin0Scan1ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rfromList [x0, sin x0])
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0Scan2 :: Assertion
testSin0Scan2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 ((rrepl @Double @1 [5] 42)))
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0Scan3 :: Assertion
testSin0Scan3 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.360788364276732] :: OR.Array 5 Double)
    (rev' (\a0 -> rscan (\_x a -> sin a)
                        (rreplicate0N [1,1,1,1,1] 84)
                        (rreplicate 3 a0)) (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0Scan4 :: Assertion
testSin0Scan4 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [-0.4458209450295252] :: OR.Array 5 Double)
    (rev' (\a0 -> rscan (\x a -> atan2F (sin x) (sin a))
                        (rreplicate0N [1,1,1,1,1] 2 * a0)
                        (rreplicate 3 a0)) (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0Scan5 :: Assertion
testSin0Scan5 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [4.126141830000979] :: OR.Array 4 Double)
    (rev' (\a0 -> rscan (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7 a))
                        (rreplicate0N [1,1,1,1] 2 * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0))))
          (FlipR $ OR.constant [1,1,1,1] 1.1))

testSin0Scan6 :: Assertion
testSin0Scan6 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [12] :: OR.Array 2 Double)
    (rev' (\a0 -> rscan (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (FlipR $ OR.constant [1,1] 1.1))

testSin0Scan7 :: Assertion
testSin0Scan7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscan (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (FlipR $ OR.constant [1,1] 1.1))

testSin0Scan8 :: Assertion
testSin0Scan8 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev' (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (rreplicate0N [1,1,1] 2 * a0)))
                        (rreplicate 3 a0)) (FlipR $ OR.constant [1,1,1] 1.1))

testSin0Scan8rev :: Assertion
testSin0Scan8rev = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [9.53298735735276])
    (rrev1 @ORArray @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Scan8rev2 :: Assertion
testSin0Scan8rev2 = do
  let h = rrev1 @(ADVal ORArray) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [285.9579482947575])
    (crev h (rscalar 1.1))

testSin0Scan1RevPP1 :: Assertion
testSin0Scan1RevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           ((rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let h10 = [rconst (rfromListLinear [2] [42.0,42.0])] ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h14 = [0, rslice 1 2 v13] in let [x24 @Natural @Double @[], v25 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h27 -> let [x48 @Natural @Double @[]] = tproject1 h27 in let [x49 @Natural @Double @[], x50 @Natural @Double @[], x51 @Natural @Double @[]] = tproject2 h27 in let h52 = [x48, x49] in [cos x50 * (let [x56 @Natural @Double @[], x57 @Natural @Double @[]] = h52 in x57 + let [x58 @Natural @Double @[], x59 @Natural @Double @[]] = h52 in x58), 0]) (\\h60 -> let h92 = [let [x84 @Natural @Double @[], x85 @Natural @Double @[], x86 @Natural @Double @[], x87 @Natural @Double @[]] = tproject2 h60 in x84, let [x88 @Natural @Double @[], x89 @Natural @Double @[], x90 @Natural @Double @[], x91 @Natural @Double @[]] = tproject2 h60 in x89] ; h101 = [let [x93 @Natural @Double @[], x94 @Natural @Double @[], x95 @Natural @Double @[], x96 @Natural @Double @[]] = tproject2 h60 in x95, let [x97 @Natural @Double @[], x98 @Natural @Double @[], x99 @Natural @Double @[], x100 @Natural @Double @[]] = tproject2 h60 in x100] in [(let [x102 @Natural @Double @[], x103 @Natural @Double @[], x104 @Natural @Double @[], x105 @Natural @Double @[]] = tproject1 h60 in x104 * negate (sin (let [x106 @Natural @Double @[], x107 @Natural @Double @[]] = h101 in x106))) * (let [x108 @Natural @Double @[], x109 @Natural @Double @[]] = h92 in x109 + let [x110 @Natural @Double @[], x111 @Natural @Double @[]] = h92 in x110) + (let [x112 @Natural @Double @[], x113 @Natural @Double @[], x114 @Natural @Double @[], x115 @Natural @Double @[]] = tproject1 h60 in x113 + let [x116 @Natural @Double @[], x117 @Natural @Double @[], x118 @Natural @Double @[], x119 @Natural @Double @[]] = tproject1 h60 in x116) * cos (let [x120 @Natural @Double @[], x121 @Natural @Double @[]] = h101 in x120), 0.0]) (\\h122 -> let h152 = [let [x144 @Natural @Double @[], x145 @Natural @Double @[], x146 @Natural @Double @[], x147 @Natural @Double @[]] = tproject2 h122 in x144, let [x148 @Natural @Double @[], x149 @Natural @Double @[], x150 @Natural @Double @[], x151 @Natural @Double @[]] = tproject2 h122 in x149] ; h161 = [let [x153 @Natural @Double @[], x154 @Natural @Double @[], x155 @Natural @Double @[], x156 @Natural @Double @[]] = tproject2 h122 in x155, let [x157 @Natural @Double @[], x158 @Natural @Double @[], x159 @Natural @Double @[], x160 @Natural @Double @[]] = tproject2 h122 in x160] ; x166 = cos (let [x162 @Natural @Double @[], x163 @Natural @Double @[]] = h161 in x162) * let [x164 @Natural @Double @[], x165 @Natural @Double @[]] = tproject1 h122 in x164 in [x166, x166, negate (sin (let [x167 @Natural @Double @[], x168 @Natural @Double @[]] = h161 in x167)) * ((let [x169 @Natural @Double @[], x170 @Natural @Double @[]] = h152 in x170 + let [x171 @Natural @Double @[], x172 @Natural @Double @[]] = h152 in x171) * let [x173 @Natural @Double @[], x174 @Natural @Double @[]] = tproject1 h122 in x173), 0]) [let [x15 @Natural @Double @[], v16 @Natural @Double @[2]] = h14 in x15] [let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = h14 in v18, let [x19 @Natural @Double @[], v20 @Natural @Double @[2], v21 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h175 -> let [x187 @Natural @Double @[]] = tproject1 h175 in let [x191 @Natural @Double @[], x192 @Natural @Double @[]] = let [x188 @Natural @Double @[]] = tproject1 h175 in let [x189 @Natural @Double @[]] = tproject2 h175 in let x190 = sin x188 in [x190, x190] in [x191, x187, x192]) (\\h193 -> let [x212 @Natural @Double @[], x213 @Natural @Double @[]] = tproject1 h193 in let x218 = let [x214 @Natural @Double @[], x215 @Natural @Double @[]] = tproject1 h193 in x214 * cos (let [x216 @Natural @Double @[], x217 @Natural @Double @[]] = tproject2 h193 in x216) in [x218, x212, x218]) (\\h219 -> let [x233 @Natural @Double @[], x234 @Natural @Double @[], x235 @Natural @Double @[]] = tproject1 h219 in let h236 = [x233, x235] in [cos (let [x237 @Natural @Double @[], x238 @Natural @Double @[]] = tproject2 h219 in x237) * (let [x239 @Natural @Double @[], x240 @Natural @Double @[]] = h236 in x240 + let [x241 @Natural @Double @[], x242 @Natural @Double @[]] = h236 in x241) + x234, 0.0]) [1.1] h10 in v20, let [v22 @Natural @Double @[2]] = h10 in v22] in x24 + v13 ! [0]"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v7 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v7 ! [0]) + cos 1.1 * v7 ! [1] + v7 ! [2]"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           ((rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let h7 = [rconst (rfromListLinear [2] [42.0,42.0])] in rappend (rreplicate 1 1.0) (rproject (dmapAccumLDer (SNat @2) (\\h11 -> let [x12 @Natural @Double @[]] = tproject1 h11 in let [x13 @Natural @Double @[], x14 @Natural @Double @[], x15 @Natural @Double @[]] = tproject2 h11 in let x30 = x12 * cos x14 in [x30, x30]) (\\h31 -> let h46 = [rproject (tproject2 h31) 2, rproject (tproject2 h31) 3] ; x52 = rproject (tproject1 h31) 0 * cos (rproject h46 0) + (rproject (tproject1 h31) 2 * negate (sin (rproject h46 0))) * rproject (tproject2 h31) 0 in [x52, x52]) (\\h53 -> let h67 = [rproject (tproject2 h53) 2, rproject (tproject2 h53) 3] ; x73 = rproject (tproject1 h53) 1 + rproject (tproject1 h53) 0 in [cos (rproject h67 0) * x73, 0, negate (sin (rproject h67 0)) * (rproject (tproject2 h53) 0 * x73), 0]) [1.0] [rreplicate 2 0.0, rproject (dmapAccumLDer (SNat @2) (\\h74 -> let [x75 @Natural @Double @[]] = tproject1 h74 in let [x83 @Natural @Double @[], x84 @Natural @Double @[]] = let [x80 @Natural @Double @[]] = tproject1 h74 in let [x81 @Natural @Double @[]] = tproject2 h74 in let x82 = sin x80 in [x82, x82] in [x83, x75, x84]) (\\h85 -> let [x86 @Natural @Double @[], x87 @Natural @Double @[]] = tproject1 h85 in let x92 = let [x88 @Natural @Double @[], x89 @Natural @Double @[]] = tproject1 h85 in x88 * cos (let [x90 @Natural @Double @[], x91 @Natural @Double @[]] = tproject2 h85 in x90) in [x92, x86, x92]) (\\h95 -> let [x96 @Natural @Double @[], x97 @Natural @Double @[], x98 @Natural @Double @[]] = tproject1 h95 in let h106 = [x96, x98] in [cos (let [x107 @Natural @Double @[], x108 @Natural @Double @[]] = tproject2 h95 in x107) * (let [x109 @Natural @Double @[], x110 @Natural @Double @[]] = h106 in x110 + let [x111 @Natural @Double @[], x112 @Natural @Double @[]] = h106 in x111) + x97, 0.0]) [1.1] h7) 1, rproject h7 0]) 1)"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           ((rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "rproject ((\\h1 -> let h7 = [rconst (rfromListLinear [2] [42.0,42.0])] in [rappend (rreplicate 1 (rproject (tproject1 h1) 0)) (rproject (dmapAccumLDer (SNat @2) (\\h11 -> let [x12 @Natural @Double @[]] = tproject1 h11 in let [x13 @Natural @Double @[], x14 @Natural @Double @[], x15 @Natural @Double @[]] = tproject2 h11 in let x30 = x12 * cos x14 in [x30, x30]) (\\h31 -> let h46 = [rproject (tproject2 h31) 2, rproject (tproject2 h31) 3] ; x52 = rproject (tproject1 h31) 0 * cos (rproject h46 0) + (rproject (tproject1 h31) 2 * negate (sin (rproject h46 0))) * rproject (tproject2 h31) 0 in [x52, x52]) (\\h53 -> let h67 = [rproject (tproject2 h53) 2, rproject (tproject2 h53) 3] ; x73 = rproject (tproject1 h53) 1 + rproject (tproject1 h53) 0 in [cos (rproject h67 0) * x73, 0, negate (sin (rproject h67 0)) * (rproject (tproject2 h53) 0 * x73), 0]) [rproject (tproject1 h1) 0] [rreplicate 2 0.0, rproject (dmapAccumLDer (SNat @2) (\\h74 -> let [x75 @Natural @Double @[]] = tproject1 h74 in let [x83 @Natural @Double @[], x84 @Natural @Double @[]] = let [x80 @Natural @Double @[]] = tproject1 h74 in let [x81 @Natural @Double @[]] = tproject2 h74 in let x82 = sin x80 in [x82, x82] in [x83, x75, x84]) (\\h85 -> let [x86 @Natural @Double @[], x87 @Natural @Double @[]] = tproject1 h85 in let x92 = let [x88 @Natural @Double @[], x89 @Natural @Double @[]] = tproject1 h85 in x88 * cos (let [x90 @Natural @Double @[], x91 @Natural @Double @[]] = tproject2 h85 in x90) in [x92, x86, x92]) (\\h95 -> let [x96 @Natural @Double @[], x97 @Natural @Double @[], x98 @Natural @Double @[]] = tproject1 h95 in let h106 = [x96, x98] in [cos (let [x107 @Natural @Double @[], x108 @Natural @Double @[]] = tproject2 h95 in x107) * (let [x109 @Natural @Double @[], x110 @Natural @Double @[]] = h106 in x110 + let [x111 @Natural @Double @[], x112 @Natural @Double @[]] = h106 in x111) + x97, 0.0]) [rproject (tproject2 h1) 0] h7) 1, rproject h7 0]) 1)]) (ttuple ([1.0], [1.1]))) 0"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h10 = [rconst (rfromListLinear [2] [5.0,7.0])] ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h14 = [0, rslice 1 2 v13] in let [x24 @Natural @Double @[], v25 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x15 @Natural @Double @[], v16 @Natural @Double @[2]] = h14 in x15] [let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = h14 in v18, let [x19 @Natural @Double @[], v20 @Natural @Double @[2], v21 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h10 in v20, let [v22 @Natural @Double @[2]] = h10 in v22] in x24 + v13 ! [0]"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7])))
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v6 x9 -> let h4 = [rconst (rfromListLinear [2] [5.0,7.0])] ; h7 = [0, rslice 1 2 v6] in [rproject (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [rproject h7 0] [rproject h7 1, rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x9] h4) 1, rproject h4 0]) 0 + v6 ! [0]]"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0])
                 (rscalar 1.1)
  printArtifactPretty @(TKR Double 1) IM.empty (simplifyArtifact art)
    @?= "\\v3 x4 -> [cos x4 * (cos (sin x4 - 5.0) * v3 ! [0]) + cos x4 * v3 ! [1] + v3 ! [2]]"

testSin0Scan1Rev2 :: Assertion
testSin0Scan1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                    (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) 1.1)

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
                           (rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h13 = [rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0])] ; v16 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h17 = [0, rslice 1 2 v16] ; h26 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x18 @Natural @Double @[], v19 @Natural @Double @[2]] = h17 in x18] [let [x20 @Natural @Double @[], v21 @Natural @Double @[2]] = h17 in v21, let [x22 @Natural @Double @[], v23 @Natural @Double @[2], v24 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h13 in v23, let [v25 @Natural @Double @[2]] = h13 in v25] ; v29 = let [x27 @Natural @Double @[], v28 @Natural @Double @[2]] = h26 in v28 in 5.0 * v29 ! [0] + 7.0 * v29 ! [1] + let [x30 @Natural @Double @[], v31 @Natural @Double @[2]] = h26 in x30 + v16 ! [0]"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v11 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; x12 = v11 ! [1] ; x13 = v11 ! [0] ; x14 = cos (sin 1.1 - 1.1 * 5.0) * x13 in cos 1.1 * x14 + 5.0 * (-1.0 * x14) + 7.0 * (-1.0 * x13) + cos 1.1 * x12 + 5.0 * (-1.0 * x12) + v11 ! [2]"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h7 = [rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0])] in rappend (rreplicate 1 1.0) (rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h7) 1, rproject h7 0]) 1)"

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
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [1] [1.0])
    (rfwd1 @ORArray @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscan (\x _a -> sin x)
                      x0 (rzero @f @Double (0 :$: ZSR))
     in f) (rscalar 1.1))

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @ORArray @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 ((rrepl @Double @1 [1] 42)))
          (rscalar 1.1))

testSin0Scan1FwdForComparison :: Assertion
testSin0Scan1FwdForComparison = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @ORArray @Double @0 @1
    (\x0 -> rfromList [x0, sin x0]) (rscalar 1.1))

testSin0Scan8fwd :: Assertion
testSin0Scan8fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @ORArray @Double @0 @3
       (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Scan8fwd2 :: Assertion
testSin0Scan8fwd2 = do
  let h = rfwd1 @(ADVal ORArray) @Double @0 @3
        (\a0 -> rscan (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 (2 * a0)))
                        (rreplicate 3 a0))
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [285.95794829475744])
    (crev h (rscalar 1.1))

testUnitriangular0PP :: Assertion
testUnitriangular0PP = do
  resetVarCounter
  let k = 1000000
      a1 = rbuild1 @(AstRanked FullSpan) @Double @1 k
           $ \i -> rbuild1 k
           $ \j -> ifF (i <=. j) 0 1
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rgather [1000000,1000000] (rconst (rfromListLinear [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1])"

unitriangular1 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> IShR k -> ranked rk (2 + k)
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
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromVector (fromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))])) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6])"

unitriangular2 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> IShR k -> ranked rk (2 + k)
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
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromVector (fromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))])) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4])"

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
                dlet
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
            ( GoodScalar rn, KnownShS sh, KnownNat k, ShapedTensor shaped
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
              dlet
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
    (srepl 1)
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
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
           in f) (srepl 1.1))

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[7]
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
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
                       $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
                          (dmkHVector $ V.fromList [])) $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
                          (dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
                          (dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
                          (dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

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
           in f) (rscalar 1.1))

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
    (srepl 0.4535961214255773)
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in f) (srepl 1.1))

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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[] (srepl 3)
                                      , DynamicShaped x0 ])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
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
                                          $ sreplicate @_ @3 (sin x / srepl 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1, 2] (srepl 0))
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
                                          $ sreplicate @_ @3 (sin x / srepl 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
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
                                             (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
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
                                             (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sbuild1 @_ @_ @4 $ \i ->
                                             sfromD (a V.! 1)
                                             - sin x1 / sreplicate @_ @3
                                                          (srepl 1 + sfromIndex0 i) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped $ x0 / (srepl 1 + sfromIntegral (sconstant (sfromR j)))
                                      , DynamicShaped $ sreplicate @_ @3 x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 3]
                                           $ sreplicate0N @_ @_ @'[5, 3]
                                               (sfromIntegral (sconstant (sfromR j)))
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ]))
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
                                             (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ])
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
                                                   / sin x / srepl 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1)))
                                           + sin x / srepl 3 ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN531 :: Assertion
testSin0rmapAccumRD01SN531 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3]
       [-0.4284609293514655,0.2047077016162759,0.9242422110631052])
    (rev' (let f :: forall f. ADReadyS f => f Double '[3] -> f Double '[2, 3]
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
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
                                         $ ingestData [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - sreplicate @_ @7
                                                 (ssum
                                                  $ sin x - sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ srepl 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (ingestData
                                           [0.4, -0.01, -0.3, 0.2, 0.5, 1.3]) ])
           in rfromS . f . sfromR) (FlipR $ OR.fromList [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531a :: Assertion
testSin0rmapAccumRD01SN531a = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3]
       [1.8478609886246988,-22.194216099801963,-40.72162125038692])
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[3] -> f Double '[2, 2, 2, 3]
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
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
                                             [srepl 0.01, ssum @_ @_ @6 x2, srepl 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - sfromD (a V.! 1)))
                                       , DynamicShaped
                                         $ srepl 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sreplicate @_ @3 (sfromIntegral (sconstant (sfromR j))))
                                      , DynamicShaped
                                        $ sreplicate @_ @6 (sfromIntegral (sconstant (sfromR i)))
                                          - sflatten (sappend x0 x0) ] )
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [srepl (-0.1), sreshape @_ @_ @'[] @'[1] $ sfromIntegral (sconstant (sfromR j))])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sscalar 0.4, sscalar (-0.01), sscalar (-0.3), sfromIntegral (sconstant (sfromR i)), sscalar 0.5, sscalar 1.3]) ])))
           in rfromS . f . sfromR) (FlipR $ OR.fromList [3] [1.1, 2, 3.14]))

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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) [] ]))))
                        $ \ !d -> rfromD $ d V.! 0
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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [1]) [0] ]))))
                        $ \ !d -> rfromD $ d V.! 0
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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) [] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (let [x15 @[Natural] @Double @[], v16 @Natural @Double @[0]] = dmapAccumLDer (SNat @0) (\\h17 -> let [x29 @[Natural] @Double @[]] = tproject1 h17 in let [x30 @[Natural] @Double @[], x31 @Natural @Double @[]] = tproject2 h17 in [x29, 0]) (\\h33 -> [let [x43 @[Natural] @Double @[], x44 @[Natural] @Double @[], x45 @Natural @Double @[]] = tproject1 h33 in x43, 0.0]) (\\h46 -> [let [x56 @[Natural] @Double @[], x57 @Natural @Double @[]] = tproject1 h46 in x56, 0, 0]) [4.0] [let [x12 @[Natural] @Double @[], v13 @[Natural] @Double @[0]] = dmapAccumRDer (SNat @0) (\\h58 -> let [x67 @[Natural] @Double @[]] = tproject1 h58 in let [x70 @[Natural] @Double @[]] = let [x68 @[Natural] @Double @[]] = tproject1 h58 in let [x69 @Natural @Double @[]] = tproject2 h58 in [x68] in [x70, x67]) (\\h71 -> let [x83 @[Natural] @Double @[], x84 @Natural @Double @[]] = tproject1 h71 in [let [x85 @[Natural] @Double @[], x86 @Natural @Double @[]] = tproject1 h71 in x85, x83]) (\\h88 -> let [x95 @[Natural] @Double @[], x96 @[Natural] @Double @[]] = tproject1 h88 in [0.0 + x96 + x95, 0.0]) [1.1] [rconst (rfromListLinear [0] [])] in v13, rconst (rfromListLinear [0] [])] in x15)]"

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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[sproject (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] [sproject (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (sfromListLinear [1] [0.0])]) 1, sconst @[1] (sfromListLinear [1] [0.0])]) 0]"

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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "(\\h1 -> [sproject (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (sproject (tproject1 h1) 0))] [sproject (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 h1) 0] [sconst @[1] (sfromListLinear [1] [0.0])]) 1, sconst @[1] (sfromListLinear [1] [0.0])]) 0]) (ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]))"

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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [1]) [0] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorSimple
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rletHVectorIn (dmapAccumLDer (SNat @1) (\\h17 -> dletHVectorInHVector (tproject1 h17) (\\[x29 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h17) (\\[x30 @Natural @Double @[], x31 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x29, DynamicRankedDummy])))) (\\h33 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h33) (\\[x43 @Natural @Double @[], x44 @Natural @Double @[], x45 @Natural @Double @[]] -> x43)), DynamicRanked 0.0])) (\\h46 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h46) (\\[x56 @Natural @Double @[], x57 @Natural @Double @[]] -> x56)), DynamicRankedDummy, DynamicRankedDummy])) dmkHVector (fromList [DynamicRanked (rconstant 4.0)]) dmkHVector (fromList [DynamicRanked (rletHVectorIn (dmapAccumRDer (SNat @1) (\\h58 -> dletHVectorInHVector (tproject1 h58) (\\[x67 @Natural @Double @[]] -> dletHVectorInHVector (dletHVectorInHVector (tproject1 h58) (\\[x68 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h58) (\\[x69 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x68])))) (\\[x70 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x70, DynamicRanked x67])))) (\\h71 -> dletHVectorInHVector (tproject1 h71) (\\[x83 @Natural @Double @[], x84 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h71) (\\[x85 @Natural @Double @[], x86 @Natural @Double @[]] -> x85)), DynamicRanked x83]))) (\\h88 -> dletHVectorInHVector (tproject1 h88) (\\[x95 @Natural @Double @[], x96 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (x95 + x96), DynamicRanked 0.0]))) dmkHVector (fromList [DynamicRanked (rconstant 1.1)]) dmkHVector (fromList [DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x12 @Natural @Double @[], v13 @Natural @Double @[1]] -> v13)), DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x15 @Natural @Double @[], v16 @Natural @Double @[1]] -> x15))])"

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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) [] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (let [m24 @[Natural] @Double @[2,2], t25 @Natural @Double @[0,2,2]] = dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i18] -> [i18])] [let [m21 @[Natural] @Double @[2,2], t22 @[Natural] @Double @[0,2,2]] = dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in t22, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in m24)))]"

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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[ssum (ssum (sproject (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i15] -> [i15])] [sproject (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]) 1, stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]) 0))]"

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
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [1]) [0] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (let [m21 @Natural @Double @[2,2], t22 @Natural @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] [let [m18 @Natural @Double @[2,2], t19 @Natural @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in t19, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in rgather [4] m21 (\\[i23] -> [remF (quotF i23 2) 2, remF i23 2]))]"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (-1.8866871148429984)
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2, 2]
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
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
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sfromIntegral (sconstant (sfromR j))) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIntegral (sconstant (sfromR i))]) ])))
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
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ]
                           in g)
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sconstant (sfromR j))) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIntegral (sconstant (sfromR i))]) ])))
      in f . sfromR) ((rscalar 1.1) :: ORArray Double 0))

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
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
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
                                                   / sin x / srepl 3))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 0)))
                                           + sin x / srepl 3 ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN55acc :: Assertion
testSin0rmapAccumRD01SN55acc = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [3] [-21.0,-42.0,-21.0])
    (rev' (let f :: forall f. ADReadyS f => f Double '[3] -> f Double '[2, 3]
               f x0 = (\res -> srepl 2 - str (sreplicate @_ @3
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
                                let x = sreplicate @g @3 (sscalar 2)
                                in dmkHVector
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
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / (sreplicate0N (sscalar 3)))) ]
                           in g)
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sindex0 x0 [1], sscalar (-0.01), sscalar (-0.3), ssum x0, sscalar 0.5, sscalar 1.3]) ])
           in rfromS . f . sfromR) (FlipR $ OR.fromList [3] [1.1, 2, 3.14]))

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
                                        [ DynamicShaped @Double @'[] (sscalar 1)
                                        , DynamicShaped $ sin x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2] knownShS [0.4989557335681351,1.1])
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
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
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
                                        [ DynamicShaped @Double @'[] (sscalar 1)
                                        , DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[5] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[1] knownShS [1.1])
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
                                        [ DynamicShaped @Double @'[] (sscalar 1)
                                        , DynamicShaped x ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[1] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN6 :: Assertion
testSin0rmapAccumRD01SN6 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
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
                                           `atan2F` smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1))
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[2]
                                                      (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in hVectorADValToADVal . f) (sscalar 1.1))

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
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
                                             (sin x / srepl 6
                                              + sindex0 @_ @_ @'[2]
                                                        (sfromD (a V.! 2)) [1]
                                                / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 6) ]
                           in g)
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in hVectorADValToADVal . f @(ADVal OSArray)) (sscalar 1.1))

testSin0ScanD1 :: Assertion
testSin0ScanD1 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ (rrepl @Double @1 [1] 42)))
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ (rrepl @Double @1 [5] 42)))
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

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
                              $ (rrepl @Double @6
                                          [3, 4, 5, 6, 7, 8] 32) ]))
                         (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0ScanD4 :: Assertion
testSin0ScanD4 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [-0.4458209450295252] :: OR.Array 5 Double)
    (rev' (\a0 -> rscanZip (\x a -> atan2F (sin x)
                                        (sin $ rfromD (a V.! 0)))
                         (V.fromList [voidFromSh @Double
                                        (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                         (rreplicate0N [1,1,1,1,1] 2 * a0)
                         (V.singleton $ DynamicRanked
                          $ rreplicate 3 a0)) (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0ScanD5 :: Assertion
testSin0ScanD5 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [4.126141830000979] :: OR.Array 4 Double)
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
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
          (FlipR $ OR.constant [1,1,1,1] 1.1))

testSin0ScanD51 :: Assertion
testSin0ScanD51 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [319.68688158967257] :: OR.Array 4 Double)
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
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
          (FlipR $ OR.constant [1,1,1,1] 1.1))

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
                          $ atan2F (sin $ sreplicate @f2 @5 x)
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
                   (sreplicate0N @_ @_ @[1,1,1,1] (sscalar 2) * a0)
                   (V.fromList
                      [ DynamicShaped
                        $ sreplicate @f @3 (sreplicate @f @2 (sreplicate @f @5 a0))
                      , DynamicRanked $ rfromS
                        $ sreplicate @f @3 (sreplicate @f @8 (sreplicate @f @3 a0)) ]
                   )
           in rfromS . f . sfromR) (FlipR $ OR.constant [1,1,1,1] 1.1))

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
                          $ rreplicate 2 a0)) (FlipR $ OR.constant [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZSR)])
                         (rreplicate 2 (rreplicate 5 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (FlipR $ OR.constant [1,1] 1.1))

testSin0ScanD8 :: Assertion
testSin0ScanD8 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev' (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] 2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
                       (FlipR $ OR.constant [1,1,1] 1.1))

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
                                 $ atan2F (rsum (rtr $ sin x))
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
       (FlipR $ OR.constant [1,1,1] 1.1))

testSin0ScanD8rev :: Assertion
testSin0ScanD8rev = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [9.53298735735276])
    (rrev1 @ORArray @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8rev2 :: Assertion
testSin0ScanD8rev2 = do
  let h = rrev1 @(ADVal ORArray) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [285.9579482947575])
    (crev h (rscalar 1.1))

testSin0ScanD8rev3 :: Assertion
testSin0ScanD8rev3 = do
  let h :: forall f. ADReady f => f Double 0 -> f Double 0
      h = rrev1 @f @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
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
                                 $ atan2F (rsum (rtr $ sin x))
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
                               $ (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h10 = [rconst (rfromListLinear [2] [42.0,42.0])] ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h14 = [0, rslice 1 2 v13] in let [x24 @Natural @Double @[], v25 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x15 @Natural @Double @[], v16 @Natural @Double @[2]] = h14 in x15] [let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = h14 in v18, let [x19 @Natural @Double @[], v20 @Natural @Double @[2], v21 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h10 in v20, let [v22 @Natural @Double @[2]] = h10 in v22] in x24 + v13 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               $ (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h7 = [rconst (rfromListLinear [2] [42.0,42.0])] in rappend (rreplicate 1 1.0) (rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h7) 1, rproject h7 0]) 1)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h10 = [rconst (rfromListLinear [2] [5.0,7.0])] ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h14 = [0, rslice 1 2 v13] in let [x24 @Natural @Double @[], v25 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x15 @Natural @Double @[], v16 @Natural @Double @[2]] = h14 in x15] [let [x17 @Natural @Double @[], v18 @Natural @Double @[2]] = h14 in v18, let [x19 @Natural @Double @[], v20 @Natural @Double @[2], v21 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h10 in v20, let [v22 @Natural @Double @[2]] = h10 in v22] in x24 + v13 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h7 = [rconst (rfromListLinear [2] [5.0,7.0])] in rappend (rreplicate 1 1.0) (rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h7) 1, rproject h7 0]) 1)"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [2.417297824578748] :: OR.Array 0 Double)
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconst (Nested.Internal.sfromListPrimLinear @Double @'[2, 2] knownShS [5, 7, 3, 4])
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
                                    (rfromList [x0 * 5, x0]))) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInlineAst a1))
    @?= 10846

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let h7 = [rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0])] in rappend (rreplicate 1 1.0) (rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h7) 1, rproject h7 0]) 1)"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [1] [1.0])
    (rfwd1 @ORArray @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [voidFromSh @Double ZSR])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$: ZSR))
     in f) (rscalar 1.1))

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [2] [1.0,0.4535961214255773])
    (rfwd1 @ORArray @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (V.fromList [ voidFromSh @Double ZSR
                               , voidFromSh @Double (3 :$: 4 :$: ZSR)])
                   x0 (V.fromList
                         [ DynamicRanked
                           $ (rrepl @Double @1 [1] 42)
                         , DynamicRanked
                           $ (rrepl @Double @3 [1, 3, 4] 32) ]))
          (rscalar 1.1))

testSin0ScanD8fwd :: Assertion
testSin0ScanD8fwd = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @ORArray @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                      (V.fromList [voidFromSh @Double ZSR])
                      (rreplicate 2 (rreplicate 5 (2 * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8fwdMapAccum :: Assertion
testSin0ScanD8fwdMapAccum = do
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @ORArray @Double @0 @3 @Double
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
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a))
                           , DynamicRanked x ]
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5 (2 * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0)) (rscalar 1.1))

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal ORArray) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon1 1e-10
    (OR.fromList [] [285.95794829475744])
    (crev h (rscalar 1.1))

testSin0FoldNestedS1 :: Assertion
testSin0FoldNestedS1 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
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
    (g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let h7 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [sproject (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1]) 1, sreplicate 1.1] in [ssum (sproject h7 1) + sproject h7 0]"

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
    (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h12 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [let [x9 @Natural @Double @[], v10 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in v10, rreplicate 11 1.1] in [rsum (let [x13 @Natural @Double @[], v14 @Natural @Double @[11]] = h12 in v14) + let [x15 @Natural @Double @[], v16 @Natural @Double @[11]] = h12 in x15]"

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
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h12 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [let [x9 @Natural @Double @[], v10 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in v10, rreplicate 11 1.1] in [rsum (let [x13 @Natural @Double @[], v14 @Natural @Double @[11]] = h12 in v14) + let [x15 @Natural @Double @[], v16 @Natural @Double @[11]] = h12 in x15]"

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
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h12 = dmapAccumRDer (SNat @11) (\\h17 -> let [x47 @Natural @Double @[]] = tproject1 h17 in let [x48 @Natural @Double @[], x49 @Natural @Double @[]] = tproject2 h17 in let h50 = [x48, x49] ; h59 = dmapAccumRDer (SNat @22) (\\h64 -> let [x88 @Natural @Double @[]] = tproject1 h64 in let [x89 @Natural @Double @[], x90 @Natural @Double @[]] = tproject2 h64 in let x91 = cos x90 in [x88, recip (x91 * x91) * x88]) (\\h92 -> let h147 = [let [x141 @Natural @Double @[], x142 @Natural @Double @[], x143 @Natural @Double @[]] = tproject2 h92 in x142, let [x144 @Natural @Double @[], x145 @Natural @Double @[], x146 @Natural @Double @[]] = tproject2 h92 in x146] ; x150 = cos (let [x148 @Natural @Double @[], x149 @Natural @Double @[]] = h147 in x149) ; x151 = x150 * x150 ; x157 = let [x152 @Natural @Double @[], x153 @Natural @Double @[], x154 @Natural @Double @[]] = tproject1 h92 in x154 * negate (sin (let [x155 @Natural @Double @[], x156 @Natural @Double @[]] = h147 in x156)) in [let [x158 @Natural @Double @[], x159 @Natural @Double @[], x160 @Natural @Double @[]] = tproject1 h92 in x158, ((x157 * x150 + x157 * x150) * negate (recip (x151 * x151))) * let [x161 @Natural @Double @[], x162 @Natural @Double @[], x163 @Natural @Double @[]] = tproject2 h92 in x161 + let [x164 @Natural @Double @[], x165 @Natural @Double @[], x166 @Natural @Double @[]] = tproject1 h92 in x164 * recip x151]) (\\h167 -> let h216 = [let [x210 @Natural @Double @[], x211 @Natural @Double @[], x212 @Natural @Double @[]] = tproject2 h167 in x211, let [x213 @Natural @Double @[], x214 @Natural @Double @[], x215 @Natural @Double @[]] = tproject2 h167 in x215] ; x219 = cos (let [x217 @Natural @Double @[], x218 @Natural @Double @[]] = h216 in x218) ; x220 = x219 * x219 ; x226 = negate (recip (x220 * x220)) * (let [x221 @Natural @Double @[], x222 @Natural @Double @[], x223 @Natural @Double @[]] = tproject2 h167 in x221 * let [x224 @Natural @Double @[], x225 @Natural @Double @[]] = tproject1 h167 in x225) in [recip x220 * let [x227 @Natural @Double @[], x228 @Natural @Double @[]] = tproject1 h167 in x228 + let [x229 @Natural @Double @[], x230 @Natural @Double @[]] = tproject1 h167 in x229, 0, negate (sin (let [x231 @Natural @Double @[], x232 @Natural @Double @[]] = h216 in x232)) * (x219 * x226 + x219 * x226)]) [x47] [let [x55 @Natural @Double @[], v56 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h233 -> let [x249 @Natural @Double @[]] = tproject1 h233 in let [x252 @Natural @Double @[]] = let [x250 @Natural @Double @[]] = tproject1 h233 in let [x251 @Natural @Double @[]] = tproject2 h233 in [x250 + tan x251] in [x252, x249]) (\\h253 -> let [x285 @Natural @Double @[], x286 @Natural @Double @[]] = tproject1 h253 in let x289 = cos (let [x287 @Natural @Double @[], x288 @Natural @Double @[]] = tproject2 h253 in x288) in [let [x290 @Natural @Double @[], x291 @Natural @Double @[]] = tproject1 h253 in x290 + let [x292 @Natural @Double @[], x293 @Natural @Double @[]] = tproject1 h253 in x293 * recip (x289 * x289), x285]) (\\h294 -> let [x311 @Natural @Double @[], x312 @Natural @Double @[]] = tproject1 h294 in let x315 = cos (let [x313 @Natural @Double @[], x314 @Natural @Double @[]] = tproject2 h294 in x314) in [x311 + x312, recip (x315 * x315) * x311]) [let [x51 @Natural @Double @[], x52 @Natural @Double @[]] = h50 in x52] [rreplicate 22 (let [x53 @Natural @Double @[], x54 @Natural @Double @[]] = h50 in x53)] in v56, rreplicate 22 (let [x57 @Natural @Double @[], x58 @Natural @Double @[]] = h50 in x57)] in [rsum (let [x60 @Natural @Double @[], v61 @Natural @Double @[22]] = h59 in v61), let [x62 @Natural @Double @[], v63 @Natural @Double @[22]] = h59 in x62]) (\\h316 -> let h353 = [let [x347 @Natural @Double @[], x348 @Natural @Double @[], x349 @Natural @Double @[]] = tproject2 h316 in x348, let [x350 @Natural @Double @[], x351 @Natural @Double @[], x352 @Natural @Double @[]] = tproject2 h316 in x352] ; h358 = dmapAccumLDer (SNat @22) (\\h399 -> let [x413 @Natural @Double @[]] = tproject1 h399 in let [x418 @Natural @Double @[], x419 @Natural @Double @[]] = let [x414 @Natural @Double @[]] = tproject1 h399 in let [x417 @Natural @Double @[]] = let [x415 @Natural @Double @[]] = tproject1 h399 in let [x416 @Natural @Double @[]] = tproject2 h399 in [x415 + tan x416] in [x417, x414] in [x418, x413, x419]) (\\h420 -> let [x445 @Natural @Double @[], x446 @Natural @Double @[]] = tproject1 h420 in let [x456 @Natural @Double @[], x457 @Natural @Double @[]] = let [x447 @Natural @Double @[], x448 @Natural @Double @[]] = tproject1 h420 in let x451 = cos (let [x449 @Natural @Double @[], x450 @Natural @Double @[]] = tproject2 h420 in x450) in [let [x452 @Natural @Double @[], x453 @Natural @Double @[]] = tproject1 h420 in x452 + let [x454 @Natural @Double @[], x455 @Natural @Double @[]] = tproject1 h420 in x455 * recip (x451 * x451), x447] in [x456, x445, x457]) (\\h458 -> let [x476 @Natural @Double @[], x477 @Natural @Double @[], x478 @Natural @Double @[]] = tproject1 h458 in let x481 = cos (let [x479 @Natural @Double @[], x480 @Natural @Double @[]] = tproject2 h458 in x480) in [x477 + x476 + x478, recip (x481 * x481) * x476]) [let [x354 @Natural @Double @[], x355 @Natural @Double @[]] = h353 in x355] [rreplicate 22 (let [x356 @Natural @Double @[], x357 @Natural @Double @[]] = h353 in x356)] ; h364 = [let [x359 @Natural @Double @[], v360 @Natural @Double @[22], v361 @Natural @Double @[22]] = h358 in v361, rreplicate 22 (let [x362 @Natural @Double @[], x363 @Natural @Double @[]] = h353 in x362)] ; h394 = dmapAccumRDer (SNat @22) (\\h482 -> let [x543 @Natural @Double @[]] = tproject1 h482 in let [x544 @Natural @Double @[], x545 @Natural @Double @[], x546 @Natural @Double @[], x547 @Natural @Double @[], x548 @Natural @Double @[]] = tproject2 h482 in let h549 = [x547, x548] ; x552 = cos (let [x550 @Natural @Double @[], x551 @Natural @Double @[]] = h549 in x551) ; x553 = x552 * x552 ; x556 = x545 * negate (sin (let [x554 @Natural @Double @[], x555 @Natural @Double @[]] = h549 in x555)) in [x543, ((x556 * x552 + x556 * x552) * negate (recip (x553 * x553))) * x546 + x543 * recip x553]) (\\h557 -> let h633 = [let [x621 @Natural @Double @[], x622 @Natural @Double @[], x623 @Natural @Double @[], x624 @Natural @Double @[], x625 @Natural @Double @[], x626 @Natural @Double @[]] = tproject2 h557 in x625, let [x627 @Natural @Double @[], x628 @Natural @Double @[], x629 @Natural @Double @[], x630 @Natural @Double @[], x631 @Natural @Double @[], x632 @Natural @Double @[]] = tproject2 h557 in x632] ; x636 = cos (let [x634 @Natural @Double @[], x635 @Natural @Double @[]] = h633 in x635) ; x637 = x636 * x636 ; x640 = negate (sin (let [x638 @Natural @Double @[], x639 @Natural @Double @[]] = h633 in x639)) ; x647 = let [x641 @Natural @Double @[], x642 @Natural @Double @[], x643 @Natural @Double @[], x644 @Natural @Double @[], x645 @Natural @Double @[], x646 @Natural @Double @[]] = tproject2 h557 in x643 * x640 ; x648 = x637 * x637 ; x649 = x647 * x636 + x647 * x636 ; x650 = negate (recip x648) ; x671 = let [x651 @Natural @Double @[], x652 @Natural @Double @[], x653 @Natural @Double @[], x654 @Natural @Double @[], x655 @Natural @Double @[], x656 @Natural @Double @[]] = tproject1 h557 in x653 * x640 + ((let [x657 @Natural @Double @[], x658 @Natural @Double @[], x659 @Natural @Double @[], x660 @Natural @Double @[], x661 @Natural @Double @[], x662 @Natural @Double @[]] = tproject1 h557 in x662 * cos (let [x663 @Natural @Double @[], x664 @Natural @Double @[]] = h633 in x664)) * -1.0) * let [x665 @Natural @Double @[], x666 @Natural @Double @[], x667 @Natural @Double @[], x668 @Natural @Double @[], x669 @Natural @Double @[], x670 @Natural @Double @[]] = tproject2 h557 in x667 ; x680 = let [x672 @Natural @Double @[], x673 @Natural @Double @[], x674 @Natural @Double @[], x675 @Natural @Double @[], x676 @Natural @Double @[], x677 @Natural @Double @[]] = tproject1 h557 in x677 * negate (sin (let [x678 @Natural @Double @[], x679 @Natural @Double @[]] = h633 in x679)) ; x681 = x680 * x636 + x680 * x636 in [let [x682 @Natural @Double @[], x683 @Natural @Double @[], x684 @Natural @Double @[], x685 @Natural @Double @[], x686 @Natural @Double @[], x687 @Natural @Double @[]] = tproject1 h557 in x682, ((x671 * x636 + x680 * x647 + x671 * x636 + x680 * x647) * x650 + (((x681 * x637 + x681 * x637) * negate (recip (x648 * x648))) * -1.0) * x649) * let [x688 @Natural @Double @[], x689 @Natural @Double @[], x690 @Natural @Double @[], x691 @Natural @Double @[], x692 @Natural @Double @[], x693 @Natural @Double @[]] = tproject2 h557 in x691 + let [x694 @Natural @Double @[], x695 @Natural @Double @[], x696 @Natural @Double @[], x697 @Natural @Double @[], x698 @Natural @Double @[], x699 @Natural @Double @[]] = tproject1 h557 in x697 * (x649 * x650) + let [x700 @Natural @Double @[], x701 @Natural @Double @[], x702 @Natural @Double @[], x703 @Natural @Double @[], x704 @Natural @Double @[], x705 @Natural @Double @[]] = tproject1 h557 in x700 * recip x637 + (x681 * negate (recip (x637 * x637))) * let [x706 @Natural @Double @[], x707 @Natural @Double @[], x708 @Natural @Double @[], x709 @Natural @Double @[], x710 @Natural @Double @[], x711 @Natural @Double @[]] = tproject2 h557 in x706]) (\\h712 -> let h777 = [let [x765 @Natural @Double @[], x766 @Natural @Double @[], x767 @Natural @Double @[], x768 @Natural @Double @[], x769 @Natural @Double @[], x770 @Natural @Double @[]] = tproject2 h712 in x769, let [x771 @Natural @Double @[], x772 @Natural @Double @[], x773 @Natural @Double @[], x774 @Natural @Double @[], x775 @Natural @Double @[], x776 @Natural @Double @[]] = tproject2 h712 in x776] ; x780 = cos (let [x778 @Natural @Double @[], x779 @Natural @Double @[]] = h777 in x779) ; x781 = x780 * x780 ; x784 = negate (sin (let [x782 @Natural @Double @[], x783 @Natural @Double @[]] = h777 in x783)) ; x791 = let [x785 @Natural @Double @[], x786 @Natural @Double @[], x787 @Natural @Double @[], x788 @Natural @Double @[], x789 @Natural @Double @[], x790 @Natural @Double @[]] = tproject2 h712 in x787 * x784 ; x792 = x781 * x781 ; x793 = x791 * x780 + x791 * x780 ; x794 = negate (recip x792) ; x803 = let [x795 @Natural @Double @[], x796 @Natural @Double @[], x797 @Natural @Double @[], x798 @Natural @Double @[], x799 @Natural @Double @[], x800 @Natural @Double @[]] = tproject2 h712 in x798 * let [x801 @Natural @Double @[], x802 @Natural @Double @[]] = tproject1 h712 in x802 ; x804 = negate (recip (x792 * x792)) * (-1.0 * (x793 * x803)) ; x805 = x794 * x803 ; x806 = x780 * x805 + x780 * x805 ; x815 = x781 * x804 + x781 * x804 + negate (recip (x781 * x781)) * (let [x807 @Natural @Double @[], x808 @Natural @Double @[], x809 @Natural @Double @[], x810 @Natural @Double @[], x811 @Natural @Double @[], x812 @Natural @Double @[]] = tproject2 h712 in x807 * let [x813 @Natural @Double @[], x814 @Natural @Double @[]] = tproject1 h712 in x814) in [recip x781 * let [x816 @Natural @Double @[], x817 @Natural @Double @[]] = tproject1 h712 in x817 + let [x818 @Natural @Double @[], x819 @Natural @Double @[]] = tproject1 h712 in x818, 0, x784 * x806, (x793 * x794) * let [x820 @Natural @Double @[], x821 @Natural @Double @[]] = tproject1 h712 in x821, 0, negate (sin (let [x822 @Natural @Double @[], x823 @Natural @Double @[]] = h777 in x823)) * (x780 * x815 + x780 * x815 + x791 * x805 + x791 * x805) + cos (let [x824 @Natural @Double @[], x825 @Natural @Double @[]] = h777 in x825) * (-1.0 * (let [x826 @Natural @Double @[], x827 @Natural @Double @[], x828 @Natural @Double @[], x829 @Natural @Double @[], x830 @Natural @Double @[], x831 @Natural @Double @[]] = tproject2 h712 in x828 * x806))]) [let [x365 @Natural @Double @[], x366 @Natural @Double @[], x367 @Natural @Double @[]] = tproject1 h316 in x365] [let [x379 @Natural @Double @[], v380 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h832 -> let [x847 @Natural @Double @[]] = tproject1 h832 in let [x848 @Natural @Double @[], x849 @Natural @Double @[], x850 @Natural @Double @[]] = tproject2 h832 in let x851 = cos x850 in [x847 + x848 * recip (x851 * x851), x847]) (\\h852 -> let x881 = cos (let [x877 @Natural @Double @[], x878 @Natural @Double @[], x879 @Natural @Double @[], x880 @Natural @Double @[]] = tproject2 h852 in x880) ; x882 = x881 * x881 ; x891 = let [x883 @Natural @Double @[], x884 @Natural @Double @[], x885 @Natural @Double @[], x886 @Natural @Double @[]] = tproject1 h852 in x886 * negate (sin (let [x887 @Natural @Double @[], x888 @Natural @Double @[], x889 @Natural @Double @[], x890 @Natural @Double @[]] = tproject2 h852 in x890)) in [let [x892 @Natural @Double @[], x893 @Natural @Double @[], x894 @Natural @Double @[], x895 @Natural @Double @[]] = tproject1 h852 in x892 + let [x896 @Natural @Double @[], x897 @Natural @Double @[], x898 @Natural @Double @[], x899 @Natural @Double @[]] = tproject1 h852 in x897 * recip x882 + ((x891 * x881 + x891 * x881) * negate (recip (x882 * x882))) * let [x900 @Natural @Double @[], x901 @Natural @Double @[], x902 @Natural @Double @[], x903 @Natural @Double @[]] = tproject2 h852 in x901, let [x904 @Natural @Double @[], x905 @Natural @Double @[], x906 @Natural @Double @[], x907 @Natural @Double @[]] = tproject1 h852 in x904]) (\\h908 -> let x933 = cos (let [x929 @Natural @Double @[], x930 @Natural @Double @[], x931 @Natural @Double @[], x932 @Natural @Double @[]] = tproject2 h908 in x932) ; x934 = x933 * x933 ; x941 = negate (recip (x934 * x934)) * (let [x935 @Natural @Double @[], x936 @Natural @Double @[], x937 @Natural @Double @[], x938 @Natural @Double @[]] = tproject2 h908 in x936 * let [x939 @Natural @Double @[], x940 @Natural @Double @[]] = tproject1 h908 in x939) in [let [x942 @Natural @Double @[], x943 @Natural @Double @[]] = tproject1 h908 in x942 + let [x944 @Natural @Double @[], x945 @Natural @Double @[]] = tproject1 h908 in x945, recip x934 * let [x946 @Natural @Double @[], x947 @Natural @Double @[]] = tproject1 h908 in x946, 0, negate (sin (let [x948 @Natural @Double @[], x949 @Natural @Double @[], x950 @Natural @Double @[], x951 @Natural @Double @[]] = tproject2 h908 in x951)) * (x933 * x941 + x933 * x941)]) [let [x368 @Natural @Double @[], x369 @Natural @Double @[], x370 @Natural @Double @[]] = tproject1 h316 in x370] [rreplicate 22 (let [x371 @Natural @Double @[], x372 @Natural @Double @[], x373 @Natural @Double @[]] = tproject1 h316 in x372), let [x374 @Natural @Double @[], v375 @Natural @Double @[22], v376 @Natural @Double @[22]] = h358 in v375, rreplicate 22 (let [x377 @Natural @Double @[], x378 @Natural @Double @[]] = h353 in x377)] in v380, rreplicate 22 (let [x381 @Natural @Double @[], x382 @Natural @Double @[], x383 @Natural @Double @[]] = tproject1 h316 in x382), let [x387 @Natural @Double @[], v388 @Natural @Double @[22], v389 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h952 -> let [x966 @Natural @Double @[]] = tproject1 h952 in let [x971 @Natural @Double @[], x972 @Natural @Double @[]] = let [x967 @Natural @Double @[]] = tproject1 h952 in let [x968 @Natural @Double @[], x969 @Natural @Double @[]] = tproject2 h952 in let x970 = cos x969 in [x967, recip (x970 * x970) * x967] in [x971, x966, x972]) (\\h973 -> let [x1006 @Natural @Double @[], x1007 @Natural @Double @[], x1008 @Natural @Double @[]] = tproject1 h973 in let h1015 = [let [x1009 @Natural @Double @[], x1010 @Natural @Double @[], x1011 @Natural @Double @[]] = tproject2 h973 in x1010, let [x1012 @Natural @Double @[], x1013 @Natural @Double @[], x1014 @Natural @Double @[]] = tproject2 h973 in x1014] ; x1018 = cos (let [x1016 @Natural @Double @[], x1017 @Natural @Double @[]] = h1015 in x1017) ; x1019 = x1018 * x1018 ; x1025 = let [x1020 @Natural @Double @[], x1021 @Natural @Double @[], x1022 @Natural @Double @[]] = tproject1 h973 in x1022 * negate (sin (let [x1023 @Natural @Double @[], x1024 @Natural @Double @[]] = h1015 in x1024)) in [let [x1026 @Natural @Double @[], x1027 @Natural @Double @[], x1028 @Natural @Double @[]] = tproject1 h973 in x1026, x1006, ((x1025 * x1018 + x1025 * x1018) * negate (recip (x1019 * x1019))) * let [x1029 @Natural @Double @[], x1030 @Natural @Double @[], x1031 @Natural @Double @[]] = tproject2 h973 in x1029 + let [x1032 @Natural @Double @[], x1033 @Natural @Double @[], x1034 @Natural @Double @[]] = tproject1 h973 in x1032 * recip x1019]) (\\h1035 -> let [x1090 @Natural @Double @[], x1091 @Natural @Double @[], x1092 @Natural @Double @[]] = tproject1 h1035 in let h1099 = [let [x1093 @Natural @Double @[], x1094 @Natural @Double @[], x1095 @Natural @Double @[]] = tproject2 h1035 in x1094, let [x1096 @Natural @Double @[], x1097 @Natural @Double @[], x1098 @Natural @Double @[]] = tproject2 h1035 in x1098] ; x1102 = cos (let [x1100 @Natural @Double @[], x1101 @Natural @Double @[]] = h1099 in x1101) ; x1103 = x1102 * x1102 ; x1107 = negate (recip (x1103 * x1103)) * (let [x1104 @Natural @Double @[], x1105 @Natural @Double @[], x1106 @Natural @Double @[]] = tproject2 h1035 in x1104 * x1092) in [x1091 + recip x1103 * x1092 + x1090, 0.0, negate (sin (let [x1108 @Natural @Double @[], x1109 @Natural @Double @[]] = h1099 in x1109)) * (x1102 * x1107 + x1102 * x1107)]) [let [x384 @Natural @Double @[], x385 @Natural @Double @[], x386 @Natural @Double @[]] = tproject2 h316 in x384] h364 in v388, let [v390 @Natural @Double @[22], v391 @Natural @Double @[22]] = h364 in v390, let [v392 @Natural @Double @[22], v393 @Natural @Double @[22]] = h364 in v393] in [rsum (let [x395 @Natural @Double @[], v396 @Natural @Double @[22]] = h394 in v396), let [x397 @Natural @Double @[], v398 @Natural @Double @[22]] = h394 in x397]) (\\h1110 -> let h1150 = [let [x1144 @Natural @Double @[], x1145 @Natural @Double @[], x1146 @Natural @Double @[]] = tproject2 h1110 in x1145, let [x1147 @Natural @Double @[], x1148 @Natural @Double @[], x1149 @Natural @Double @[]] = tproject2 h1110 in x1149] ; h1155 = dmapAccumLDer (SNat @22) (\\h1216 -> let [x1230 @Natural @Double @[]] = tproject1 h1216 in let [x1235 @Natural @Double @[], x1236 @Natural @Double @[]] = let [x1231 @Natural @Double @[]] = tproject1 h1216 in let [x1234 @Natural @Double @[]] = let [x1232 @Natural @Double @[]] = tproject1 h1216 in let [x1233 @Natural @Double @[]] = tproject2 h1216 in [x1232 + tan x1233] in [x1234, x1231] in [x1235, x1230, x1236]) (\\h1237 -> let [x1262 @Natural @Double @[], x1263 @Natural @Double @[]] = tproject1 h1237 in let [x1273 @Natural @Double @[], x1274 @Natural @Double @[]] = let [x1264 @Natural @Double @[], x1265 @Natural @Double @[]] = tproject1 h1237 in let x1268 = cos (let [x1266 @Natural @Double @[], x1267 @Natural @Double @[]] = tproject2 h1237 in x1267) in [let [x1269 @Natural @Double @[], x1270 @Natural @Double @[]] = tproject1 h1237 in x1269 + let [x1271 @Natural @Double @[], x1272 @Natural @Double @[]] = tproject1 h1237 in x1272 * recip (x1268 * x1268), x1264] in [x1273, x1262, x1274]) (\\h1275 -> let [x1293 @Natural @Double @[], x1294 @Natural @Double @[], x1295 @Natural @Double @[]] = tproject1 h1275 in let x1298 = cos (let [x1296 @Natural @Double @[], x1297 @Natural @Double @[]] = tproject2 h1275 in x1297) in [x1294 + x1293 + x1295, recip (x1298 * x1298) * x1293]) [let [x1151 @Natural @Double @[], x1152 @Natural @Double @[]] = h1150 in x1152] [rreplicate 22 (let [x1153 @Natural @Double @[], x1154 @Natural @Double @[]] = h1150 in x1153)] ; h1161 = [let [x1156 @Natural @Double @[], v1157 @Natural @Double @[22], v1158 @Natural @Double @[22]] = h1155 in v1158, rreplicate 22 (let [x1159 @Natural @Double @[], x1160 @Natural @Double @[]] = h1150 in x1159)] ; h1164 = [let [x1162 @Natural @Double @[], x1163 @Natural @Double @[]] = tproject1 h1110 in x1163, 0] ; h1167 = [0, rreplicate 22 (let [x1165 @Natural @Double @[], x1166 @Natural @Double @[]] = tproject1 h1110 in x1165)] ; h1176 = [let [x1168 @Natural @Double @[], v1169 @Natural @Double @[22]] = h1167 in x1168 + let [x1170 @Natural @Double @[], v1171 @Natural @Double @[22]] = h1164 in x1170, let [x1172 @Natural @Double @[], v1173 @Natural @Double @[22]] = h1167 in v1173 + let [x1174 @Natural @Double @[], v1175 @Natural @Double @[22]] = h1164 in v1175] ; h1191 = dmapAccumLDer (SNat @22) (\\h1299 -> let [x1353 @Natural @Double @[]] = tproject1 h1299 in let [x1354 @Natural @Double @[], x1355 @Natural @Double @[], x1356 @Natural @Double @[], x1357 @Natural @Double @[]] = tproject2 h1299 in let h1358 = [x1356, x1357] ; x1361 = cos (let [x1359 @Natural @Double @[], x1360 @Natural @Double @[]] = h1358 in x1360) ; x1362 = x1361 * x1361 ; x1363 = negate (recip (x1362 * x1362)) * (x1355 * x1354) in [recip x1362 * x1354 + x1353, 0, negate (sin (let [x1364 @Natural @Double @[], x1365 @Natural @Double @[]] = h1358 in x1365)) * (x1361 * x1363 + x1361 * x1363)]) (\\h1366 -> let h1436 = [let [x1426 @Natural @Double @[], x1427 @Natural @Double @[], x1428 @Natural @Double @[], x1429 @Natural @Double @[], x1430 @Natural @Double @[]] = tproject2 h1366 in x1429, let [x1431 @Natural @Double @[], x1432 @Natural @Double @[], x1433 @Natural @Double @[], x1434 @Natural @Double @[], x1435 @Natural @Double @[]] = tproject2 h1366 in x1435] ; x1439 = cos (let [x1437 @Natural @Double @[], x1438 @Natural @Double @[]] = h1436 in x1438) ; x1440 = x1439 * x1439 ; x1441 = x1440 * x1440 ; x1442 = negate (recip x1441) ; x1453 = let [x1443 @Natural @Double @[], x1444 @Natural @Double @[], x1445 @Natural @Double @[], x1446 @Natural @Double @[], x1447 @Natural @Double @[]] = tproject2 h1366 in x1445 * let [x1448 @Natural @Double @[], x1449 @Natural @Double @[], x1450 @Natural @Double @[], x1451 @Natural @Double @[], x1452 @Natural @Double @[]] = tproject2 h1366 in x1449 ; x1454 = x1442 * x1453 ; x1462 = let [x1455 @Natural @Double @[], x1456 @Natural @Double @[], x1457 @Natural @Double @[], x1458 @Natural @Double @[], x1459 @Natural @Double @[]] = tproject1 h1366 in x1459 * negate (sin (let [x1460 @Natural @Double @[], x1461 @Natural @Double @[]] = h1436 in x1461)) ; x1463 = x1462 * x1439 + x1462 * x1439 ; x1484 = (((x1463 * x1440 + x1463 * x1440) * negate (recip (x1441 * x1441))) * -1.0) * x1453 + (let [x1464 @Natural @Double @[], x1465 @Natural @Double @[], x1466 @Natural @Double @[], x1467 @Natural @Double @[], x1468 @Natural @Double @[]] = tproject1 h1366 in x1466 * let [x1469 @Natural @Double @[], x1470 @Natural @Double @[], x1471 @Natural @Double @[], x1472 @Natural @Double @[], x1473 @Natural @Double @[]] = tproject2 h1366 in x1470 + let [x1474 @Natural @Double @[], x1475 @Natural @Double @[], x1476 @Natural @Double @[], x1477 @Natural @Double @[], x1478 @Natural @Double @[]] = tproject1 h1366 in x1475 * let [x1479 @Natural @Double @[], x1480 @Natural @Double @[], x1481 @Natural @Double @[], x1482 @Natural @Double @[], x1483 @Natural @Double @[]] = tproject2 h1366 in x1481) * x1442 in [let [x1485 @Natural @Double @[], x1486 @Natural @Double @[], x1487 @Natural @Double @[], x1488 @Natural @Double @[], x1489 @Natural @Double @[]] = tproject1 h1366 in x1485 + (x1463 * negate (recip (x1440 * x1440))) * let [x1490 @Natural @Double @[], x1491 @Natural @Double @[], x1492 @Natural @Double @[], x1493 @Natural @Double @[], x1494 @Natural @Double @[]] = tproject2 h1366 in x1491 + let [x1495 @Natural @Double @[], x1496 @Natural @Double @[], x1497 @Natural @Double @[], x1498 @Natural @Double @[], x1499 @Natural @Double @[]] = tproject1 h1366 in x1496 * recip x1440, 0.0, ((let [x1500 @Natural @Double @[], x1501 @Natural @Double @[], x1502 @Natural @Double @[], x1503 @Natural @Double @[], x1504 @Natural @Double @[]] = tproject1 h1366 in x1504 * cos (let [x1505 @Natural @Double @[], x1506 @Natural @Double @[]] = h1436 in x1506)) * -1.0) * (x1439 * x1454 + x1439 * x1454) + (x1462 * x1454 + x1484 * x1439 + x1462 * x1454 + x1484 * x1439) * negate (sin (let [x1507 @Natural @Double @[], x1508 @Natural @Double @[]] = h1436 in x1508))]) (\\h1509 -> let h1568 = [let [x1558 @Natural @Double @[], x1559 @Natural @Double @[], x1560 @Natural @Double @[], x1561 @Natural @Double @[], x1562 @Natural @Double @[]] = tproject2 h1509 in x1561, let [x1563 @Natural @Double @[], x1564 @Natural @Double @[], x1565 @Natural @Double @[], x1566 @Natural @Double @[], x1567 @Natural @Double @[]] = tproject2 h1509 in x1567] ; x1571 = cos (let [x1569 @Natural @Double @[], x1570 @Natural @Double @[]] = h1568 in x1570) ; x1572 = x1571 * x1571 ; x1573 = x1572 * x1572 ; x1574 = negate (recip x1573) ; x1585 = let [x1575 @Natural @Double @[], x1576 @Natural @Double @[], x1577 @Natural @Double @[], x1578 @Natural @Double @[], x1579 @Natural @Double @[]] = tproject2 h1509 in x1577 * let [x1580 @Natural @Double @[], x1581 @Natural @Double @[], x1582 @Natural @Double @[], x1583 @Natural @Double @[], x1584 @Natural @Double @[]] = tproject2 h1509 in x1581 ; x1586 = x1574 * x1585 ; x1592 = negate (sin (let [x1587 @Natural @Double @[], x1588 @Natural @Double @[]] = h1568 in x1588)) * let [x1589 @Natural @Double @[], x1590 @Natural @Double @[], x1591 @Natural @Double @[]] = tproject1 h1509 in x1591 ; x1593 = x1571 * x1592 + x1571 * x1592 ; x1594 = x1574 * x1593 ; x1595 = negate (recip (x1573 * x1573)) * (-1.0 * (x1585 * x1593)) ; x1604 = x1572 * x1595 + x1572 * x1595 + negate (recip (x1572 * x1572)) * (let [x1596 @Natural @Double @[], x1597 @Natural @Double @[], x1598 @Natural @Double @[], x1599 @Natural @Double @[], x1600 @Natural @Double @[]] = tproject2 h1509 in x1597 * let [x1601 @Natural @Double @[], x1602 @Natural @Double @[], x1603 @Natural @Double @[]] = tproject1 h1509 in x1601) in [let [x1605 @Natural @Double @[], x1606 @Natural @Double @[], x1607 @Natural @Double @[]] = tproject1 h1509 in x1605, let [x1608 @Natural @Double @[], x1609 @Natural @Double @[], x1610 @Natural @Double @[], x1611 @Natural @Double @[], x1612 @Natural @Double @[]] = tproject2 h1509 in x1610 * x1594 + recip x1572 * let [x1613 @Natural @Double @[], x1614 @Natural @Double @[], x1615 @Natural @Double @[]] = tproject1 h1509 in x1613, let [x1616 @Natural @Double @[], x1617 @Natural @Double @[], x1618 @Natural @Double @[], x1619 @Natural @Double @[], x1620 @Natural @Double @[]] = tproject2 h1509 in x1617 * x1594, 0, negate (sin (let [x1621 @Natural @Double @[], x1622 @Natural @Double @[]] = h1568 in x1622)) * (x1571 * x1604 + x1571 * x1604 + x1586 * x1592 + x1586 * x1592) + cos (let [x1623 @Natural @Double @[], x1624 @Natural @Double @[]] = h1568 in x1624) * (-1.0 * ((x1571 * x1586 + x1571 * x1586) * let [x1625 @Natural @Double @[], x1626 @Natural @Double @[], x1627 @Natural @Double @[]] = tproject1 h1509 in x1627))]) [let [x1177 @Natural @Double @[], v1178 @Natural @Double @[22]] = h1176 in x1177] [let [x1179 @Natural @Double @[], v1180 @Natural @Double @[22]] = h1176 in v1180, let [x1184 @Natural @Double @[], v1185 @Natural @Double @[22], v1186 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h1628 -> let [x1642 @Natural @Double @[]] = tproject1 h1628 in let [x1647 @Natural @Double @[], x1648 @Natural @Double @[]] = let [x1643 @Natural @Double @[]] = tproject1 h1628 in let [x1644 @Natural @Double @[], x1645 @Natural @Double @[]] = tproject2 h1628 in let x1646 = cos x1645 in [x1643, recip (x1646 * x1646) * x1643] in [x1647, x1642, x1648]) (\\h1649 -> let [x1709 @Natural @Double @[], x1710 @Natural @Double @[], x1711 @Natural @Double @[]] = tproject1 h1649 in let h1718 = [let [x1712 @Natural @Double @[], x1713 @Natural @Double @[], x1714 @Natural @Double @[]] = tproject2 h1649 in x1713, let [x1715 @Natural @Double @[], x1716 @Natural @Double @[], x1717 @Natural @Double @[]] = tproject2 h1649 in x1717] ; x1721 = cos (let [x1719 @Natural @Double @[], x1720 @Natural @Double @[]] = h1718 in x1720) ; x1722 = x1721 * x1721 ; x1728 = let [x1723 @Natural @Double @[], x1724 @Natural @Double @[], x1725 @Natural @Double @[]] = tproject1 h1649 in x1725 * negate (sin (let [x1726 @Natural @Double @[], x1727 @Natural @Double @[]] = h1718 in x1727)) in [let [x1729 @Natural @Double @[], x1730 @Natural @Double @[], x1731 @Natural @Double @[]] = tproject1 h1649 in x1729, x1709, ((x1728 * x1721 + x1728 * x1721) * negate (recip (x1722 * x1722))) * let [x1732 @Natural @Double @[], x1733 @Natural @Double @[], x1734 @Natural @Double @[]] = tproject2 h1649 in x1732 + let [x1735 @Natural @Double @[], x1736 @Natural @Double @[], x1737 @Natural @Double @[]] = tproject1 h1649 in x1735 * recip x1722]) (\\h1738 -> let [x1769 @Natural @Double @[], x1770 @Natural @Double @[], x1771 @Natural @Double @[]] = tproject1 h1738 in let h1778 = [let [x1772 @Natural @Double @[], x1773 @Natural @Double @[], x1774 @Natural @Double @[]] = tproject2 h1738 in x1773, let [x1775 @Natural @Double @[], x1776 @Natural @Double @[], x1777 @Natural @Double @[]] = tproject2 h1738 in x1777] ; x1781 = cos (let [x1779 @Natural @Double @[], x1780 @Natural @Double @[]] = h1778 in x1780) ; x1782 = x1781 * x1781 ; x1786 = negate (recip (x1782 * x1782)) * (let [x1783 @Natural @Double @[], x1784 @Natural @Double @[], x1785 @Natural @Double @[]] = tproject2 h1738 in x1783 * x1771) in [x1770 + recip x1782 * x1771 + x1769, 0.0, negate (sin (let [x1787 @Natural @Double @[], x1788 @Natural @Double @[]] = h1778 in x1788)) * (x1781 * x1786 + x1781 * x1786)]) [let [x1181 @Natural @Double @[], x1182 @Natural @Double @[], x1183 @Natural @Double @[]] = tproject2 h1110 in x1181] h1161 in v1185, let [v1187 @Natural @Double @[22], v1188 @Natural @Double @[22]] = h1161 in v1187, let [v1189 @Natural @Double @[22], v1190 @Natural @Double @[22]] = h1161 in v1190] ; h1195 = [0, let [x1192 @Natural @Double @[], v1193 @Natural @Double @[22], v1194 @Natural @Double @[22]] = h1191 in v1193] ; h1205 = dmapAccumRDer (SNat @22) (\\h1789 -> let [x1800 @Natural @Double @[]] = tproject1 h1789 in let [x1801 @Natural @Double @[], x1802 @Natural @Double @[], x1803 @Natural @Double @[]] = tproject2 h1789 in let x1804 = cos x1803 in [x1800 + x1801, recip (x1804 * x1804) * x1800]) (\\h1805 -> let x1830 = cos (let [x1826 @Natural @Double @[], x1827 @Natural @Double @[], x1828 @Natural @Double @[], x1829 @Natural @Double @[]] = tproject2 h1805 in x1829) ; x1831 = x1830 * x1830 ; x1840 = let [x1832 @Natural @Double @[], x1833 @Natural @Double @[], x1834 @Natural @Double @[], x1835 @Natural @Double @[]] = tproject1 h1805 in x1835 * negate (sin (let [x1836 @Natural @Double @[], x1837 @Natural @Double @[], x1838 @Natural @Double @[], x1839 @Natural @Double @[]] = tproject2 h1805 in x1839)) in [let [x1841 @Natural @Double @[], x1842 @Natural @Double @[], x1843 @Natural @Double @[], x1844 @Natural @Double @[]] = tproject1 h1805 in x1841 + let [x1845 @Natural @Double @[], x1846 @Natural @Double @[], x1847 @Natural @Double @[], x1848 @Natural @Double @[]] = tproject1 h1805 in x1846, ((x1840 * x1830 + x1840 * x1830) * negate (recip (x1831 * x1831))) * let [x1849 @Natural @Double @[], x1850 @Natural @Double @[], x1851 @Natural @Double @[], x1852 @Natural @Double @[]] = tproject2 h1805 in x1849 + let [x1853 @Natural @Double @[], x1854 @Natural @Double @[], x1855 @Natural @Double @[], x1856 @Natural @Double @[]] = tproject1 h1805 in x1853 * recip x1831]) (\\h1857 -> let x1878 = cos (let [x1874 @Natural @Double @[], x1875 @Natural @Double @[], x1876 @Natural @Double @[], x1877 @Natural @Double @[]] = tproject2 h1857 in x1877) ; x1879 = x1878 * x1878 ; x1886 = negate (recip (x1879 * x1879)) * (let [x1880 @Natural @Double @[], x1881 @Natural @Double @[], x1882 @Natural @Double @[], x1883 @Natural @Double @[]] = tproject2 h1857 in x1880 * let [x1884 @Natural @Double @[], x1885 @Natural @Double @[]] = tproject1 h1857 in x1885) in [let [x1887 @Natural @Double @[], x1888 @Natural @Double @[]] = tproject1 h1857 in x1887 + recip x1879 * let [x1889 @Natural @Double @[], x1890 @Natural @Double @[]] = tproject1 h1857 in x1890, let [x1891 @Natural @Double @[], x1892 @Natural @Double @[]] = tproject1 h1857 in x1891, 0, negate (sin (let [x1893 @Natural @Double @[], x1894 @Natural @Double @[], x1895 @Natural @Double @[], x1896 @Natural @Double @[]] = tproject2 h1857 in x1896)) * (x1878 * x1886 + x1878 * x1886)]) [let [x1196 @Natural @Double @[], v1197 @Natural @Double @[22]] = h1195 in x1196] [let [x1198 @Natural @Double @[], v1199 @Natural @Double @[22]] = h1195 in v1199, let [x1200 @Natural @Double @[], v1201 @Natural @Double @[22], v1202 @Natural @Double @[22]] = h1155 in v1201, rreplicate 22 (let [x1203 @Natural @Double @[], x1204 @Natural @Double @[]] = h1150 in x1203)] in [let [x1206 @Natural @Double @[], v1207 @Natural @Double @[22], v1208 @Natural @Double @[22]] = h1191 in x1206, rsum (let [x1209 @Natural @Double @[], v1210 @Natural @Double @[22]] = h1205 in v1210) + rsum (let [x1211 @Natural @Double @[], v1212 @Natural @Double @[22], v1213 @Natural @Double @[22]] = h1191 in v1213), let [x1214 @Natural @Double @[], v1215 @Natural @Double @[22]] = h1205 in x1214]) [1.0] [let [x9 @Natural @Double @[], v10 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) (\\h1897 -> let [x1910 @Natural @Double @[]] = tproject1 h1897 in let [x1915 @Natural @Double @[]] = let [x1911 @Natural @Double @[]] = tproject1 h1897 in let [x1912 @Natural @Double @[]] = tproject2 h1897 in [let [x1913 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h1916 -> let [x1925 @Natural @Double @[]] = tproject1 h1916 in let [x1926 @Natural @Double @[]] = tproject2 h1916 in [x1925 + tan x1926]) (\\h1928 -> let x1949 = cos (let [x1947 @Natural @Double @[], x1948 @Natural @Double @[]] = tproject2 h1928 in x1948) in [let [x1950 @Natural @Double @[], x1951 @Natural @Double @[]] = tproject1 h1928 in x1950 + let [x1952 @Natural @Double @[], x1953 @Natural @Double @[]] = tproject1 h1928 in x1953 * recip (x1949 * x1949)]) (\\h1954 -> let x1971 = cos (let [x1969 @Natural @Double @[], x1970 @Natural @Double @[]] = tproject2 h1954 in x1970) in [let [x1972 @Natural @Double @[]] = tproject1 h1954 in x1972, recip (x1971 * x1971) * let [x1973 @Natural @Double @[]] = tproject1 h1954 in x1973]) [x1912] [rreplicate 22 x1911] in x1913] in [x1915, x1910]) (\\h1974 -> let [x2002 @Natural @Double @[], x2003 @Natural @Double @[]] = tproject1 h1974 in [let [x2016 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h2018 -> let [x2054 @Natural @Double @[]] = tproject1 h2018 in let [x2055 @Natural @Double @[], x2056 @Natural @Double @[], x2057 @Natural @Double @[]] = tproject2 h2018 in let h2058 = [x2054, x2055] ; x2059 = cos x2057 in [let [x2060 @Natural @Double @[], x2061 @Natural @Double @[]] = h2058 in x2060 + let [x2062 @Natural @Double @[], x2063 @Natural @Double @[]] = h2058 in x2063 * recip (x2059 * x2059)]) (\\h2064 -> let h2134 = [let [x2126 @Natural @Double @[], x2127 @Natural @Double @[], x2128 @Natural @Double @[], x2129 @Natural @Double @[]] = tproject2 h2064 in x2128, let [x2130 @Natural @Double @[], x2131 @Natural @Double @[], x2132 @Natural @Double @[], x2133 @Natural @Double @[]] = tproject2 h2064 in x2133] ; x2137 = cos (let [x2135 @Natural @Double @[], x2136 @Natural @Double @[]] = h2134 in x2136) ; x2138 = x2137 * x2137 ; x2145 = let [x2139 @Natural @Double @[], x2140 @Natural @Double @[], x2141 @Natural @Double @[], x2142 @Natural @Double @[]] = tproject1 h2064 in x2142 * negate (sin (let [x2143 @Natural @Double @[], x2144 @Natural @Double @[]] = h2134 in x2144)) in [let [x2146 @Natural @Double @[], x2147 @Natural @Double @[], x2148 @Natural @Double @[], x2149 @Natural @Double @[]] = tproject1 h2064 in x2146 + let [x2150 @Natural @Double @[], x2151 @Natural @Double @[], x2152 @Natural @Double @[], x2153 @Natural @Double @[]] = tproject1 h2064 in x2151 * recip x2138 + ((x2145 * x2137 + x2145 * x2137) * negate (recip (x2138 * x2138))) * let [x2154 @Natural @Double @[], x2155 @Natural @Double @[], x2156 @Natural @Double @[], x2157 @Natural @Double @[]] = tproject2 h2064 in x2155]) (\\h2158 -> let h2215 = [let [x2207 @Natural @Double @[], x2208 @Natural @Double @[], x2209 @Natural @Double @[], x2210 @Natural @Double @[]] = tproject2 h2158 in x2209, let [x2211 @Natural @Double @[], x2212 @Natural @Double @[], x2213 @Natural @Double @[], x2214 @Natural @Double @[]] = tproject2 h2158 in x2214] ; x2218 = cos (let [x2216 @Natural @Double @[], x2217 @Natural @Double @[]] = h2215 in x2217) ; x2219 = x2218 * x2218 ; x2225 = negate (recip (x2219 * x2219)) * (let [x2220 @Natural @Double @[], x2221 @Natural @Double @[], x2222 @Natural @Double @[], x2223 @Natural @Double @[]] = tproject2 h2158 in x2221 * let [x2224 @Natural @Double @[]] = tproject1 h2158 in x2224) in [let [x2226 @Natural @Double @[]] = tproject1 h2158 in x2226, recip x2219 * let [x2227 @Natural @Double @[]] = tproject1 h2158 in x2227, 0, negate (sin (let [x2228 @Natural @Double @[], x2229 @Natural @Double @[]] = h2215 in x2229)) * (x2218 * x2225 + x2218 * x2225)]) [let [x2004 @Natural @Double @[], x2005 @Natural @Double @[]] = tproject1 h1974 in x2005] [rreplicate 22 (let [x2006 @Natural @Double @[], x2007 @Natural @Double @[]] = tproject1 h1974 in x2006), let [x2012 @Natural @Double @[], v2013 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h2230 -> let [x2246 @Natural @Double @[]] = tproject1 h2230 in let [x2249 @Natural @Double @[]] = let [x2247 @Natural @Double @[]] = tproject1 h2230 in let [x2248 @Natural @Double @[]] = tproject2 h2230 in [x2247 + tan x2248] in [x2249, x2246]) (\\h2250 -> let [x2272 @Natural @Double @[], x2273 @Natural @Double @[]] = tproject1 h2250 in let x2276 = cos (let [x2274 @Natural @Double @[], x2275 @Natural @Double @[]] = tproject2 h2250 in x2275) in [let [x2277 @Natural @Double @[], x2278 @Natural @Double @[]] = tproject1 h2250 in x2277 + let [x2279 @Natural @Double @[], x2280 @Natural @Double @[]] = tproject1 h2250 in x2280 * recip (x2276 * x2276), x2272]) (\\h2281 -> let [x2306 @Natural @Double @[], x2307 @Natural @Double @[]] = tproject1 h2281 in let x2310 = cos (let [x2308 @Natural @Double @[], x2309 @Natural @Double @[]] = tproject2 h2281 in x2309) in [x2306 + x2307, recip (x2310 * x2310) * x2306]) [let [x2008 @Natural @Double @[], x2009 @Natural @Double @[]] = tproject2 h1974 in x2009] [rreplicate 22 (let [x2010 @Natural @Double @[], x2011 @Natural @Double @[]] = tproject2 h1974 in x2010)] in v2013, rreplicate 22 (let [x2014 @Natural @Double @[], x2015 @Natural @Double @[]] = tproject2 h1974 in x2014)] in x2016, x2002]) (\\h2311 -> let [x2331 @Natural @Double @[], x2332 @Natural @Double @[]] = tproject1 h2311 in let h2341 = dmapAccumRDer (SNat @22) (\\h2348 -> let [x2354 @Natural @Double @[]] = tproject1 h2348 in let [x2355 @Natural @Double @[], x2356 @Natural @Double @[]] = tproject2 h2348 in let x2357 = cos x2356 in [x2354, recip (x2357 * x2357) * x2354]) (\\h2358 -> let h2392 = [let [x2386 @Natural @Double @[], x2387 @Natural @Double @[], x2388 @Natural @Double @[]] = tproject2 h2358 in x2387, let [x2389 @Natural @Double @[], x2390 @Natural @Double @[], x2391 @Natural @Double @[]] = tproject2 h2358 in x2391] ; x2395 = cos (let [x2393 @Natural @Double @[], x2394 @Natural @Double @[]] = h2392 in x2394) ; x2396 = x2395 * x2395 ; x2402 = let [x2397 @Natural @Double @[], x2398 @Natural @Double @[], x2399 @Natural @Double @[]] = tproject1 h2358 in x2399 * negate (sin (let [x2400 @Natural @Double @[], x2401 @Natural @Double @[]] = h2392 in x2401)) in [let [x2403 @Natural @Double @[], x2404 @Natural @Double @[], x2405 @Natural @Double @[]] = tproject1 h2358 in x2403, ((x2402 * x2395 + x2402 * x2395) * negate (recip (x2396 * x2396))) * let [x2406 @Natural @Double @[], x2407 @Natural @Double @[], x2408 @Natural @Double @[]] = tproject2 h2358 in x2406 + let [x2409 @Natural @Double @[], x2410 @Natural @Double @[], x2411 @Natural @Double @[]] = tproject1 h2358 in x2409 * recip x2396]) (\\h2412 -> let h2443 = [let [x2437 @Natural @Double @[], x2438 @Natural @Double @[], x2439 @Natural @Double @[]] = tproject2 h2412 in x2438, let [x2440 @Natural @Double @[], x2441 @Natural @Double @[], x2442 @Natural @Double @[]] = tproject2 h2412 in x2442] ; x2446 = cos (let [x2444 @Natural @Double @[], x2445 @Natural @Double @[]] = h2443 in x2445) ; x2447 = x2446 * x2446 ; x2453 = negate (recip (x2447 * x2447)) * (let [x2448 @Natural @Double @[], x2449 @Natural @Double @[], x2450 @Natural @Double @[]] = tproject2 h2412 in x2448 * let [x2451 @Natural @Double @[], x2452 @Natural @Double @[]] = tproject1 h2412 in x2452) in [recip x2447 * let [x2454 @Natural @Double @[], x2455 @Natural @Double @[]] = tproject1 h2412 in x2455 + let [x2456 @Natural @Double @[], x2457 @Natural @Double @[]] = tproject1 h2412 in x2456, 0, negate (sin (let [x2458 @Natural @Double @[], x2459 @Natural @Double @[]] = h2443 in x2459)) * (x2446 * x2453 + x2446 * x2453)]) [x2331] [let [x2337 @Natural @Double @[], v2338 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h2460 -> let [x2466 @Natural @Double @[]] = tproject1 h2460 in let [x2469 @Natural @Double @[]] = let [x2467 @Natural @Double @[]] = tproject1 h2460 in let [x2468 @Natural @Double @[]] = tproject2 h2460 in [x2467 + tan x2468] in [x2469, x2466]) (\\h2470 -> let [x2481 @Natural @Double @[], x2482 @Natural @Double @[]] = tproject1 h2470 in let x2485 = cos (let [x2483 @Natural @Double @[], x2484 @Natural @Double @[]] = tproject2 h2470 in x2484) in [let [x2486 @Natural @Double @[], x2487 @Natural @Double @[]] = tproject1 h2470 in x2486 + let [x2488 @Natural @Double @[], x2489 @Natural @Double @[]] = tproject1 h2470 in x2489 * recip (x2485 * x2485), x2481]) (\\h2490 -> let [x2497 @Natural @Double @[], x2498 @Natural @Double @[]] = tproject1 h2490 in let x2501 = cos (let [x2499 @Natural @Double @[], x2500 @Natural @Double @[]] = tproject2 h2490 in x2500) in [x2497 + x2498, recip (x2501 * x2501) * x2497]) [let [x2333 @Natural @Double @[], x2334 @Natural @Double @[]] = tproject2 h2311 in x2334] [rreplicate 22 (let [x2335 @Natural @Double @[], x2336 @Natural @Double @[]] = tproject2 h2311 in x2335)] in v2338, rreplicate 22 (let [x2339 @Natural @Double @[], x2340 @Natural @Double @[]] = tproject2 h2311 in x2339)] in [rsum (let [x2342 @Natural @Double @[], v2343 @Natural @Double @[22]] = h2341 in v2343) + x2332, let [x2345 @Natural @Double @[], v2346 @Natural @Double @[22]] = h2341 in x2345]) [1.1] [rreplicate 11 1.1] in v10, rreplicate 11 1.1] in [rsum (let [x13 @Natural @Double @[], v14 @Natural @Double @[11]] = h12 in v14) + let [x15 @Natural @Double @[], v16 @Natural @Double @[11]] = h12 in x15]"

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
      (simplifyInline
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4_470

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
      (simplifyInline
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 54_458

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
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 739_006

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
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11_819_607

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
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
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
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
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
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h11 = dmapAccumRDer (SNat @2) (\\h16 -> let [x43 @Natural @Double @[]] = tproject1 h16 in let [x44 @Natural @Double @[], x45 @Natural @Double @[]] = tproject2 h16 in let h46 = [x44, x45] ; h55 = dmapAccumRDer (SNat @2) (\\h60 -> let [x82 @Natural @Double @[]] = tproject1 h60 in let [x83 @Natural @Double @[], x84 @Natural @Double @[]] = tproject2 h60 in let x85 = cos x84 in [x82, recip (x85 * x85) * x82]) (\\h86 -> let h141 = [let [x135 @Natural @Double @[], x136 @Natural @Double @[], x137 @Natural @Double @[]] = tproject2 h86 in x136, let [x138 @Natural @Double @[], x139 @Natural @Double @[], x140 @Natural @Double @[]] = tproject2 h86 in x140] ; x144 = cos (let [x142 @Natural @Double @[], x143 @Natural @Double @[]] = h141 in x143) ; x145 = x144 * x144 ; x151 = let [x146 @Natural @Double @[], x147 @Natural @Double @[], x148 @Natural @Double @[]] = tproject1 h86 in x148 * negate (sin (let [x149 @Natural @Double @[], x150 @Natural @Double @[]] = h141 in x150)) in [let [x152 @Natural @Double @[], x153 @Natural @Double @[], x154 @Natural @Double @[]] = tproject1 h86 in x152, ((x151 * x144 + x151 * x144) * negate (recip (x145 * x145))) * let [x155 @Natural @Double @[], x156 @Natural @Double @[], x157 @Natural @Double @[]] = tproject2 h86 in x155 + let [x158 @Natural @Double @[], x159 @Natural @Double @[], x160 @Natural @Double @[]] = tproject1 h86 in x158 * recip x145]) (\\h161 -> let h210 = [let [x204 @Natural @Double @[], x205 @Natural @Double @[], x206 @Natural @Double @[]] = tproject2 h161 in x205, let [x207 @Natural @Double @[], x208 @Natural @Double @[], x209 @Natural @Double @[]] = tproject2 h161 in x209] ; x213 = cos (let [x211 @Natural @Double @[], x212 @Natural @Double @[]] = h210 in x212) ; x214 = x213 * x213 ; x220 = negate (recip (x214 * x214)) * (let [x215 @Natural @Double @[], x216 @Natural @Double @[], x217 @Natural @Double @[]] = tproject2 h161 in x215 * let [x218 @Natural @Double @[], x219 @Natural @Double @[]] = tproject1 h161 in x219) in [recip x214 * let [x221 @Natural @Double @[], x222 @Natural @Double @[]] = tproject1 h161 in x222 + let [x223 @Natural @Double @[], x224 @Natural @Double @[]] = tproject1 h161 in x223, 0, negate (sin (let [x225 @Natural @Double @[], x226 @Natural @Double @[]] = h210 in x226)) * (x213 * x220 + x213 * x220)]) [x43] [let [x51 @Natural @Double @[], v52 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h227 -> let [x241 @Natural @Double @[]] = tproject1 h227 in let [x244 @Natural @Double @[]] = let [x242 @Natural @Double @[]] = tproject1 h227 in let [x243 @Natural @Double @[]] = tproject2 h227 in [x242 + tan x243] in [x244, x241]) (\\h245 -> let [x275 @Natural @Double @[], x276 @Natural @Double @[]] = tproject1 h245 in let x279 = cos (let [x277 @Natural @Double @[], x278 @Natural @Double @[]] = tproject2 h245 in x278) in [let [x280 @Natural @Double @[], x281 @Natural @Double @[]] = tproject1 h245 in x280 + let [x282 @Natural @Double @[], x283 @Natural @Double @[]] = tproject1 h245 in x283 * recip (x279 * x279), x275]) (\\h284 -> let [x301 @Natural @Double @[], x302 @Natural @Double @[]] = tproject1 h284 in let x305 = cos (let [x303 @Natural @Double @[], x304 @Natural @Double @[]] = tproject2 h284 in x304) in [x301 + x302, recip (x305 * x305) * x301]) [let [x47 @Natural @Double @[], x48 @Natural @Double @[]] = h46 in x48] [rreplicate 2 (let [x49 @Natural @Double @[], x50 @Natural @Double @[]] = h46 in x49)] in v52, rreplicate 2 (let [x53 @Natural @Double @[], x54 @Natural @Double @[]] = h46 in x53)] in [rsum (let [x56 @Natural @Double @[], v57 @Natural @Double @[2]] = h55 in v57), let [x58 @Natural @Double @[], v59 @Natural @Double @[2]] = h55 in x58]) (\\h306 -> let h343 = [let [x337 @Natural @Double @[], x338 @Natural @Double @[], x339 @Natural @Double @[]] = tproject2 h306 in x338, let [x340 @Natural @Double @[], x341 @Natural @Double @[], x342 @Natural @Double @[]] = tproject2 h306 in x342] ; h348 = dmapAccumLDer (SNat @2) (\\h389 -> let [x403 @Natural @Double @[]] = tproject1 h389 in let [x408 @Natural @Double @[], x409 @Natural @Double @[]] = let [x404 @Natural @Double @[]] = tproject1 h389 in let [x407 @Natural @Double @[]] = let [x405 @Natural @Double @[]] = tproject1 h389 in let [x406 @Natural @Double @[]] = tproject2 h389 in [x405 + tan x406] in [x407, x404] in [x408, x403, x409]) (\\h410 -> let [x435 @Natural @Double @[], x436 @Natural @Double @[]] = tproject1 h410 in let [x446 @Natural @Double @[], x447 @Natural @Double @[]] = let [x437 @Natural @Double @[], x438 @Natural @Double @[]] = tproject1 h410 in let x441 = cos (let [x439 @Natural @Double @[], x440 @Natural @Double @[]] = tproject2 h410 in x440) in [let [x442 @Natural @Double @[], x443 @Natural @Double @[]] = tproject1 h410 in x442 + let [x444 @Natural @Double @[], x445 @Natural @Double @[]] = tproject1 h410 in x445 * recip (x441 * x441), x437] in [x446, x435, x447]) (\\h448 -> let [x466 @Natural @Double @[], x467 @Natural @Double @[], x468 @Natural @Double @[]] = tproject1 h448 in let x471 = cos (let [x469 @Natural @Double @[], x470 @Natural @Double @[]] = tproject2 h448 in x470) in [x467 + x466 + x468, recip (x471 * x471) * x466]) [let [x344 @Natural @Double @[], x345 @Natural @Double @[]] = h343 in x345] [rreplicate 2 (let [x346 @Natural @Double @[], x347 @Natural @Double @[]] = h343 in x346)] ; h354 = [let [x349 @Natural @Double @[], v350 @Natural @Double @[2], v351 @Natural @Double @[2]] = h348 in v351, rreplicate 2 (let [x352 @Natural @Double @[], x353 @Natural @Double @[]] = h343 in x352)] ; h384 = dmapAccumRDer (SNat @2) (\\h472 -> let [x533 @Natural @Double @[]] = tproject1 h472 in let [x534 @Natural @Double @[], x535 @Natural @Double @[], x536 @Natural @Double @[], x537 @Natural @Double @[], x538 @Natural @Double @[]] = tproject2 h472 in let h539 = [x537, x538] ; x542 = cos (let [x540 @Natural @Double @[], x541 @Natural @Double @[]] = h539 in x541) ; x543 = x542 * x542 ; x546 = x535 * negate (sin (let [x544 @Natural @Double @[], x545 @Natural @Double @[]] = h539 in x545)) in [x533, ((x546 * x542 + x546 * x542) * negate (recip (x543 * x543))) * x536 + x533 * recip x543]) (\\h547 -> let h623 = [let [x611 @Natural @Double @[], x612 @Natural @Double @[], x613 @Natural @Double @[], x614 @Natural @Double @[], x615 @Natural @Double @[], x616 @Natural @Double @[]] = tproject2 h547 in x615, let [x617 @Natural @Double @[], x618 @Natural @Double @[], x619 @Natural @Double @[], x620 @Natural @Double @[], x621 @Natural @Double @[], x622 @Natural @Double @[]] = tproject2 h547 in x622] ; x626 = cos (let [x624 @Natural @Double @[], x625 @Natural @Double @[]] = h623 in x625) ; x627 = x626 * x626 ; x630 = negate (sin (let [x628 @Natural @Double @[], x629 @Natural @Double @[]] = h623 in x629)) ; x637 = let [x631 @Natural @Double @[], x632 @Natural @Double @[], x633 @Natural @Double @[], x634 @Natural @Double @[], x635 @Natural @Double @[], x636 @Natural @Double @[]] = tproject2 h547 in x633 * x630 ; x638 = x627 * x627 ; x639 = x637 * x626 + x637 * x626 ; x640 = negate (recip x638) ; x661 = let [x641 @Natural @Double @[], x642 @Natural @Double @[], x643 @Natural @Double @[], x644 @Natural @Double @[], x645 @Natural @Double @[], x646 @Natural @Double @[]] = tproject1 h547 in x643 * x630 + ((let [x647 @Natural @Double @[], x648 @Natural @Double @[], x649 @Natural @Double @[], x650 @Natural @Double @[], x651 @Natural @Double @[], x652 @Natural @Double @[]] = tproject1 h547 in x652 * cos (let [x653 @Natural @Double @[], x654 @Natural @Double @[]] = h623 in x654)) * -1.0) * let [x655 @Natural @Double @[], x656 @Natural @Double @[], x657 @Natural @Double @[], x658 @Natural @Double @[], x659 @Natural @Double @[], x660 @Natural @Double @[]] = tproject2 h547 in x657 ; x670 = let [x662 @Natural @Double @[], x663 @Natural @Double @[], x664 @Natural @Double @[], x665 @Natural @Double @[], x666 @Natural @Double @[], x667 @Natural @Double @[]] = tproject1 h547 in x667 * negate (sin (let [x668 @Natural @Double @[], x669 @Natural @Double @[]] = h623 in x669)) ; x671 = x670 * x626 + x670 * x626 in [let [x672 @Natural @Double @[], x673 @Natural @Double @[], x674 @Natural @Double @[], x675 @Natural @Double @[], x676 @Natural @Double @[], x677 @Natural @Double @[]] = tproject1 h547 in x672, ((x661 * x626 + x670 * x637 + x661 * x626 + x670 * x637) * x640 + (((x671 * x627 + x671 * x627) * negate (recip (x638 * x638))) * -1.0) * x639) * let [x678 @Natural @Double @[], x679 @Natural @Double @[], x680 @Natural @Double @[], x681 @Natural @Double @[], x682 @Natural @Double @[], x683 @Natural @Double @[]] = tproject2 h547 in x681 + let [x684 @Natural @Double @[], x685 @Natural @Double @[], x686 @Natural @Double @[], x687 @Natural @Double @[], x688 @Natural @Double @[], x689 @Natural @Double @[]] = tproject1 h547 in x687 * (x639 * x640) + let [x690 @Natural @Double @[], x691 @Natural @Double @[], x692 @Natural @Double @[], x693 @Natural @Double @[], x694 @Natural @Double @[], x695 @Natural @Double @[]] = tproject1 h547 in x690 * recip x627 + (x671 * negate (recip (x627 * x627))) * let [x696 @Natural @Double @[], x697 @Natural @Double @[], x698 @Natural @Double @[], x699 @Natural @Double @[], x700 @Natural @Double @[], x701 @Natural @Double @[]] = tproject2 h547 in x696]) (\\h702 -> let h767 = [let [x755 @Natural @Double @[], x756 @Natural @Double @[], x757 @Natural @Double @[], x758 @Natural @Double @[], x759 @Natural @Double @[], x760 @Natural @Double @[]] = tproject2 h702 in x759, let [x761 @Natural @Double @[], x762 @Natural @Double @[], x763 @Natural @Double @[], x764 @Natural @Double @[], x765 @Natural @Double @[], x766 @Natural @Double @[]] = tproject2 h702 in x766] ; x770 = cos (let [x768 @Natural @Double @[], x769 @Natural @Double @[]] = h767 in x769) ; x771 = x770 * x770 ; x774 = negate (sin (let [x772 @Natural @Double @[], x773 @Natural @Double @[]] = h767 in x773)) ; x781 = let [x775 @Natural @Double @[], x776 @Natural @Double @[], x777 @Natural @Double @[], x778 @Natural @Double @[], x779 @Natural @Double @[], x780 @Natural @Double @[]] = tproject2 h702 in x777 * x774 ; x782 = x771 * x771 ; x783 = x781 * x770 + x781 * x770 ; x784 = negate (recip x782) ; x793 = let [x785 @Natural @Double @[], x786 @Natural @Double @[], x787 @Natural @Double @[], x788 @Natural @Double @[], x789 @Natural @Double @[], x790 @Natural @Double @[]] = tproject2 h702 in x788 * let [x791 @Natural @Double @[], x792 @Natural @Double @[]] = tproject1 h702 in x792 ; x794 = negate (recip (x782 * x782)) * (-1.0 * (x783 * x793)) ; x795 = x784 * x793 ; x796 = x770 * x795 + x770 * x795 ; x805 = x771 * x794 + x771 * x794 + negate (recip (x771 * x771)) * (let [x797 @Natural @Double @[], x798 @Natural @Double @[], x799 @Natural @Double @[], x800 @Natural @Double @[], x801 @Natural @Double @[], x802 @Natural @Double @[]] = tproject2 h702 in x797 * let [x803 @Natural @Double @[], x804 @Natural @Double @[]] = tproject1 h702 in x804) in [recip x771 * let [x806 @Natural @Double @[], x807 @Natural @Double @[]] = tproject1 h702 in x807 + let [x808 @Natural @Double @[], x809 @Natural @Double @[]] = tproject1 h702 in x808, 0, x774 * x796, (x783 * x784) * let [x810 @Natural @Double @[], x811 @Natural @Double @[]] = tproject1 h702 in x811, 0, negate (sin (let [x812 @Natural @Double @[], x813 @Natural @Double @[]] = h767 in x813)) * (x770 * x805 + x770 * x805 + x781 * x795 + x781 * x795) + cos (let [x814 @Natural @Double @[], x815 @Natural @Double @[]] = h767 in x815) * (-1.0 * (let [x816 @Natural @Double @[], x817 @Natural @Double @[], x818 @Natural @Double @[], x819 @Natural @Double @[], x820 @Natural @Double @[], x821 @Natural @Double @[]] = tproject2 h702 in x818 * x796))]) [let [x355 @Natural @Double @[], x356 @Natural @Double @[], x357 @Natural @Double @[]] = tproject1 h306 in x355] [let [x369 @Natural @Double @[], v370 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h822 -> let [x837 @Natural @Double @[]] = tproject1 h822 in let [x838 @Natural @Double @[], x839 @Natural @Double @[], x840 @Natural @Double @[]] = tproject2 h822 in let x841 = cos x840 in [x837 + x838 * recip (x841 * x841), x837]) (\\h842 -> let x871 = cos (let [x867 @Natural @Double @[], x868 @Natural @Double @[], x869 @Natural @Double @[], x870 @Natural @Double @[]] = tproject2 h842 in x870) ; x872 = x871 * x871 ; x881 = let [x873 @Natural @Double @[], x874 @Natural @Double @[], x875 @Natural @Double @[], x876 @Natural @Double @[]] = tproject1 h842 in x876 * negate (sin (let [x877 @Natural @Double @[], x878 @Natural @Double @[], x879 @Natural @Double @[], x880 @Natural @Double @[]] = tproject2 h842 in x880)) in [let [x882 @Natural @Double @[], x883 @Natural @Double @[], x884 @Natural @Double @[], x885 @Natural @Double @[]] = tproject1 h842 in x882 + let [x886 @Natural @Double @[], x887 @Natural @Double @[], x888 @Natural @Double @[], x889 @Natural @Double @[]] = tproject1 h842 in x887 * recip x872 + ((x881 * x871 + x881 * x871) * negate (recip (x872 * x872))) * let [x890 @Natural @Double @[], x891 @Natural @Double @[], x892 @Natural @Double @[], x893 @Natural @Double @[]] = tproject2 h842 in x891, let [x894 @Natural @Double @[], x895 @Natural @Double @[], x896 @Natural @Double @[], x897 @Natural @Double @[]] = tproject1 h842 in x894]) (\\h898 -> let x923 = cos (let [x919 @Natural @Double @[], x920 @Natural @Double @[], x921 @Natural @Double @[], x922 @Natural @Double @[]] = tproject2 h898 in x922) ; x924 = x923 * x923 ; x931 = negate (recip (x924 * x924)) * (let [x925 @Natural @Double @[], x926 @Natural @Double @[], x927 @Natural @Double @[], x928 @Natural @Double @[]] = tproject2 h898 in x926 * let [x929 @Natural @Double @[], x930 @Natural @Double @[]] = tproject1 h898 in x929) in [let [x932 @Natural @Double @[], x933 @Natural @Double @[]] = tproject1 h898 in x932 + let [x934 @Natural @Double @[], x935 @Natural @Double @[]] = tproject1 h898 in x935, recip x924 * let [x936 @Natural @Double @[], x937 @Natural @Double @[]] = tproject1 h898 in x936, 0, negate (sin (let [x938 @Natural @Double @[], x939 @Natural @Double @[], x940 @Natural @Double @[], x941 @Natural @Double @[]] = tproject2 h898 in x941)) * (x923 * x931 + x923 * x931)]) [let [x358 @Natural @Double @[], x359 @Natural @Double @[], x360 @Natural @Double @[]] = tproject1 h306 in x360] [rreplicate 2 (let [x361 @Natural @Double @[], x362 @Natural @Double @[], x363 @Natural @Double @[]] = tproject1 h306 in x362), let [x364 @Natural @Double @[], v365 @Natural @Double @[2], v366 @Natural @Double @[2]] = h348 in v365, rreplicate 2 (let [x367 @Natural @Double @[], x368 @Natural @Double @[]] = h343 in x367)] in v370, rreplicate 2 (let [x371 @Natural @Double @[], x372 @Natural @Double @[], x373 @Natural @Double @[]] = tproject1 h306 in x372), let [x377 @Natural @Double @[], v378 @Natural @Double @[2], v379 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h942 -> let [x956 @Natural @Double @[]] = tproject1 h942 in let [x961 @Natural @Double @[], x962 @Natural @Double @[]] = let [x957 @Natural @Double @[]] = tproject1 h942 in let [x958 @Natural @Double @[], x959 @Natural @Double @[]] = tproject2 h942 in let x960 = cos x959 in [x957, recip (x960 * x960) * x957] in [x961, x956, x962]) (\\h963 -> let [x996 @Natural @Double @[], x997 @Natural @Double @[], x998 @Natural @Double @[]] = tproject1 h963 in let h1005 = [let [x999 @Natural @Double @[], x1000 @Natural @Double @[], x1001 @Natural @Double @[]] = tproject2 h963 in x1000, let [x1002 @Natural @Double @[], x1003 @Natural @Double @[], x1004 @Natural @Double @[]] = tproject2 h963 in x1004] ; x1008 = cos (let [x1006 @Natural @Double @[], x1007 @Natural @Double @[]] = h1005 in x1007) ; x1009 = x1008 * x1008 ; x1015 = let [x1010 @Natural @Double @[], x1011 @Natural @Double @[], x1012 @Natural @Double @[]] = tproject1 h963 in x1012 * negate (sin (let [x1013 @Natural @Double @[], x1014 @Natural @Double @[]] = h1005 in x1014)) in [let [x1016 @Natural @Double @[], x1017 @Natural @Double @[], x1018 @Natural @Double @[]] = tproject1 h963 in x1016, x996, ((x1015 * x1008 + x1015 * x1008) * negate (recip (x1009 * x1009))) * let [x1019 @Natural @Double @[], x1020 @Natural @Double @[], x1021 @Natural @Double @[]] = tproject2 h963 in x1019 + let [x1022 @Natural @Double @[], x1023 @Natural @Double @[], x1024 @Natural @Double @[]] = tproject1 h963 in x1022 * recip x1009]) (\\h1025 -> let [x1080 @Natural @Double @[], x1081 @Natural @Double @[], x1082 @Natural @Double @[]] = tproject1 h1025 in let h1089 = [let [x1083 @Natural @Double @[], x1084 @Natural @Double @[], x1085 @Natural @Double @[]] = tproject2 h1025 in x1084, let [x1086 @Natural @Double @[], x1087 @Natural @Double @[], x1088 @Natural @Double @[]] = tproject2 h1025 in x1088] ; x1092 = cos (let [x1090 @Natural @Double @[], x1091 @Natural @Double @[]] = h1089 in x1091) ; x1093 = x1092 * x1092 ; x1097 = negate (recip (x1093 * x1093)) * (let [x1094 @Natural @Double @[], x1095 @Natural @Double @[], x1096 @Natural @Double @[]] = tproject2 h1025 in x1094 * x1082) in [x1081 + recip x1093 * x1082 + x1080, 0.0, negate (sin (let [x1098 @Natural @Double @[], x1099 @Natural @Double @[]] = h1089 in x1099)) * (x1092 * x1097 + x1092 * x1097)]) [let [x374 @Natural @Double @[], x375 @Natural @Double @[], x376 @Natural @Double @[]] = tproject2 h306 in x374] h354 in v378, let [v380 @Natural @Double @[2], v381 @Natural @Double @[2]] = h354 in v380, let [v382 @Natural @Double @[2], v383 @Natural @Double @[2]] = h354 in v383] in [rsum (let [x385 @Natural @Double @[], v386 @Natural @Double @[2]] = h384 in v386), let [x387 @Natural @Double @[], v388 @Natural @Double @[2]] = h384 in x387]) (\\h1100 -> let h1140 = [let [x1134 @Natural @Double @[], x1135 @Natural @Double @[], x1136 @Natural @Double @[]] = tproject2 h1100 in x1135, let [x1137 @Natural @Double @[], x1138 @Natural @Double @[], x1139 @Natural @Double @[]] = tproject2 h1100 in x1139] ; h1145 = dmapAccumLDer (SNat @2) (\\h1206 -> let [x1220 @Natural @Double @[]] = tproject1 h1206 in let [x1225 @Natural @Double @[], x1226 @Natural @Double @[]] = let [x1221 @Natural @Double @[]] = tproject1 h1206 in let [x1224 @Natural @Double @[]] = let [x1222 @Natural @Double @[]] = tproject1 h1206 in let [x1223 @Natural @Double @[]] = tproject2 h1206 in [x1222 + tan x1223] in [x1224, x1221] in [x1225, x1220, x1226]) (\\h1227 -> let [x1252 @Natural @Double @[], x1253 @Natural @Double @[]] = tproject1 h1227 in let [x1263 @Natural @Double @[], x1264 @Natural @Double @[]] = let [x1254 @Natural @Double @[], x1255 @Natural @Double @[]] = tproject1 h1227 in let x1258 = cos (let [x1256 @Natural @Double @[], x1257 @Natural @Double @[]] = tproject2 h1227 in x1257) in [let [x1259 @Natural @Double @[], x1260 @Natural @Double @[]] = tproject1 h1227 in x1259 + let [x1261 @Natural @Double @[], x1262 @Natural @Double @[]] = tproject1 h1227 in x1262 * recip (x1258 * x1258), x1254] in [x1263, x1252, x1264]) (\\h1265 -> let [x1283 @Natural @Double @[], x1284 @Natural @Double @[], x1285 @Natural @Double @[]] = tproject1 h1265 in let x1288 = cos (let [x1286 @Natural @Double @[], x1287 @Natural @Double @[]] = tproject2 h1265 in x1287) in [x1284 + x1283 + x1285, recip (x1288 * x1288) * x1283]) [let [x1141 @Natural @Double @[], x1142 @Natural @Double @[]] = h1140 in x1142] [rreplicate 2 (let [x1143 @Natural @Double @[], x1144 @Natural @Double @[]] = h1140 in x1143)] ; h1151 = [let [x1146 @Natural @Double @[], v1147 @Natural @Double @[2], v1148 @Natural @Double @[2]] = h1145 in v1148, rreplicate 2 (let [x1149 @Natural @Double @[], x1150 @Natural @Double @[]] = h1140 in x1149)] ; h1154 = [let [x1152 @Natural @Double @[], x1153 @Natural @Double @[]] = tproject1 h1100 in x1153, 0] ; h1157 = [0, rreplicate 2 (let [x1155 @Natural @Double @[], x1156 @Natural @Double @[]] = tproject1 h1100 in x1155)] ; h1166 = [let [x1158 @Natural @Double @[], v1159 @Natural @Double @[2]] = h1157 in x1158 + let [x1160 @Natural @Double @[], v1161 @Natural @Double @[2]] = h1154 in x1160, let [x1162 @Natural @Double @[], v1163 @Natural @Double @[2]] = h1157 in v1163 + let [x1164 @Natural @Double @[], v1165 @Natural @Double @[2]] = h1154 in v1165] ; h1181 = dmapAccumLDer (SNat @2) (\\h1289 -> let [x1343 @Natural @Double @[]] = tproject1 h1289 in let [x1344 @Natural @Double @[], x1345 @Natural @Double @[], x1346 @Natural @Double @[], x1347 @Natural @Double @[]] = tproject2 h1289 in let h1348 = [x1346, x1347] ; x1351 = cos (let [x1349 @Natural @Double @[], x1350 @Natural @Double @[]] = h1348 in x1350) ; x1352 = x1351 * x1351 ; x1353 = negate (recip (x1352 * x1352)) * (x1345 * x1344) in [recip x1352 * x1344 + x1343, 0, negate (sin (let [x1354 @Natural @Double @[], x1355 @Natural @Double @[]] = h1348 in x1355)) * (x1351 * x1353 + x1351 * x1353)]) (\\h1356 -> let h1426 = [let [x1416 @Natural @Double @[], x1417 @Natural @Double @[], x1418 @Natural @Double @[], x1419 @Natural @Double @[], x1420 @Natural @Double @[]] = tproject2 h1356 in x1419, let [x1421 @Natural @Double @[], x1422 @Natural @Double @[], x1423 @Natural @Double @[], x1424 @Natural @Double @[], x1425 @Natural @Double @[]] = tproject2 h1356 in x1425] ; x1429 = cos (let [x1427 @Natural @Double @[], x1428 @Natural @Double @[]] = h1426 in x1428) ; x1430 = x1429 * x1429 ; x1431 = x1430 * x1430 ; x1432 = negate (recip x1431) ; x1443 = let [x1433 @Natural @Double @[], x1434 @Natural @Double @[], x1435 @Natural @Double @[], x1436 @Natural @Double @[], x1437 @Natural @Double @[]] = tproject2 h1356 in x1435 * let [x1438 @Natural @Double @[], x1439 @Natural @Double @[], x1440 @Natural @Double @[], x1441 @Natural @Double @[], x1442 @Natural @Double @[]] = tproject2 h1356 in x1439 ; x1444 = x1432 * x1443 ; x1452 = let [x1445 @Natural @Double @[], x1446 @Natural @Double @[], x1447 @Natural @Double @[], x1448 @Natural @Double @[], x1449 @Natural @Double @[]] = tproject1 h1356 in x1449 * negate (sin (let [x1450 @Natural @Double @[], x1451 @Natural @Double @[]] = h1426 in x1451)) ; x1453 = x1452 * x1429 + x1452 * x1429 ; x1474 = (((x1453 * x1430 + x1453 * x1430) * negate (recip (x1431 * x1431))) * -1.0) * x1443 + (let [x1454 @Natural @Double @[], x1455 @Natural @Double @[], x1456 @Natural @Double @[], x1457 @Natural @Double @[], x1458 @Natural @Double @[]] = tproject1 h1356 in x1456 * let [x1459 @Natural @Double @[], x1460 @Natural @Double @[], x1461 @Natural @Double @[], x1462 @Natural @Double @[], x1463 @Natural @Double @[]] = tproject2 h1356 in x1460 + let [x1464 @Natural @Double @[], x1465 @Natural @Double @[], x1466 @Natural @Double @[], x1467 @Natural @Double @[], x1468 @Natural @Double @[]] = tproject1 h1356 in x1465 * let [x1469 @Natural @Double @[], x1470 @Natural @Double @[], x1471 @Natural @Double @[], x1472 @Natural @Double @[], x1473 @Natural @Double @[]] = tproject2 h1356 in x1471) * x1432 in [let [x1475 @Natural @Double @[], x1476 @Natural @Double @[], x1477 @Natural @Double @[], x1478 @Natural @Double @[], x1479 @Natural @Double @[]] = tproject1 h1356 in x1475 + (x1453 * negate (recip (x1430 * x1430))) * let [x1480 @Natural @Double @[], x1481 @Natural @Double @[], x1482 @Natural @Double @[], x1483 @Natural @Double @[], x1484 @Natural @Double @[]] = tproject2 h1356 in x1481 + let [x1485 @Natural @Double @[], x1486 @Natural @Double @[], x1487 @Natural @Double @[], x1488 @Natural @Double @[], x1489 @Natural @Double @[]] = tproject1 h1356 in x1486 * recip x1430, 0.0, ((let [x1490 @Natural @Double @[], x1491 @Natural @Double @[], x1492 @Natural @Double @[], x1493 @Natural @Double @[], x1494 @Natural @Double @[]] = tproject1 h1356 in x1494 * cos (let [x1495 @Natural @Double @[], x1496 @Natural @Double @[]] = h1426 in x1496)) * -1.0) * (x1429 * x1444 + x1429 * x1444) + (x1452 * x1444 + x1474 * x1429 + x1452 * x1444 + x1474 * x1429) * negate (sin (let [x1497 @Natural @Double @[], x1498 @Natural @Double @[]] = h1426 in x1498))]) (\\h1499 -> let h1558 = [let [x1548 @Natural @Double @[], x1549 @Natural @Double @[], x1550 @Natural @Double @[], x1551 @Natural @Double @[], x1552 @Natural @Double @[]] = tproject2 h1499 in x1551, let [x1553 @Natural @Double @[], x1554 @Natural @Double @[], x1555 @Natural @Double @[], x1556 @Natural @Double @[], x1557 @Natural @Double @[]] = tproject2 h1499 in x1557] ; x1561 = cos (let [x1559 @Natural @Double @[], x1560 @Natural @Double @[]] = h1558 in x1560) ; x1562 = x1561 * x1561 ; x1563 = x1562 * x1562 ; x1564 = negate (recip x1563) ; x1575 = let [x1565 @Natural @Double @[], x1566 @Natural @Double @[], x1567 @Natural @Double @[], x1568 @Natural @Double @[], x1569 @Natural @Double @[]] = tproject2 h1499 in x1567 * let [x1570 @Natural @Double @[], x1571 @Natural @Double @[], x1572 @Natural @Double @[], x1573 @Natural @Double @[], x1574 @Natural @Double @[]] = tproject2 h1499 in x1571 ; x1576 = x1564 * x1575 ; x1582 = negate (sin (let [x1577 @Natural @Double @[], x1578 @Natural @Double @[]] = h1558 in x1578)) * let [x1579 @Natural @Double @[], x1580 @Natural @Double @[], x1581 @Natural @Double @[]] = tproject1 h1499 in x1581 ; x1583 = x1561 * x1582 + x1561 * x1582 ; x1584 = x1564 * x1583 ; x1585 = negate (recip (x1563 * x1563)) * (-1.0 * (x1575 * x1583)) ; x1594 = x1562 * x1585 + x1562 * x1585 + negate (recip (x1562 * x1562)) * (let [x1586 @Natural @Double @[], x1587 @Natural @Double @[], x1588 @Natural @Double @[], x1589 @Natural @Double @[], x1590 @Natural @Double @[]] = tproject2 h1499 in x1587 * let [x1591 @Natural @Double @[], x1592 @Natural @Double @[], x1593 @Natural @Double @[]] = tproject1 h1499 in x1591) in [let [x1595 @Natural @Double @[], x1596 @Natural @Double @[], x1597 @Natural @Double @[]] = tproject1 h1499 in x1595, let [x1598 @Natural @Double @[], x1599 @Natural @Double @[], x1600 @Natural @Double @[], x1601 @Natural @Double @[], x1602 @Natural @Double @[]] = tproject2 h1499 in x1600 * x1584 + recip x1562 * let [x1603 @Natural @Double @[], x1604 @Natural @Double @[], x1605 @Natural @Double @[]] = tproject1 h1499 in x1603, let [x1606 @Natural @Double @[], x1607 @Natural @Double @[], x1608 @Natural @Double @[], x1609 @Natural @Double @[], x1610 @Natural @Double @[]] = tproject2 h1499 in x1607 * x1584, 0, negate (sin (let [x1611 @Natural @Double @[], x1612 @Natural @Double @[]] = h1558 in x1612)) * (x1561 * x1594 + x1561 * x1594 + x1576 * x1582 + x1576 * x1582) + cos (let [x1613 @Natural @Double @[], x1614 @Natural @Double @[]] = h1558 in x1614) * (-1.0 * ((x1561 * x1576 + x1561 * x1576) * let [x1615 @Natural @Double @[], x1616 @Natural @Double @[], x1617 @Natural @Double @[]] = tproject1 h1499 in x1617))]) [let [x1167 @Natural @Double @[], v1168 @Natural @Double @[2]] = h1166 in x1167] [let [x1169 @Natural @Double @[], v1170 @Natural @Double @[2]] = h1166 in v1170, let [x1174 @Natural @Double @[], v1175 @Natural @Double @[2], v1176 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h1618 -> let [x1632 @Natural @Double @[]] = tproject1 h1618 in let [x1637 @Natural @Double @[], x1638 @Natural @Double @[]] = let [x1633 @Natural @Double @[]] = tproject1 h1618 in let [x1634 @Natural @Double @[], x1635 @Natural @Double @[]] = tproject2 h1618 in let x1636 = cos x1635 in [x1633, recip (x1636 * x1636) * x1633] in [x1637, x1632, x1638]) (\\h1639 -> let [x1699 @Natural @Double @[], x1700 @Natural @Double @[], x1701 @Natural @Double @[]] = tproject1 h1639 in let h1708 = [let [x1702 @Natural @Double @[], x1703 @Natural @Double @[], x1704 @Natural @Double @[]] = tproject2 h1639 in x1703, let [x1705 @Natural @Double @[], x1706 @Natural @Double @[], x1707 @Natural @Double @[]] = tproject2 h1639 in x1707] ; x1711 = cos (let [x1709 @Natural @Double @[], x1710 @Natural @Double @[]] = h1708 in x1710) ; x1712 = x1711 * x1711 ; x1718 = let [x1713 @Natural @Double @[], x1714 @Natural @Double @[], x1715 @Natural @Double @[]] = tproject1 h1639 in x1715 * negate (sin (let [x1716 @Natural @Double @[], x1717 @Natural @Double @[]] = h1708 in x1717)) in [let [x1719 @Natural @Double @[], x1720 @Natural @Double @[], x1721 @Natural @Double @[]] = tproject1 h1639 in x1719, x1699, ((x1718 * x1711 + x1718 * x1711) * negate (recip (x1712 * x1712))) * let [x1722 @Natural @Double @[], x1723 @Natural @Double @[], x1724 @Natural @Double @[]] = tproject2 h1639 in x1722 + let [x1725 @Natural @Double @[], x1726 @Natural @Double @[], x1727 @Natural @Double @[]] = tproject1 h1639 in x1725 * recip x1712]) (\\h1728 -> let [x1759 @Natural @Double @[], x1760 @Natural @Double @[], x1761 @Natural @Double @[]] = tproject1 h1728 in let h1768 = [let [x1762 @Natural @Double @[], x1763 @Natural @Double @[], x1764 @Natural @Double @[]] = tproject2 h1728 in x1763, let [x1765 @Natural @Double @[], x1766 @Natural @Double @[], x1767 @Natural @Double @[]] = tproject2 h1728 in x1767] ; x1771 = cos (let [x1769 @Natural @Double @[], x1770 @Natural @Double @[]] = h1768 in x1770) ; x1772 = x1771 * x1771 ; x1776 = negate (recip (x1772 * x1772)) * (let [x1773 @Natural @Double @[], x1774 @Natural @Double @[], x1775 @Natural @Double @[]] = tproject2 h1728 in x1773 * x1761) in [x1760 + recip x1772 * x1761 + x1759, 0.0, negate (sin (let [x1777 @Natural @Double @[], x1778 @Natural @Double @[]] = h1768 in x1778)) * (x1771 * x1776 + x1771 * x1776)]) [let [x1171 @Natural @Double @[], x1172 @Natural @Double @[], x1173 @Natural @Double @[]] = tproject2 h1100 in x1171] h1151 in v1175, let [v1177 @Natural @Double @[2], v1178 @Natural @Double @[2]] = h1151 in v1177, let [v1179 @Natural @Double @[2], v1180 @Natural @Double @[2]] = h1151 in v1180] ; h1185 = [0, let [x1182 @Natural @Double @[], v1183 @Natural @Double @[2], v1184 @Natural @Double @[2]] = h1181 in v1183] ; h1195 = dmapAccumRDer (SNat @2) (\\h1779 -> let [x1790 @Natural @Double @[]] = tproject1 h1779 in let [x1791 @Natural @Double @[], x1792 @Natural @Double @[], x1793 @Natural @Double @[]] = tproject2 h1779 in let x1794 = cos x1793 in [x1790 + x1791, recip (x1794 * x1794) * x1790]) (\\h1795 -> let x1820 = cos (let [x1816 @Natural @Double @[], x1817 @Natural @Double @[], x1818 @Natural @Double @[], x1819 @Natural @Double @[]] = tproject2 h1795 in x1819) ; x1821 = x1820 * x1820 ; x1830 = let [x1822 @Natural @Double @[], x1823 @Natural @Double @[], x1824 @Natural @Double @[], x1825 @Natural @Double @[]] = tproject1 h1795 in x1825 * negate (sin (let [x1826 @Natural @Double @[], x1827 @Natural @Double @[], x1828 @Natural @Double @[], x1829 @Natural @Double @[]] = tproject2 h1795 in x1829)) in [let [x1831 @Natural @Double @[], x1832 @Natural @Double @[], x1833 @Natural @Double @[], x1834 @Natural @Double @[]] = tproject1 h1795 in x1831 + let [x1835 @Natural @Double @[], x1836 @Natural @Double @[], x1837 @Natural @Double @[], x1838 @Natural @Double @[]] = tproject1 h1795 in x1836, ((x1830 * x1820 + x1830 * x1820) * negate (recip (x1821 * x1821))) * let [x1839 @Natural @Double @[], x1840 @Natural @Double @[], x1841 @Natural @Double @[], x1842 @Natural @Double @[]] = tproject2 h1795 in x1839 + let [x1843 @Natural @Double @[], x1844 @Natural @Double @[], x1845 @Natural @Double @[], x1846 @Natural @Double @[]] = tproject1 h1795 in x1843 * recip x1821]) (\\h1847 -> let x1868 = cos (let [x1864 @Natural @Double @[], x1865 @Natural @Double @[], x1866 @Natural @Double @[], x1867 @Natural @Double @[]] = tproject2 h1847 in x1867) ; x1869 = x1868 * x1868 ; x1876 = negate (recip (x1869 * x1869)) * (let [x1870 @Natural @Double @[], x1871 @Natural @Double @[], x1872 @Natural @Double @[], x1873 @Natural @Double @[]] = tproject2 h1847 in x1870 * let [x1874 @Natural @Double @[], x1875 @Natural @Double @[]] = tproject1 h1847 in x1875) in [let [x1877 @Natural @Double @[], x1878 @Natural @Double @[]] = tproject1 h1847 in x1877 + recip x1869 * let [x1879 @Natural @Double @[], x1880 @Natural @Double @[]] = tproject1 h1847 in x1880, let [x1881 @Natural @Double @[], x1882 @Natural @Double @[]] = tproject1 h1847 in x1881, 0, negate (sin (let [x1883 @Natural @Double @[], x1884 @Natural @Double @[], x1885 @Natural @Double @[], x1886 @Natural @Double @[]] = tproject2 h1847 in x1886)) * (x1868 * x1876 + x1868 * x1876)]) [let [x1186 @Natural @Double @[], v1187 @Natural @Double @[2]] = h1185 in x1186] [let [x1188 @Natural @Double @[], v1189 @Natural @Double @[2]] = h1185 in v1189, let [x1190 @Natural @Double @[], v1191 @Natural @Double @[2], v1192 @Natural @Double @[2]] = h1145 in v1191, rreplicate 2 (let [x1193 @Natural @Double @[], x1194 @Natural @Double @[]] = h1140 in x1193)] in [let [x1196 @Natural @Double @[], v1197 @Natural @Double @[2], v1198 @Natural @Double @[2]] = h1181 in x1196, rsum (let [x1199 @Natural @Double @[], v1200 @Natural @Double @[2]] = h1195 in v1200) + rsum (let [x1201 @Natural @Double @[], v1202 @Natural @Double @[2], v1203 @Natural @Double @[2]] = h1181 in v1203), let [x1204 @Natural @Double @[], v1205 @Natural @Double @[2]] = h1195 in x1204]) [1.0] [let [x8 @Natural @Double @[], v9 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h1887 -> let [x1896 @Natural @Double @[]] = tproject1 h1887 in let [x1899 @Natural @Double @[]] = let [x1897 @Natural @Double @[]] = tproject1 h1887 in let [x1898 @Natural @Double @[]] = tproject2 h1887 in dmapAccumLDer (SNat @2) (\\h1900 -> let [x1907 @Natural @Double @[]] = tproject1 h1900 in let [x1908 @Natural @Double @[]] = tproject2 h1900 in [x1907 + tan x1908]) (\\h1909 -> let x1928 = cos (let [x1926 @Natural @Double @[], x1927 @Natural @Double @[]] = tproject2 h1909 in x1927) in [let [x1929 @Natural @Double @[], x1930 @Natural @Double @[]] = tproject1 h1909 in x1929 + let [x1931 @Natural @Double @[], x1932 @Natural @Double @[]] = tproject1 h1909 in x1932 * recip (x1928 * x1928)]) (\\h1933 -> let x1948 = cos (let [x1946 @Natural @Double @[], x1947 @Natural @Double @[]] = tproject2 h1933 in x1947) in [let [x1949 @Natural @Double @[]] = tproject1 h1933 in x1949, recip (x1948 * x1948) * let [x1950 @Natural @Double @[]] = tproject1 h1933 in x1950]) [x1898] [rreplicate 2 x1897] in [x1899, x1896]) (\\h1951 -> let [x1976 @Natural @Double @[], x1977 @Natural @Double @[]] = tproject1 h1951 in [let [x1990 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\h1992 -> let [x2026 @Natural @Double @[]] = tproject1 h1992 in let [x2027 @Natural @Double @[], x2028 @Natural @Double @[], x2029 @Natural @Double @[]] = tproject2 h1992 in let h2030 = [x2026, x2027] ; x2031 = cos x2029 in [let [x2032 @Natural @Double @[], x2033 @Natural @Double @[]] = h2030 in x2032 + let [x2034 @Natural @Double @[], x2035 @Natural @Double @[]] = h2030 in x2035 * recip (x2031 * x2031)]) (\\h2036 -> let h2106 = [let [x2098 @Natural @Double @[], x2099 @Natural @Double @[], x2100 @Natural @Double @[], x2101 @Natural @Double @[]] = tproject2 h2036 in x2100, let [x2102 @Natural @Double @[], x2103 @Natural @Double @[], x2104 @Natural @Double @[], x2105 @Natural @Double @[]] = tproject2 h2036 in x2105] ; x2109 = cos (let [x2107 @Natural @Double @[], x2108 @Natural @Double @[]] = h2106 in x2108) ; x2110 = x2109 * x2109 ; x2117 = let [x2111 @Natural @Double @[], x2112 @Natural @Double @[], x2113 @Natural @Double @[], x2114 @Natural @Double @[]] = tproject1 h2036 in x2114 * negate (sin (let [x2115 @Natural @Double @[], x2116 @Natural @Double @[]] = h2106 in x2116)) in [let [x2118 @Natural @Double @[], x2119 @Natural @Double @[], x2120 @Natural @Double @[], x2121 @Natural @Double @[]] = tproject1 h2036 in x2118 + let [x2122 @Natural @Double @[], x2123 @Natural @Double @[], x2124 @Natural @Double @[], x2125 @Natural @Double @[]] = tproject1 h2036 in x2123 * recip x2110 + ((x2117 * x2109 + x2117 * x2109) * negate (recip (x2110 * x2110))) * let [x2126 @Natural @Double @[], x2127 @Natural @Double @[], x2128 @Natural @Double @[], x2129 @Natural @Double @[]] = tproject2 h2036 in x2127]) (\\h2130 -> let h2187 = [let [x2179 @Natural @Double @[], x2180 @Natural @Double @[], x2181 @Natural @Double @[], x2182 @Natural @Double @[]] = tproject2 h2130 in x2181, let [x2183 @Natural @Double @[], x2184 @Natural @Double @[], x2185 @Natural @Double @[], x2186 @Natural @Double @[]] = tproject2 h2130 in x2186] ; x2190 = cos (let [x2188 @Natural @Double @[], x2189 @Natural @Double @[]] = h2187 in x2189) ; x2191 = x2190 * x2190 ; x2197 = negate (recip (x2191 * x2191)) * (let [x2192 @Natural @Double @[], x2193 @Natural @Double @[], x2194 @Natural @Double @[], x2195 @Natural @Double @[]] = tproject2 h2130 in x2193 * let [x2196 @Natural @Double @[]] = tproject1 h2130 in x2196) in [let [x2198 @Natural @Double @[]] = tproject1 h2130 in x2198, recip x2191 * let [x2199 @Natural @Double @[]] = tproject1 h2130 in x2199, 0, negate (sin (let [x2200 @Natural @Double @[], x2201 @Natural @Double @[]] = h2187 in x2201)) * (x2190 * x2197 + x2190 * x2197)]) [let [x1978 @Natural @Double @[], x1979 @Natural @Double @[]] = tproject1 h1951 in x1979] [rreplicate 2 (let [x1980 @Natural @Double @[], x1981 @Natural @Double @[]] = tproject1 h1951 in x1980), let [x1986 @Natural @Double @[], v1987 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h2202 -> let [x2216 @Natural @Double @[]] = tproject1 h2202 in let [x2219 @Natural @Double @[]] = let [x2217 @Natural @Double @[]] = tproject1 h2202 in let [x2218 @Natural @Double @[]] = tproject2 h2202 in [x2217 + tan x2218] in [x2219, x2216]) (\\h2220 -> let [x2242 @Natural @Double @[], x2243 @Natural @Double @[]] = tproject1 h2220 in let x2246 = cos (let [x2244 @Natural @Double @[], x2245 @Natural @Double @[]] = tproject2 h2220 in x2245) in [let [x2247 @Natural @Double @[], x2248 @Natural @Double @[]] = tproject1 h2220 in x2247 + let [x2249 @Natural @Double @[], x2250 @Natural @Double @[]] = tproject1 h2220 in x2250 * recip (x2246 * x2246), x2242]) (\\h2251 -> let [x2274 @Natural @Double @[], x2275 @Natural @Double @[]] = tproject1 h2251 in let x2278 = cos (let [x2276 @Natural @Double @[], x2277 @Natural @Double @[]] = tproject2 h2251 in x2277) in [x2274 + x2275, recip (x2278 * x2278) * x2274]) [let [x1982 @Natural @Double @[], x1983 @Natural @Double @[]] = tproject2 h1951 in x1983] [rreplicate 2 (let [x1984 @Natural @Double @[], x1985 @Natural @Double @[]] = tproject2 h1951 in x1984)] in v1987, rreplicate 2 (let [x1988 @Natural @Double @[], x1989 @Natural @Double @[]] = tproject2 h1951 in x1988)] in x1990, x1976]) (\\h2279 -> let [x2299 @Natural @Double @[], x2300 @Natural @Double @[]] = tproject1 h2279 in let h2309 = dmapAccumRDer (SNat @2) (\\h2316 -> let [x2322 @Natural @Double @[]] = tproject1 h2316 in let [x2323 @Natural @Double @[], x2324 @Natural @Double @[]] = tproject2 h2316 in let x2325 = cos x2324 in [x2322, recip (x2325 * x2325) * x2322]) (\\h2326 -> let h2360 = [let [x2354 @Natural @Double @[], x2355 @Natural @Double @[], x2356 @Natural @Double @[]] = tproject2 h2326 in x2355, let [x2357 @Natural @Double @[], x2358 @Natural @Double @[], x2359 @Natural @Double @[]] = tproject2 h2326 in x2359] ; x2363 = cos (let [x2361 @Natural @Double @[], x2362 @Natural @Double @[]] = h2360 in x2362) ; x2364 = x2363 * x2363 ; x2370 = let [x2365 @Natural @Double @[], x2366 @Natural @Double @[], x2367 @Natural @Double @[]] = tproject1 h2326 in x2367 * negate (sin (let [x2368 @Natural @Double @[], x2369 @Natural @Double @[]] = h2360 in x2369)) in [let [x2371 @Natural @Double @[], x2372 @Natural @Double @[], x2373 @Natural @Double @[]] = tproject1 h2326 in x2371, ((x2370 * x2363 + x2370 * x2363) * negate (recip (x2364 * x2364))) * let [x2374 @Natural @Double @[], x2375 @Natural @Double @[], x2376 @Natural @Double @[]] = tproject2 h2326 in x2374 + let [x2377 @Natural @Double @[], x2378 @Natural @Double @[], x2379 @Natural @Double @[]] = tproject1 h2326 in x2377 * recip x2364]) (\\h2380 -> let h2411 = [let [x2405 @Natural @Double @[], x2406 @Natural @Double @[], x2407 @Natural @Double @[]] = tproject2 h2380 in x2406, let [x2408 @Natural @Double @[], x2409 @Natural @Double @[], x2410 @Natural @Double @[]] = tproject2 h2380 in x2410] ; x2414 = cos (let [x2412 @Natural @Double @[], x2413 @Natural @Double @[]] = h2411 in x2413) ; x2415 = x2414 * x2414 ; x2421 = negate (recip (x2415 * x2415)) * (let [x2416 @Natural @Double @[], x2417 @Natural @Double @[], x2418 @Natural @Double @[]] = tproject2 h2380 in x2416 * let [x2419 @Natural @Double @[], x2420 @Natural @Double @[]] = tproject1 h2380 in x2420) in [recip x2415 * let [x2422 @Natural @Double @[], x2423 @Natural @Double @[]] = tproject1 h2380 in x2423 + let [x2424 @Natural @Double @[], x2425 @Natural @Double @[]] = tproject1 h2380 in x2424, 0, negate (sin (let [x2426 @Natural @Double @[], x2427 @Natural @Double @[]] = h2411 in x2427)) * (x2414 * x2421 + x2414 * x2421)]) [x2299] [let [x2305 @Natural @Double @[], v2306 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h2428 -> let [x2434 @Natural @Double @[]] = tproject1 h2428 in let [x2437 @Natural @Double @[]] = let [x2435 @Natural @Double @[]] = tproject1 h2428 in let [x2436 @Natural @Double @[]] = tproject2 h2428 in [x2435 + tan x2436] in [x2437, x2434]) (\\h2438 -> let [x2449 @Natural @Double @[], x2450 @Natural @Double @[]] = tproject1 h2438 in let x2453 = cos (let [x2451 @Natural @Double @[], x2452 @Natural @Double @[]] = tproject2 h2438 in x2452) in [let [x2454 @Natural @Double @[], x2455 @Natural @Double @[]] = tproject1 h2438 in x2454 + let [x2456 @Natural @Double @[], x2457 @Natural @Double @[]] = tproject1 h2438 in x2457 * recip (x2453 * x2453), x2449]) (\\h2458 -> let [x2465 @Natural @Double @[], x2466 @Natural @Double @[]] = tproject1 h2458 in let x2469 = cos (let [x2467 @Natural @Double @[], x2468 @Natural @Double @[]] = tproject2 h2458 in x2468) in [x2465 + x2466, recip (x2469 * x2469) * x2465]) [let [x2301 @Natural @Double @[], x2302 @Natural @Double @[]] = tproject2 h2279 in x2302] [rreplicate 2 (let [x2303 @Natural @Double @[], x2304 @Natural @Double @[]] = tproject2 h2279 in x2303)] in v2306, rreplicate 2 (let [x2307 @Natural @Double @[], x2308 @Natural @Double @[]] = tproject2 h2279 in x2307)] in [rsum (let [x2310 @Natural @Double @[], v2311 @Natural @Double @[2]] = h2309 in v2311) + x2300, let [x2313 @Natural @Double @[], v2314 @Natural @Double @[2]] = h2309 in x2313]) [1.1] [rreplicate 2 1.1] in v9, rreplicate 2 1.1] in [rsum (let [x12 @Natural @Double @[], v13 @Natural @Double @[2]] = h11 in v13) + let [x14 @Natural @Double @[], v15 @Natural @Double @[2]] = h11 in x14]"

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
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11814318

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
                                         $ DynamicRanked $ rscalar 0.01 * y + tan w)
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
  (rscalar 1.0837278549794862 :: ORArray Double 0)
  (rev
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
                                           $ DynamicRanked $ rscalar 0.01 * y + tan w)
                             (dmkHVector a5) (mkreplicate1HVector (SNat @2) x5))
                           (dmkHVector a4) (mkreplicate1HVector (SNat @2) x4))
                         (dmkHVector a3) (mkreplicate1HVector (SNat @2) x3))
                       (dmkHVector a2) (mkreplicate1HVector (SNat @2) x2))
                     (dmkHVector a) (mkreplicate1HVector (SNat @2) x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10r :: Assertion
testSin0MapAccumNestedR10r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781 :: ORArray Double 0)
  (rev
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
                                             $ rscalar 0.01 * y + tan w)
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
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10f :: Assertion
testSin0MapAccumNestedR10f = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781e-4 :: ORArray Double 0)
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
                                             $ rscalar 0.01 * y + tan w)
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
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10fN :: Assertion
testSin0MapAccumNestedR10fN = do
 assertEqualUpToEpsilon 1e-10
  ( srepl 1.379370673816781e-4 :: OSArray Float '[1]
  , rscalar 1.379370673816781e-4 :: ORArray Double 0)
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
                                             $ rscalar  0.01 * y + tan w)
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
      f x = (sfromList [scast $ sfromR $ g x], g x + rscalar  0.2)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10rf :: Assertion
testSin0MapAccumNestedR10rf = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: ORArray Double 0)
  (rev
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
                                             $ rscalar 0.01 * y + tan w)
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
    in rfwd1 f) (rscalar 0.0001))

testSin0MapAccumNestedR10rr :: Assertion
testSin0MapAccumNestedR10rr = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: ORArray Double 0)
  (rev
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
                                             $ rscalar 0.01 * y + tan w)
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
    in rrev1 f) (rscalar 0.0001))

testSin0FoldNestedS1FwdFwd0 :: Assertion
testSin0FoldNestedS1FwdFwd0 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
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
                                 x2 * sfwd1 (sfwd1 (\b2 -> srepl 0.7 * b2)) a2)
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
                                 x2 * srev1 (srev1 (\b2 -> srepl 0.7 * b2)) a2)
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
                          sfold (\x3 a3 -> srepl 0.7 * x3 * a3)
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
                            sfold (\x4 a4 -> srepl 0.1 * x4 * a4)
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
                              sfold (\x5 a5 -> srepl 0.1 * x5 * a5)
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
                                sfold (\x6 a6 -> sscalar 0.1 * x6 * a6)
                                      a5 (sreplicate @_ @1 x5))
                                    a4 (sreplicate @_ @1 x4))
                                  a3 (sreplicate @_ @1 x3))
                                a2 (sreplicate @_ @1 x2))
                              a (sreplicate @_ @1 x))
                            a0 (sreplicate @_ @1 a0)
  assertEqualUpToEpsilon 1e-10
    (srepl 0.22000000000000003)
    (srev1 @OSArray @Double @'[] @'[] f (sscalar 1.1))

testSin0FoldNestedS5fwd :: Assertion
testSin0FoldNestedS5fwd = do
  let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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
    (sfwd1 @OSArray @Double @'[] @'[] f (sscalar 1.1))

testSin0FoldNestedSi :: Assertion
testSin0FoldNestedSi = do
  assertEqualUpToEpsilon' 1e-10
    (-0.20775612781643243 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[3]
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
           in rfromS . f . sfromR) 1.1)

testSin0FoldNestedR1 :: Assertion
testSin0FoldNestedR1 = do
  assertEqualUpToEpsilon' 1e-10
    (2.0504979297616553e-43 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 -> rscalar 0.7 * x2 * a2)
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
                                 x2 * rfwd1 (rrev1 (\b2 -> rscalar 0.7 * b2)) a2)
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
                          rfold (\x3 a3 -> rscalar 0.7 * x3 * a3)
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
                                                               rscalar 0.7 * b3))) a3)
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
                            rfold (\x4 a4 -> rscalar 0.1 * x4 * a4)
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
                              rfold (\x5 a5 -> rscalar 0.1 * x5 * a5)
                                    a4 (rreplicate 2 x4))
                                  a3 (rreplicate 1 x3))
                                a2 (rreplicate 1 x2))
                              a (rreplicate 2 x))
                            a0 (rreplicate 1 a0)
           in f) 1.1)

_testSin0FoldNestedR41 :: Assertion
_testSin0FoldNestedR41 = do
  assertEqualUpToEpsilon' 1e-10
    (0.22000000000000003 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
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
                              rfold (\x5 a5 -> rscalar 0.1 * x5 * a5)
                                    a4 (rreplicate 0 x4))
                                  a3 (rreplicate 0 x3))
                                a2 (rreplicate 0 x2))
                              a (rreplicate 0 x))
                            a0 (rreplicate 0 a0)
           in f) 1.1)

_testSin0FoldNestedR400 :: Assertion
_testSin0FoldNestedR400 = do
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
                                              a (rscan (-) 0 (rslice 0 1 x))))
                            (rreplicate 3 $ (rscalar 2) * a0) (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR22 :: Assertion
testSin0FoldNestedR22 = do
  assertEqualUpToEpsilon' 1e-10
    (2.877421010384167e-5 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                          rfold (\x3 a3 -> rscalar 0.44 * x3 * a3)
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
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
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
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInlineAst a1))
    @?= 148802

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZSR))
             x
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (rscalar 0.4535961214255773))
    (f @ORArray (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

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
                                     $ DynamicRanked @Double @0 (rscalar 1.1)))
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
    (V.singleton $ DynamicRanked @Double @0 (rscalar (-0.8912073600614354)))
    (crev (h @ORArray) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

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
    (V.singleton $ DynamicShaped @Double @'[] (sscalar $ -0.8912073600614354))
    (crev (h @ORArray) (V.singleton $ DynamicShaped @Double @'[] (srepl 1.1)))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g.
           (HVectorTensor g (ShapedOf g), RankedTensor g, ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1 (rscanZip const doms 5)
               doms3 x (ringestData1 [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0])
    (crev (h @ORArray)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g.
           ( HVectorTensor g (ShapedOf g), ShapedTensor (ShapedOf g)
           , ProductTensor g )
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4] (sscanZip const doms (srepl 5))
               doms3 x (ingestData [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0])
    (crev (h @ORArray)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g.
           (HVectorTensor g (ShapedOf g), RankedTensor g, ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1
               (\v -> rscanZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 v)
                doms3 x (ringestData1 [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ ringestData1 [4.0,6.0,8.0])
    (crev (h @ORArray)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g.
           ( HVectorTensor g (ShapedOf g), ShapedTensor (ShapedOf g)
           , ProductTensor g )
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4]
               (\v -> sscanZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms (srepl 5) v)
               doms3 x (ingestData [1, 2, 3, 4])
      h :: forall g. ADReady g
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [4.0,6.0,8.0])
    (crev (h @ORArray)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

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
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [1, 1, 1])
    (crev (h @ORArray)
          (V.singleton $ DynamicShaped @Double @'[3]
           $ sreplicate @OSArray @3 (sscalar 1.1)))

fFoldZipR
  :: forall n r ranked.
     (KnownNat n, GoodScalar r, ADReady ranked)
  => VoidHVector
  -> ranked r (1 + n)
  -> HVector ranked
  -> (forall f. ADReady f
      => f r n -> f r n -> HVector f
      -> HVectorOf f)
  -> IShR n
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
              in rletHVectorIn (rf cr x a) $ \ !rfRes ->
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
                          (rf cr x a) $ \ !rfRes ->
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
  let h :: ranked ~ ORArray
        => HVector (ADVal ranked)
        -> ADVal (HVectorPseudoTensor ranked) Float '()
      h = hVectorADValToADVal . fFoldZipRX @(ADVal ORArray)
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (rscalar (-7.313585321642452e-2)) ])
    (crev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)
                        , DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1) ]))

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
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (rscalar (-7.313585321642452e-2)) ])
    (rev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)
                       , DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1) ]))

fFoldS
  :: forall m k rm shm r sh shaped.
     ( KnownNat k, GoodScalar rm, KnownShS shm, GoodScalar r, KnownShS sh
     , ADReadyS shaped, KnownNat m, X.Rank shm ~ m)
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
                         (rf cr x a) $ \ !rfRes ->
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
                         sletHVectorIn (rf cr x a) $ \ !rfRes ->
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
      p = sscan f (srepl 7) as
      rf :: forall f. ADReadyS f
         => f Double '[] -> f Double '[] -> f Double '[]
         -> HVectorOf (RankedOf f)
      rf _x _y z = srev @_ @f (\v -> f (sscalar 42) (sfromD (v V.! 1)))
                        doms (V.fromList [ DynamicShaped @Double @'[] z
                                         , DynamicShaped @Double @'[] z ])
                     -- not exactly the rev of f
  in fFoldS @0 p as rf (srepl 26)

testSin0revhFoldS :: Assertion
testSin0revhFoldS = do
  assertEqualUpToEpsilon 1e-10
    (sreplicate @_ @3 (sscalar $ -7.313585321642452e-2))
    (rev (fFoldSX @(AstShaped FullSpan))
         (sreplicate @_ @3 (sscalar 1.1)))

testSin0revhFold2S :: Assertion
testSin0revhFold2S = do
  assertEqualUpToEpsilon' 1e-10
    (treplicateR 3 (-7.313585321642452e-2))
    (rev' (rfromS . fFoldSX . sfromR)
          (FlipR $ treplicateR 3 1.1))

testSin0revhFold3S :: Assertion
testSin0revhFold3S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ sreplicate @_ @3 (sscalar (-7.313585321642452e-2)) ])
    (crev (\(asD :: HVector (ADVal ORArray)) ->
             fFoldSX (sfromD (asD V.! 1)))
          (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                      , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))

testSin0revhFold4S :: Assertion
testSin0revhFold4S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ srepl (-7.313585321642452e-2) ])
    (rev (\(asD :: HVector (AstRanked FullSpan)) ->
             fFoldSX (sfromD (asD V.! 1)))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))

testSin0revhFold5S :: Assertion
testSin0revhFold5S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ srepl (-7.313585321642452e-2) ])
    (rev (\(asD :: AstTensor FullSpan TKUntyped) ->
            sletHVectorIn asD (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))
