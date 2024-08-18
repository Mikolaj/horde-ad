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
    @?= "let [v12 @[Natural] @Double @[5], m13 @[Natural] @Double @[1,5]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1] in let [v17 @[Natural] @Double @[5], v18 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])] [m13, sreplicate 1.1] in rfromS (sreshape v18) + rfromS (ssum v17)"

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
    @?= "let v12 = rconst (rfromListLinear [2] [42.0,42.0]) in let [x14 @Natural @Double @[], v15 @Natural @Double @[2], v16 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h27 -> let [x39 @Natural @Double @[]] = tproject1 h27 in let [x43 @Natural @Double @[], x44 @Natural @Double @[]] = let [x40 @Natural @Double @[]] = tproject1 h27 in let [x41 @Natural @Double @[]] = tproject2 h27 in let x42 = sin x40 in [x42, x42] in [x43, x39, x44]) (\\h45 -> let [x64 @Natural @Double @[], x65 @Natural @Double @[]] = tproject1 h45 in let x70 = let [x66 @Natural @Double @[], x67 @Natural @Double @[]] = tproject1 h45 in x66 * cos (let [x68 @Natural @Double @[], x69 @Natural @Double @[]] = tproject2 h45 in x68) in [x70, x64, x70]) (\\h71 -> let [x92 @Natural @Double @[], x93 @Natural @Double @[], x94 @Natural @Double @[]] = tproject1 h71 in let h95 = [x92, x94] in [cos (let [x96 @Natural @Double @[], x97 @Natural @Double @[]] = tproject2 h71 in x96) * (let [x98 @Natural @Double @[], x99 @Natural @Double @[]] = h95 in x99 + let [x100 @Natural @Double @[], x101 @Natural @Double @[]] = h95 in x100) + x93, 0.0]) [1.1] [v12] in let v17 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in let [x22 @Natural @Double @[], v23 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h103 -> let [x117 @Natural @Double @[]] = tproject1 h103 in let [x118 @Natural @Double @[], x119 @Natural @Double @[], x120 @Natural @Double @[]] = tproject2 h103 in let h121 = [x117, x118] in [cos x119 * (let [x125 @Natural @Double @[], x126 @Natural @Double @[]] = h121 in x126 + let [x127 @Natural @Double @[], x128 @Natural @Double @[]] = h121 in x127), 0]) (\\h129 -> [(let [x155 @Natural @Double @[], x156 @Natural @Double @[], x157 @Natural @Double @[], x158 @Natural @Double @[]] = tproject1 h129 in x157 * negate (sin (let [x159 @Natural @Double @[], x160 @Natural @Double @[], x161 @Natural @Double @[], x162 @Natural @Double @[]] = tproject2 h129 in x161))) * (let [x163 @Natural @Double @[], x164 @Natural @Double @[], x165 @Natural @Double @[], x166 @Natural @Double @[]] = tproject2 h129 in x164 + let [x167 @Natural @Double @[], x168 @Natural @Double @[], x169 @Natural @Double @[], x170 @Natural @Double @[]] = tproject2 h129 in x167) + (let [x171 @Natural @Double @[], x172 @Natural @Double @[], x173 @Natural @Double @[], x174 @Natural @Double @[]] = tproject1 h129 in x172 + let [x175 @Natural @Double @[], x176 @Natural @Double @[], x177 @Natural @Double @[], x178 @Natural @Double @[]] = tproject1 h129 in x175) * cos (let [x179 @Natural @Double @[], x180 @Natural @Double @[], x181 @Natural @Double @[], x182 @Natural @Double @[]] = tproject2 h129 in x181), 0.0]) (\\h183 -> let x213 = cos (let [x207 @Natural @Double @[], x208 @Natural @Double @[], x209 @Natural @Double @[], x210 @Natural @Double @[]] = tproject2 h183 in x209) * let [x211 @Natural @Double @[], x212 @Natural @Double @[]] = tproject1 h183 in x211 in [x213, x213, negate (sin (let [x214 @Natural @Double @[], x215 @Natural @Double @[], x216 @Natural @Double @[], x217 @Natural @Double @[]] = tproject2 h183 in x216)) * ((let [x218 @Natural @Double @[], x219 @Natural @Double @[], x220 @Natural @Double @[], x221 @Natural @Double @[]] = tproject2 h183 in x219 + let [x222 @Natural @Double @[], x223 @Natural @Double @[], x224 @Natural @Double @[], x225 @Natural @Double @[]] = tproject2 h183 in x222) * let [x226 @Natural @Double @[], x227 @Natural @Double @[]] = tproject1 h183 in x226), 0]) [0] [rslice 1 2 v17, v15, v12] in x22 + v17 ! [0]"

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
    @?= "let v7 = rconst (rfromListLinear [2] [42.0,42.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h14 -> let [x15 @Natural @Double @[]] = tproject1 h14 in let [x23 @Natural @Double @[], x24 @Natural @Double @[]] = let [x20 @Natural @Double @[]] = tproject1 h14 in let [x21 @Natural @Double @[]] = tproject2 h14 in let x22 = sin x20 in [x22, x22] in [x23, x15, x24]) (\\h25 -> let [x26 @Natural @Double @[], x27 @Natural @Double @[]] = tproject1 h25 in let x40 = let [x36 @Natural @Double @[], x37 @Natural @Double @[]] = tproject1 h25 in x36 * cos (let [x38 @Natural @Double @[], x39 @Natural @Double @[]] = tproject2 h25 in x38) in [x40, x26, x40]) (\\h43 -> let [x44 @Natural @Double @[], x45 @Natural @Double @[], x46 @Natural @Double @[]] = tproject1 h43 in let h54 = [x44, x46] in [cos (let [x55 @Natural @Double @[], x56 @Natural @Double @[]] = tproject2 h43 in x55) * (let [x57 @Natural @Double @[], x58 @Natural @Double @[]] = h54 in x58 + let [x59 @Natural @Double @[], x60 @Natural @Double @[]] = h54 in x59) + x45, 0.0]) [1.1] [v7] in let [x11 @Natural @Double @[], v12 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h63 -> let [x64 @Natural @Double @[]] = tproject1 h63 in let [x65 @Natural @Double @[], x66 @Natural @Double @[], x67 @Natural @Double @[]] = tproject2 h63 in let x74 = x64 * cos x66 in [x74, x74]) (\\h75 -> let x98 = rproject (tproject1 h75) 0 * cos (rproject (tproject2 h75) 2) + (rproject (tproject1 h75) 2 * negate (sin (rproject (tproject2 h75) 2))) * rproject (tproject2 h75) 0 in [x98, x98]) (\\h99 -> let x121 = rproject (tproject1 h99) 1 + rproject (tproject1 h99) 0 in [cos (rproject (tproject2 h99) 2) * x121, 0, negate (sin (rproject (tproject2 h99) 2)) * (rproject (tproject2 h99) 0 * x121), 0]) [1.0] [rreplicate 2 0.0, v9, v7] in rappend (rreplicate 1 1.0) v12"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           ((rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "rproject ((\\h1 -> let v7 = rconst (rfromListLinear [2] [42.0,42.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h14 -> let [x15 @Natural @Double @[]] = tproject1 h14 in let [x23 @Natural @Double @[], x24 @Natural @Double @[]] = let [x20 @Natural @Double @[]] = tproject1 h14 in let [x21 @Natural @Double @[]] = tproject2 h14 in let x22 = sin x20 in [x22, x22] in [x23, x15, x24]) (\\h25 -> let [x26 @Natural @Double @[], x27 @Natural @Double @[]] = tproject1 h25 in let x40 = let [x36 @Natural @Double @[], x37 @Natural @Double @[]] = tproject1 h25 in x36 * cos (let [x38 @Natural @Double @[], x39 @Natural @Double @[]] = tproject2 h25 in x38) in [x40, x26, x40]) (\\h43 -> let [x44 @Natural @Double @[], x45 @Natural @Double @[], x46 @Natural @Double @[]] = tproject1 h43 in let h54 = [x44, x46] in [cos (let [x55 @Natural @Double @[], x56 @Natural @Double @[]] = tproject2 h43 in x55) * (let [x57 @Natural @Double @[], x58 @Natural @Double @[]] = h54 in x58 + let [x59 @Natural @Double @[], x60 @Natural @Double @[]] = h54 in x59) + x45, 0.0]) [rproject (tproject2 h1) 0] [v7] in let [x11 @Natural @Double @[], v12 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h63 -> let [x64 @Natural @Double @[]] = tproject1 h63 in let [x65 @Natural @Double @[], x66 @Natural @Double @[], x67 @Natural @Double @[]] = tproject2 h63 in let x74 = x64 * cos x66 in [x74, x74]) (\\h75 -> let x98 = rproject (tproject1 h75) 0 * cos (rproject (tproject2 h75) 2) + (rproject (tproject1 h75) 2 * negate (sin (rproject (tproject2 h75) 2))) * rproject (tproject2 h75) 0 in [x98, x98]) (\\h99 -> let x121 = rproject (tproject1 h99) 1 + rproject (tproject1 h99) 0 in [cos (rproject (tproject2 h99) 2) * x121, 0, negate (sin (rproject (tproject2 h99) 2)) * (rproject (tproject2 h99) 0 * x121), 0]) [rproject (tproject1 h1) 0] [rreplicate 2 0.0, v9, v7] in [rappend (rreplicate 1 (rproject (tproject1 h1) 0)) v12]) (ttuple ([1.0], [1.1]))) 0"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v12 = rconst (rfromListLinear [2] [5.0,7.0]) in let [x14 @Natural @Double @[], v15 @Natural @Double @[2], v16 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v17 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in let [x22 @Natural @Double @[], v23 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v17, v15, v12] in x22 + v17 ! [0]"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7])))
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v11 x12 -> let v4 = rconst (rfromListLinear [2] [5.0,7.0]) in let [x5 @Natural @Double @[], v6 @Natural @Double @[2], v7 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x12] [v4] in let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v11, v6, v4] in [x9 + v11 ! [0]]"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt @Double @1 @(AstRanked FullSpan)
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0])
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v4 x5 -> [cos x5 * (cos (sin x5 - 5.0) * v4 ! [0]) + cos x5 * v4 ! [1] + v4 ! [2]]"

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
    @?= "let v15 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in let [x17 @Natural @Double @[], v18 @Natural @Double @[2], v19 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v15] in let v20 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in let [x25 @Natural @Double @[], v26 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v20, v18, v15] in 5.0 * v26 ! [0] + 7.0 * v26 ! [1] + x25 + v20 ! [0]"

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
    @?= "let v7 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v7] in let [x14 @Natural @Double @[], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), v9, v7] in rappend (rreplicate 1 1.0) v15"

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
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
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
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
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
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
                          (dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [x13 @[Natural] @Double @[], v14 @[Natural] @Double @[0]] = dmapAccumRDer (SNat @0) (\\h22 -> let [x31 @[Natural] @Double @[]] = tproject1 h22 in let [x34 @[Natural] @Double @[]] = let [x32 @[Natural] @Double @[]] = tproject1 h22 in let [x33 @Natural @Double @[]] = tproject2 h22 in [x32] in [x34, x31]) (\\h35 -> let [x47 @[Natural] @Double @[], x48 @Natural @Double @[]] = tproject1 h35 in [let [x49 @[Natural] @Double @[], x50 @Natural @Double @[]] = tproject1 h35 in x49, x47]) (\\h52 -> let [x64 @[Natural] @Double @[], x65 @[Natural] @Double @[]] = tproject1 h52 in [0.0 + x65 + x64, 0.0]) [1.1] [rconst (rfromListLinear [0] [])] in let [x18 @[Natural] @Double @[], v19 @Natural @Double @[0]] = dmapAccumLDer (SNat @0) (\\h66 -> let [x73 @[Natural] @Double @[]] = tproject1 h66 in let [x74 @[Natural] @Double @[], x75 @Natural @Double @[]] = tproject2 h66 in [x73, 0]) (\\h77 -> [let [x88 @[Natural] @Double @[], x89 @[Natural] @Double @[], x90 @Natural @Double @[]] = tproject1 h77 in x88, 0.0]) (\\h91 -> [let [x102 @[Natural] @Double @[], x103 @Natural @Double @[]] = tproject1 h91 in x102, 0, 0]) [4.0] [v14, rconst (rfromListLinear [0] [])] in [rfromS x18]"

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
    (simplifyInlineHVector
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (sfromListLinear [1] [0.0])] in let [x11 @[Natural] @Double @[], v12 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] [v9, sconst @[1] (sfromListLinear [1] [0.0])] in [x11]"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "(\\h1 -> let [x8 @[Natural] @Double @[], v9 @[Natural] @Double @[1]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 h1) 0] [sconst @[1] (sfromListLinear [1] [0.0])] in let [x11 @[Natural] @Double @[], v12 @[Natural] @Double @[1]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (sproject (tproject1 h1) 0))] [v9, sconst @[1] (sfromListLinear [1] [0.0])] in [x11]) (ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]))"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dletHVectorInHVector (dmapAccumRDer (SNat @1) (\\h22 -> dletHVectorInHVector (tproject1 h22) (\\[x31 @Natural @Double @[]] -> dletHVectorInHVector (dletHVectorInHVector (tproject1 h22) (\\[x32 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h22) (\\[x33 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x32])))) (\\[x34 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x34, DynamicRanked x31])))) (\\h35 -> dletHVectorInHVector (tproject1 h35) (\\[x47 @Natural @Double @[], x48 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h35) (\\[x49 @Natural @Double @[], x50 @Natural @Double @[]] -> x49)), DynamicRanked x47]))) (\\h52 -> dletHVectorInHVector (tproject1 h52) (\\[x64 @Natural @Double @[], x65 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (x64 + x65), DynamicRanked 0.0]))) dmkHVector (fromList [DynamicRanked (rconstant 1.1)]) dmkHVector (fromList [DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x13 @Natural @Double @[], v14 @Natural @Double @[1]] -> dletHVectorInHVector (dmapAccumLDer (SNat @1) (\\h66 -> dletHVectorInHVector (tproject1 h66) (\\[x73 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h66) (\\[x74 @Natural @Double @[], x75 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x73, DynamicRankedDummy])))) (\\h77 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h77) (\\[x88 @Natural @Double @[], x89 @Natural @Double @[], x90 @Natural @Double @[]] -> x88)), DynamicRanked 0.0])) (\\h91 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h91) (\\[x102 @Natural @Double @[], x103 @Natural @Double @[]] -> x102)), DynamicRankedDummy, DynamicRankedDummy])) dmkHVector (fromList [DynamicRanked (rconstant 4.0)]) dmkHVector (fromList [DynamicRanked v14, DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x18 @Natural @Double @[], v19 @Natural @Double @[1]] -> dmkHVector (fromList [DynamicRanked x18])))"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [m20 @[Natural] @Double @[2,2], t21 @[Natural] @Double @[0,2,2]] = dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in let [m26 @[Natural] @Double @[2,2], t27 @Natural @Double @[0,2,2]] = dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i22] -> [i22])] [t21, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in [rfromS (ssum (ssum m26))]"

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
    (simplifyInlineHVector
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let [m13 @[Natural] @Double @[2,2], t14 @[Natural] @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))] in let [m18 @[Natural] @Double @[2,2], t19 @[Natural] @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i17] -> [i17])] [t14, stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))] in [ssum (ssum m18)]"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [m18 @Natural @Double @[2,2], t19 @Natural @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in let [m23 @Natural @Double @[2,2], t24 @Natural @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] [t19, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in [rsum (rreshape [4] m23)]"

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
    @?= "let v12 = rconst (rfromListLinear [2] [42.0,42.0]) in let [x14 @Natural @Double @[], v15 @Natural @Double @[2], v16 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v17 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in let [x22 @Natural @Double @[], v23 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v17, v15, v12] in x22 + v17 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               $ (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v7 = rconst (rfromListLinear [2] [42.0,42.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v7] in let [x11 @Natural @Double @[], v12 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, v9, v7] in rappend (rreplicate 1 1.0) v12"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v12 = rconst (rfromListLinear [2] [5.0,7.0]) in let [x14 @Natural @Double @[], v15 @Natural @Double @[2], v16 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v12] in let v17 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in let [x22 @Natural @Double @[], v23 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0] [rslice 1 2 v17, v15, v12] in x22 + v17 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v7 = rconst (rfromListLinear [2] [5.0,7.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v7] in let [x11 @Natural @Double @[], v12 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, v9, v7] in rappend (rreplicate 1 1.0) v12"

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
    @?= 8912

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v7 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in let [x8 @Natural @Double @[], v9 @Natural @Double @[2], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v7] in let [x14 @Natural @Double @[], v15 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), v9, v7] in rappend (rreplicate 1 1.0) v15"

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
    @?= "let [x6 @[Natural] @Double @[], v7 @[Natural] @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1] in let [x9 @[Natural] @Double @[], v10 @[Natural] @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v7, sreplicate 1.1] in [ssum v10 + x9]"

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
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x17 @Natural @Double @[], v18 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v13, rreplicate 11 1.1] in [rsum v18 + x17]"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in let [x17 @Natural @Double @[], v18 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [v13, rreplicate 11 1.1] in [rsum v18 + x17]"

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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [x12 @Natural @Double @[], v13 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) (\\h23 -> let [x36 @Natural @Double @[]] = tproject1 h23 in let [x41 @Natural @Double @[]] = let [x37 @Natural @Double @[]] = tproject1 h23 in let [x38 @Natural @Double @[]] = tproject2 h23 in [let [x39 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h42 -> let [x51 @Natural @Double @[]] = tproject1 h42 in let [x52 @Natural @Double @[]] = tproject2 h42 in [x51 + tan x52]) (\\h54 -> let x75 = cos (let [x73 @Natural @Double @[], x74 @Natural @Double @[]] = tproject2 h54 in x74) in [let [x76 @Natural @Double @[], x77 @Natural @Double @[]] = tproject1 h54 in x76 + let [x78 @Natural @Double @[], x79 @Natural @Double @[]] = tproject1 h54 in x79 * recip (x75 * x75)]) (\\h80 -> let x97 = cos (let [x95 @Natural @Double @[], x96 @Natural @Double @[]] = tproject2 h80 in x96) in [let [x98 @Natural @Double @[]] = tproject1 h80 in x98, recip (x97 * x97) * let [x99 @Natural @Double @[]] = tproject1 h80 in x99]) [x38] [rreplicate 22 x37] in x39] in [x41, x36]) (\\h100 -> let [x130 @Natural @Double @[], x131 @Natural @Double @[]] = tproject1 h100 in let [x145 @Natural @Double @[]] = let [x136 @Natural @Double @[], v137 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h146 -> let [x162 @Natural @Double @[]] = tproject1 h146 in let [x165 @Natural @Double @[]] = let [x163 @Natural @Double @[]] = tproject1 h146 in let [x164 @Natural @Double @[]] = tproject2 h146 in [x163 + tan x164] in [x165, x162]) (\\h166 -> let [x198 @Natural @Double @[], x199 @Natural @Double @[]] = tproject1 h166 in let x202 = cos (let [x200 @Natural @Double @[], x201 @Natural @Double @[]] = tproject2 h166 in x201) in [let [x203 @Natural @Double @[], x204 @Natural @Double @[]] = tproject1 h166 in x203 + let [x205 @Natural @Double @[], x206 @Natural @Double @[]] = tproject1 h166 in x206 * recip (x202 * x202), x198]) (\\h207 -> let [x232 @Natural @Double @[], x233 @Natural @Double @[]] = tproject1 h207 in let x236 = cos (let [x234 @Natural @Double @[], x235 @Natural @Double @[]] = tproject2 h207 in x235) in [x232 + x233, recip (x236 * x236) * x232]) [let [x132 @Natural @Double @[], x133 @Natural @Double @[]] = tproject2 h100 in x133] [rreplicate 22 (let [x134 @Natural @Double @[], x135 @Natural @Double @[]] = tproject2 h100 in x134)] in let [x144 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h237 -> let [x263 @Natural @Double @[]] = tproject1 h237 in let [x264 @Natural @Double @[], x265 @Natural @Double @[], x266 @Natural @Double @[]] = tproject2 h237 in let h267 = [x263, x264] ; x268 = cos x266 in [let [x269 @Natural @Double @[], x270 @Natural @Double @[]] = h267 in x269 + let [x271 @Natural @Double @[], x272 @Natural @Double @[]] = h267 in x272 * recip (x268 * x268)]) (\\h273 -> let x336 = cos (let [x332 @Natural @Double @[], x333 @Natural @Double @[], x334 @Natural @Double @[], x335 @Natural @Double @[]] = tproject2 h273 in x335) ; x337 = x336 * x336 ; x346 = let [x338 @Natural @Double @[], x339 @Natural @Double @[], x340 @Natural @Double @[], x341 @Natural @Double @[]] = tproject1 h273 in x341 * negate (sin (let [x342 @Natural @Double @[], x343 @Natural @Double @[], x344 @Natural @Double @[], x345 @Natural @Double @[]] = tproject2 h273 in x345)) in [let [x347 @Natural @Double @[], x348 @Natural @Double @[], x349 @Natural @Double @[], x350 @Natural @Double @[]] = tproject1 h273 in x347 + let [x351 @Natural @Double @[], x352 @Natural @Double @[], x353 @Natural @Double @[], x354 @Natural @Double @[]] = tproject1 h273 in x352 * recip x337 + ((x346 * x336 + x346 * x336) * negate (recip (x337 * x337))) * let [x355 @Natural @Double @[], x356 @Natural @Double @[], x357 @Natural @Double @[], x358 @Natural @Double @[]] = tproject2 h273 in x356]) (\\h359 -> let x409 = cos (let [x405 @Natural @Double @[], x406 @Natural @Double @[], x407 @Natural @Double @[], x408 @Natural @Double @[]] = tproject2 h359 in x408) ; x410 = x409 * x409 ; x416 = negate (recip (x410 * x410)) * (let [x411 @Natural @Double @[], x412 @Natural @Double @[], x413 @Natural @Double @[], x414 @Natural @Double @[]] = tproject2 h359 in x412 * let [x415 @Natural @Double @[]] = tproject1 h359 in x415) in [let [x417 @Natural @Double @[]] = tproject1 h359 in x417, recip x410 * let [x418 @Natural @Double @[]] = tproject1 h359 in x418, 0, negate (sin (let [x419 @Natural @Double @[], x420 @Natural @Double @[], x421 @Natural @Double @[], x422 @Natural @Double @[]] = tproject2 h359 in x422)) * (x409 * x416 + x409 * x416)]) [let [x138 @Natural @Double @[], x139 @Natural @Double @[]] = tproject1 h100 in x139] [rreplicate 22 (let [x140 @Natural @Double @[], x141 @Natural @Double @[]] = tproject1 h100 in x140), v137, rreplicate 22 (let [x142 @Natural @Double @[], x143 @Natural @Double @[]] = tproject2 h100 in x142)] in [x144] in [x145, x130]) (\\h423 -> let [x453 @Natural @Double @[], x454 @Natural @Double @[]] = tproject1 h423 in let [x465 @Natural @Double @[], x466 @Natural @Double @[]] = let [x459 @Natural @Double @[], v460 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h467 -> let [x483 @Natural @Double @[]] = tproject1 h467 in let [x486 @Natural @Double @[]] = let [x484 @Natural @Double @[]] = tproject1 h467 in let [x485 @Natural @Double @[]] = tproject2 h467 in [x484 + tan x485] in [x486, x483]) (\\h487 -> let [x519 @Natural @Double @[], x520 @Natural @Double @[]] = tproject1 h487 in let x523 = cos (let [x521 @Natural @Double @[], x522 @Natural @Double @[]] = tproject2 h487 in x522) in [let [x524 @Natural @Double @[], x525 @Natural @Double @[]] = tproject1 h487 in x524 + let [x526 @Natural @Double @[], x527 @Natural @Double @[]] = tproject1 h487 in x527 * recip (x523 * x523), x519]) (\\h528 -> let [x553 @Natural @Double @[], x554 @Natural @Double @[]] = tproject1 h528 in let x557 = cos (let [x555 @Natural @Double @[], x556 @Natural @Double @[]] = tproject2 h528 in x556) in [x553 + x554, recip (x557 * x557) * x553]) [let [x455 @Natural @Double @[], x456 @Natural @Double @[]] = tproject2 h423 in x456] [rreplicate 22 (let [x457 @Natural @Double @[], x458 @Natural @Double @[]] = tproject2 h423 in x457)] in let [x463 @Natural @Double @[], v464 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h558 -> let [x574 @Natural @Double @[]] = tproject1 h558 in let [x575 @Natural @Double @[], x576 @Natural @Double @[]] = tproject2 h558 in let x577 = cos x576 in [x574, recip (x577 * x577) * x574]) (\\h578 -> let x626 = cos (let [x623 @Natural @Double @[], x624 @Natural @Double @[], x625 @Natural @Double @[]] = tproject2 h578 in x625) ; x627 = x626 * x626 ; x634 = let [x628 @Natural @Double @[], x629 @Natural @Double @[], x630 @Natural @Double @[]] = tproject1 h578 in x630 * negate (sin (let [x631 @Natural @Double @[], x632 @Natural @Double @[], x633 @Natural @Double @[]] = tproject2 h578 in x633)) in [let [x635 @Natural @Double @[], x636 @Natural @Double @[], x637 @Natural @Double @[]] = tproject1 h578 in x635, ((x634 * x626 + x634 * x626) * negate (recip (x627 * x627))) * let [x638 @Natural @Double @[], x639 @Natural @Double @[], x640 @Natural @Double @[]] = tproject2 h578 in x638 + let [x641 @Natural @Double @[], x642 @Natural @Double @[], x643 @Natural @Double @[]] = tproject1 h578 in x641 * recip x627]) (\\h644 -> let x686 = cos (let [x683 @Natural @Double @[], x684 @Natural @Double @[], x685 @Natural @Double @[]] = tproject2 h644 in x685) ; x687 = x686 * x686 ; x693 = negate (recip (x687 * x687)) * (let [x688 @Natural @Double @[], x689 @Natural @Double @[], x690 @Natural @Double @[]] = tproject2 h644 in x688 * let [x691 @Natural @Double @[], x692 @Natural @Double @[]] = tproject1 h644 in x692) in [recip x687 * let [x694 @Natural @Double @[], x695 @Natural @Double @[]] = tproject1 h644 in x695 + let [x696 @Natural @Double @[], x697 @Natural @Double @[]] = tproject1 h644 in x696, 0, negate (sin (let [x698 @Natural @Double @[], x699 @Natural @Double @[], x700 @Natural @Double @[]] = tproject2 h644 in x700)) * (x686 * x693 + x686 * x693)]) [x453] [v460, rreplicate 22 (let [x461 @Natural @Double @[], x462 @Natural @Double @[]] = tproject2 h423 in x461)] in [rsum v464, x463] in [x465 + x454, x466]) [1.1] [rreplicate 11 1.1] in let [x17 @Natural @Double @[], v18 @Natural @Double @[11]] = dmapAccumRDer (SNat @11) (\\h701 -> let [x718 @Natural @Double @[]] = tproject1 h701 in let [x719 @Natural @Double @[], x720 @Natural @Double @[]] = tproject2 h701 in let h721 = [x719, x720] in let [x726 @Natural @Double @[], v727 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h732 -> let [x738 @Natural @Double @[]] = tproject1 h732 in let [x741 @Natural @Double @[]] = let [x739 @Natural @Double @[]] = tproject1 h732 in let [x740 @Natural @Double @[]] = tproject2 h732 in [x739 + tan x740] in [x741, x738]) (\\h742 -> let [x753 @Natural @Double @[], x754 @Natural @Double @[]] = tproject1 h742 in let x757 = cos (let [x755 @Natural @Double @[], x756 @Natural @Double @[]] = tproject2 h742 in x756) in [let [x758 @Natural @Double @[], x759 @Natural @Double @[]] = tproject1 h742 in x758 + let [x760 @Natural @Double @[], x761 @Natural @Double @[]] = tproject1 h742 in x761 * recip (x757 * x757), x753]) (\\h762 -> let [x769 @Natural @Double @[], x770 @Natural @Double @[]] = tproject1 h762 in let x773 = cos (let [x771 @Natural @Double @[], x772 @Natural @Double @[]] = tproject2 h762 in x772) in [x769 + x770, recip (x773 * x773) * x769]) [let [x722 @Natural @Double @[], x723 @Natural @Double @[]] = h721 in x723] [rreplicate 22 (let [x724 @Natural @Double @[], x725 @Natural @Double @[]] = h721 in x724)] in let [x730 @Natural @Double @[], v731 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h774 -> let [x780 @Natural @Double @[]] = tproject1 h774 in let [x781 @Natural @Double @[], x782 @Natural @Double @[]] = tproject2 h774 in let x783 = cos x782 in [x780, recip (x783 * x783) * x780]) (\\h784 -> let x810 = cos (let [x807 @Natural @Double @[], x808 @Natural @Double @[], x809 @Natural @Double @[]] = tproject2 h784 in x809) ; x811 = x810 * x810 ; x818 = let [x812 @Natural @Double @[], x813 @Natural @Double @[], x814 @Natural @Double @[]] = tproject1 h784 in x814 * negate (sin (let [x815 @Natural @Double @[], x816 @Natural @Double @[], x817 @Natural @Double @[]] = tproject2 h784 in x817)) in [let [x819 @Natural @Double @[], x820 @Natural @Double @[], x821 @Natural @Double @[]] = tproject1 h784 in x819, ((x818 * x810 + x818 * x810) * negate (recip (x811 * x811))) * let [x822 @Natural @Double @[], x823 @Natural @Double @[], x824 @Natural @Double @[]] = tproject2 h784 in x822 + let [x825 @Natural @Double @[], x826 @Natural @Double @[], x827 @Natural @Double @[]] = tproject1 h784 in x825 * recip x811]) (\\h828 -> let x851 = cos (let [x848 @Natural @Double @[], x849 @Natural @Double @[], x850 @Natural @Double @[]] = tproject2 h828 in x850) ; x852 = x851 * x851 ; x858 = negate (recip (x852 * x852)) * (let [x853 @Natural @Double @[], x854 @Natural @Double @[], x855 @Natural @Double @[]] = tproject2 h828 in x853 * let [x856 @Natural @Double @[], x857 @Natural @Double @[]] = tproject1 h828 in x857) in [recip x852 * let [x859 @Natural @Double @[], x860 @Natural @Double @[]] = tproject1 h828 in x860 + let [x861 @Natural @Double @[], x862 @Natural @Double @[]] = tproject1 h828 in x861, 0, negate (sin (let [x863 @Natural @Double @[], x864 @Natural @Double @[], x865 @Natural @Double @[]] = tproject2 h828 in x865)) * (x851 * x858 + x851 * x858)]) [x718] [v727, rreplicate 22 (let [x728 @Natural @Double @[], x729 @Natural @Double @[]] = h721 in x728)] in [rsum v731, x730]) (\\h866 -> let [x907 @Natural @Double @[], v908 @Natural @Double @[22], v909 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h941 -> let [x955 @Natural @Double @[]] = tproject1 h941 in let [x960 @Natural @Double @[], x961 @Natural @Double @[]] = let [x956 @Natural @Double @[]] = tproject1 h941 in let [x959 @Natural @Double @[]] = let [x957 @Natural @Double @[]] = tproject1 h941 in let [x958 @Natural @Double @[]] = tproject2 h941 in [x957 + tan x958] in [x959, x956] in [x960, x955, x961]) (\\h962 -> let [x987 @Natural @Double @[], x988 @Natural @Double @[]] = tproject1 h962 in let [x998 @Natural @Double @[], x999 @Natural @Double @[]] = let [x989 @Natural @Double @[], x990 @Natural @Double @[]] = tproject1 h962 in let x993 = cos (let [x991 @Natural @Double @[], x992 @Natural @Double @[]] = tproject2 h962 in x992) in [let [x994 @Natural @Double @[], x995 @Natural @Double @[]] = tproject1 h962 in x994 + let [x996 @Natural @Double @[], x997 @Natural @Double @[]] = tproject1 h962 in x997 * recip (x993 * x993), x989] in [x998, x987, x999]) (\\h1000 -> let [x1018 @Natural @Double @[], x1019 @Natural @Double @[], x1020 @Natural @Double @[]] = tproject1 h1000 in let x1023 = cos (let [x1021 @Natural @Double @[], x1022 @Natural @Double @[]] = tproject2 h1000 in x1022) in [x1019 + x1018 + x1020, recip (x1023 * x1023) * x1018]) [let [x901 @Natural @Double @[], x902 @Natural @Double @[], x903 @Natural @Double @[]] = tproject2 h866 in x903] [rreplicate 22 (let [x904 @Natural @Double @[], x905 @Natural @Double @[], x906 @Natural @Double @[]] = tproject2 h866 in x905)] in let [x916 @Natural @Double @[], v917 @Natural @Double @[22], v918 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h1024 -> let [x1038 @Natural @Double @[]] = tproject1 h1024 in let [x1043 @Natural @Double @[], x1044 @Natural @Double @[]] = let [x1039 @Natural @Double @[]] = tproject1 h1024 in let [x1040 @Natural @Double @[], x1041 @Natural @Double @[]] = tproject2 h1024 in let x1042 = cos x1041 in [x1039, recip (x1042 * x1042) * x1039] in [x1043, x1038, x1044]) (\\h1045 -> let [x1095 @Natural @Double @[], x1096 @Natural @Double @[], x1097 @Natural @Double @[]] = tproject1 h1045 in let x1101 = cos (let [x1098 @Natural @Double @[], x1099 @Natural @Double @[], x1100 @Natural @Double @[]] = tproject2 h1045 in x1100) ; x1102 = x1101 * x1101 ; x1109 = let [x1103 @Natural @Double @[], x1104 @Natural @Double @[], x1105 @Natural @Double @[]] = tproject1 h1045 in x1105 * negate (sin (let [x1106 @Natural @Double @[], x1107 @Natural @Double @[], x1108 @Natural @Double @[]] = tproject2 h1045 in x1108)) in [let [x1110 @Natural @Double @[], x1111 @Natural @Double @[], x1112 @Natural @Double @[]] = tproject1 h1045 in x1110, x1095, ((x1109 * x1101 + x1109 * x1101) * negate (recip (x1102 * x1102))) * let [x1113 @Natural @Double @[], x1114 @Natural @Double @[], x1115 @Natural @Double @[]] = tproject2 h1045 in x1113 + let [x1116 @Natural @Double @[], x1117 @Natural @Double @[], x1118 @Natural @Double @[]] = tproject1 h1045 in x1116 * recip x1102]) (\\h1119 -> let [x1164 @Natural @Double @[], x1165 @Natural @Double @[], x1166 @Natural @Double @[]] = tproject1 h1119 in let x1170 = cos (let [x1167 @Natural @Double @[], x1168 @Natural @Double @[], x1169 @Natural @Double @[]] = tproject2 h1119 in x1169) ; x1171 = x1170 * x1170 ; x1175 = negate (recip (x1171 * x1171)) * (let [x1172 @Natural @Double @[], x1173 @Natural @Double @[], x1174 @Natural @Double @[]] = tproject2 h1119 in x1172 * x1166) in [x1165 + recip x1171 * x1166 + x1164, 0.0, negate (sin (let [x1176 @Natural @Double @[], x1177 @Natural @Double @[], x1178 @Natural @Double @[]] = tproject2 h1119 in x1178)) * (x1170 * x1175 + x1170 * x1175)]) [let [x910 @Natural @Double @[], x911 @Natural @Double @[], x912 @Natural @Double @[]] = tproject2 h866 in x910] [v909, rreplicate 22 (let [x913 @Natural @Double @[], x914 @Natural @Double @[], x915 @Natural @Double @[]] = tproject2 h866 in x914)] in let [x928 @Natural @Double @[], v929 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h1179 -> let [x1194 @Natural @Double @[]] = tproject1 h1179 in let [x1195 @Natural @Double @[], x1196 @Natural @Double @[], x1197 @Natural @Double @[]] = tproject2 h1179 in let x1198 = cos x1197 in [x1194 + x1195 * recip (x1198 * x1198), x1194]) (\\h1199 -> let x1228 = cos (let [x1224 @Natural @Double @[], x1225 @Natural @Double @[], x1226 @Natural @Double @[], x1227 @Natural @Double @[]] = tproject2 h1199 in x1227) ; x1229 = x1228 * x1228 ; x1238 = let [x1230 @Natural @Double @[], x1231 @Natural @Double @[], x1232 @Natural @Double @[], x1233 @Natural @Double @[]] = tproject1 h1199 in x1233 * negate (sin (let [x1234 @Natural @Double @[], x1235 @Natural @Double @[], x1236 @Natural @Double @[], x1237 @Natural @Double @[]] = tproject2 h1199 in x1237)) in [let [x1239 @Natural @Double @[], x1240 @Natural @Double @[], x1241 @Natural @Double @[], x1242 @Natural @Double @[]] = tproject1 h1199 in x1239 + let [x1243 @Natural @Double @[], x1244 @Natural @Double @[], x1245 @Natural @Double @[], x1246 @Natural @Double @[]] = tproject1 h1199 in x1244 * recip x1229 + ((x1238 * x1228 + x1238 * x1228) * negate (recip (x1229 * x1229))) * let [x1247 @Natural @Double @[], x1248 @Natural @Double @[], x1249 @Natural @Double @[], x1250 @Natural @Double @[]] = tproject2 h1199 in x1248, let [x1251 @Natural @Double @[], x1252 @Natural @Double @[], x1253 @Natural @Double @[], x1254 @Natural @Double @[]] = tproject1 h1199 in x1251]) (\\h1255 -> let x1280 = cos (let [x1276 @Natural @Double @[], x1277 @Natural @Double @[], x1278 @Natural @Double @[], x1279 @Natural @Double @[]] = tproject2 h1255 in x1279) ; x1281 = x1280 * x1280 ; x1288 = negate (recip (x1281 * x1281)) * (let [x1282 @Natural @Double @[], x1283 @Natural @Double @[], x1284 @Natural @Double @[], x1285 @Natural @Double @[]] = tproject2 h1255 in x1283 * let [x1286 @Natural @Double @[], x1287 @Natural @Double @[]] = tproject1 h1255 in x1286) in [let [x1289 @Natural @Double @[], x1290 @Natural @Double @[]] = tproject1 h1255 in x1289 + let [x1291 @Natural @Double @[], x1292 @Natural @Double @[]] = tproject1 h1255 in x1292, recip x1281 * let [x1293 @Natural @Double @[], x1294 @Natural @Double @[]] = tproject1 h1255 in x1293, 0, negate (sin (let [x1295 @Natural @Double @[], x1296 @Natural @Double @[], x1297 @Natural @Double @[], x1298 @Natural @Double @[]] = tproject2 h1255 in x1298)) * (x1280 * x1288 + x1280 * x1288)]) [let [x919 @Natural @Double @[], x920 @Natural @Double @[], x921 @Natural @Double @[]] = tproject1 h866 in x921] [rreplicate 22 (let [x922 @Natural @Double @[], x923 @Natural @Double @[], x924 @Natural @Double @[]] = tproject1 h866 in x923), v908, rreplicate 22 (let [x925 @Natural @Double @[], x926 @Natural @Double @[], x927 @Natural @Double @[]] = tproject2 h866 in x926)] in let [x939 @Natural @Double @[], v940 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h1299 -> let [x1328 @Natural @Double @[]] = tproject1 h1299 in let [x1329 @Natural @Double @[], x1330 @Natural @Double @[], x1331 @Natural @Double @[], x1332 @Natural @Double @[], x1333 @Natural @Double @[]] = tproject2 h1299 in let x1334 = cos x1333 ; x1335 = x1334 * x1334 ; x1336 = x1330 * negate (sin x1333) in [x1328, ((x1336 * x1334 + x1336 * x1334) * negate (recip (x1335 * x1335))) * x1331 + x1328 * recip x1335]) (\\h1337 -> let x1399 = cos (let [x1393 @Natural @Double @[], x1394 @Natural @Double @[], x1395 @Natural @Double @[], x1396 @Natural @Double @[], x1397 @Natural @Double @[], x1398 @Natural @Double @[]] = tproject2 h1337 in x1398) ; x1400 = x1399 * x1399 ; x1407 = negate (sin (let [x1401 @Natural @Double @[], x1402 @Natural @Double @[], x1403 @Natural @Double @[], x1404 @Natural @Double @[], x1405 @Natural @Double @[], x1406 @Natural @Double @[]] = tproject2 h1337 in x1406)) ; x1414 = let [x1408 @Natural @Double @[], x1409 @Natural @Double @[], x1410 @Natural @Double @[], x1411 @Natural @Double @[], x1412 @Natural @Double @[], x1413 @Natural @Double @[]] = tproject2 h1337 in x1410 * x1407 ; x1415 = x1400 * x1400 ; x1416 = x1414 * x1399 + x1414 * x1399 ; x1417 = negate (recip x1415) ; x1442 = let [x1418 @Natural @Double @[], x1419 @Natural @Double @[], x1420 @Natural @Double @[], x1421 @Natural @Double @[], x1422 @Natural @Double @[], x1423 @Natural @Double @[]] = tproject1 h1337 in x1420 * x1407 + ((let [x1424 @Natural @Double @[], x1425 @Natural @Double @[], x1426 @Natural @Double @[], x1427 @Natural @Double @[], x1428 @Natural @Double @[], x1429 @Natural @Double @[]] = tproject1 h1337 in x1429 * cos (let [x1430 @Natural @Double @[], x1431 @Natural @Double @[], x1432 @Natural @Double @[], x1433 @Natural @Double @[], x1434 @Natural @Double @[], x1435 @Natural @Double @[]] = tproject2 h1337 in x1435)) * -1.0) * let [x1436 @Natural @Double @[], x1437 @Natural @Double @[], x1438 @Natural @Double @[], x1439 @Natural @Double @[], x1440 @Natural @Double @[], x1441 @Natural @Double @[]] = tproject2 h1337 in x1438 ; x1455 = let [x1443 @Natural @Double @[], x1444 @Natural @Double @[], x1445 @Natural @Double @[], x1446 @Natural @Double @[], x1447 @Natural @Double @[], x1448 @Natural @Double @[]] = tproject1 h1337 in x1448 * negate (sin (let [x1449 @Natural @Double @[], x1450 @Natural @Double @[], x1451 @Natural @Double @[], x1452 @Natural @Double @[], x1453 @Natural @Double @[], x1454 @Natural @Double @[]] = tproject2 h1337 in x1454)) ; x1456 = x1455 * x1399 + x1455 * x1399 in [let [x1457 @Natural @Double @[], x1458 @Natural @Double @[], x1459 @Natural @Double @[], x1460 @Natural @Double @[], x1461 @Natural @Double @[], x1462 @Natural @Double @[]] = tproject1 h1337 in x1457, ((x1442 * x1399 + x1455 * x1414 + x1442 * x1399 + x1455 * x1414) * x1417 + (((x1456 * x1400 + x1456 * x1400) * negate (recip (x1415 * x1415))) * -1.0) * x1416) * let [x1463 @Natural @Double @[], x1464 @Natural @Double @[], x1465 @Natural @Double @[], x1466 @Natural @Double @[], x1467 @Natural @Double @[], x1468 @Natural @Double @[]] = tproject2 h1337 in x1466 + let [x1469 @Natural @Double @[], x1470 @Natural @Double @[], x1471 @Natural @Double @[], x1472 @Natural @Double @[], x1473 @Natural @Double @[], x1474 @Natural @Double @[]] = tproject1 h1337 in x1472 * (x1416 * x1417) + let [x1475 @Natural @Double @[], x1476 @Natural @Double @[], x1477 @Natural @Double @[], x1478 @Natural @Double @[], x1479 @Natural @Double @[], x1480 @Natural @Double @[]] = tproject1 h1337 in x1475 * recip x1400 + (x1456 * negate (recip (x1400 * x1400))) * let [x1481 @Natural @Double @[], x1482 @Natural @Double @[], x1483 @Natural @Double @[], x1484 @Natural @Double @[], x1485 @Natural @Double @[], x1486 @Natural @Double @[]] = tproject2 h1337 in x1481]) (\\h1487 -> let x1538 = cos (let [x1532 @Natural @Double @[], x1533 @Natural @Double @[], x1534 @Natural @Double @[], x1535 @Natural @Double @[], x1536 @Natural @Double @[], x1537 @Natural @Double @[]] = tproject2 h1487 in x1537) ; x1539 = x1538 * x1538 ; x1546 = negate (sin (let [x1540 @Natural @Double @[], x1541 @Natural @Double @[], x1542 @Natural @Double @[], x1543 @Natural @Double @[], x1544 @Natural @Double @[], x1545 @Natural @Double @[]] = tproject2 h1487 in x1545)) ; x1553 = let [x1547 @Natural @Double @[], x1548 @Natural @Double @[], x1549 @Natural @Double @[], x1550 @Natural @Double @[], x1551 @Natural @Double @[], x1552 @Natural @Double @[]] = tproject2 h1487 in x1549 * x1546 ; x1554 = x1539 * x1539 ; x1555 = x1553 * x1538 + x1553 * x1538 ; x1556 = negate (recip x1554) ; x1565 = let [x1557 @Natural @Double @[], x1558 @Natural @Double @[], x1559 @Natural @Double @[], x1560 @Natural @Double @[], x1561 @Natural @Double @[], x1562 @Natural @Double @[]] = tproject2 h1487 in x1560 * let [x1563 @Natural @Double @[], x1564 @Natural @Double @[]] = tproject1 h1487 in x1564 ; x1566 = negate (recip (x1554 * x1554)) * (-1.0 * (x1555 * x1565)) ; x1567 = x1556 * x1565 ; x1568 = x1538 * x1567 + x1538 * x1567 ; x1577 = x1539 * x1566 + x1539 * x1566 + negate (recip (x1539 * x1539)) * (let [x1569 @Natural @Double @[], x1570 @Natural @Double @[], x1571 @Natural @Double @[], x1572 @Natural @Double @[], x1573 @Natural @Double @[], x1574 @Natural @Double @[]] = tproject2 h1487 in x1569 * let [x1575 @Natural @Double @[], x1576 @Natural @Double @[]] = tproject1 h1487 in x1576) in [recip x1539 * let [x1578 @Natural @Double @[], x1579 @Natural @Double @[]] = tproject1 h1487 in x1579 + let [x1580 @Natural @Double @[], x1581 @Natural @Double @[]] = tproject1 h1487 in x1580, 0, x1546 * x1568, (x1555 * x1556) * let [x1582 @Natural @Double @[], x1583 @Natural @Double @[]] = tproject1 h1487 in x1583, 0, negate (sin (let [x1584 @Natural @Double @[], x1585 @Natural @Double @[], x1586 @Natural @Double @[], x1587 @Natural @Double @[], x1588 @Natural @Double @[], x1589 @Natural @Double @[]] = tproject2 h1487 in x1589)) * (x1538 * x1577 + x1538 * x1577 + x1553 * x1567 + x1553 * x1567) + cos (let [x1590 @Natural @Double @[], x1591 @Natural @Double @[], x1592 @Natural @Double @[], x1593 @Natural @Double @[], x1594 @Natural @Double @[], x1595 @Natural @Double @[]] = tproject2 h1487 in x1595) * (-1.0 * (let [x1596 @Natural @Double @[], x1597 @Natural @Double @[], x1598 @Natural @Double @[], x1599 @Natural @Double @[], x1600 @Natural @Double @[], x1601 @Natural @Double @[]] = tproject2 h1487 in x1598 * x1568))]) [let [x930 @Natural @Double @[], x931 @Natural @Double @[], x932 @Natural @Double @[]] = tproject1 h866 in x930] [v929, rreplicate 22 (let [x933 @Natural @Double @[], x934 @Natural @Double @[], x935 @Natural @Double @[]] = tproject1 h866 in x934), v917, v909, rreplicate 22 (let [x936 @Natural @Double @[], x937 @Natural @Double @[], x938 @Natural @Double @[]] = tproject2 h866 in x937)] in [rsum v940, x939]) (\\h1602 -> let [x1643 @Natural @Double @[], v1644 @Natural @Double @[22], v1645 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h1670 -> let [x1684 @Natural @Double @[]] = tproject1 h1670 in let [x1689 @Natural @Double @[], x1690 @Natural @Double @[]] = let [x1685 @Natural @Double @[]] = tproject1 h1670 in let [x1688 @Natural @Double @[]] = let [x1686 @Natural @Double @[]] = tproject1 h1670 in let [x1687 @Natural @Double @[]] = tproject2 h1670 in [x1686 + tan x1687] in [x1688, x1685] in [x1689, x1684, x1690]) (\\h1691 -> let [x1716 @Natural @Double @[], x1717 @Natural @Double @[]] = tproject1 h1691 in let [x1727 @Natural @Double @[], x1728 @Natural @Double @[]] = let [x1718 @Natural @Double @[], x1719 @Natural @Double @[]] = tproject1 h1691 in let x1722 = cos (let [x1720 @Natural @Double @[], x1721 @Natural @Double @[]] = tproject2 h1691 in x1721) in [let [x1723 @Natural @Double @[], x1724 @Natural @Double @[]] = tproject1 h1691 in x1723 + let [x1725 @Natural @Double @[], x1726 @Natural @Double @[]] = tproject1 h1691 in x1726 * recip (x1722 * x1722), x1718] in [x1727, x1716, x1728]) (\\h1729 -> let [x1747 @Natural @Double @[], x1748 @Natural @Double @[], x1749 @Natural @Double @[]] = tproject1 h1729 in let x1752 = cos (let [x1750 @Natural @Double @[], x1751 @Natural @Double @[]] = tproject2 h1729 in x1751) in [x1748 + x1747 + x1749, recip (x1752 * x1752) * x1747]) [let [x1637 @Natural @Double @[], x1638 @Natural @Double @[], x1639 @Natural @Double @[]] = tproject2 h1602 in x1639] [rreplicate 22 (let [x1640 @Natural @Double @[], x1641 @Natural @Double @[], x1642 @Natural @Double @[]] = tproject2 h1602 in x1641)] in let [x1652 @Natural @Double @[], v1653 @Natural @Double @[22], v1654 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h1753 -> let [x1767 @Natural @Double @[]] = tproject1 h1753 in let [x1772 @Natural @Double @[], x1773 @Natural @Double @[]] = let [x1768 @Natural @Double @[]] = tproject1 h1753 in let [x1769 @Natural @Double @[], x1770 @Natural @Double @[]] = tproject2 h1753 in let x1771 = cos x1770 in [x1768, recip (x1771 * x1771) * x1768] in [x1772, x1767, x1773]) (\\h1774 -> let [x1824 @Natural @Double @[], x1825 @Natural @Double @[], x1826 @Natural @Double @[]] = tproject1 h1774 in let x1830 = cos (let [x1827 @Natural @Double @[], x1828 @Natural @Double @[], x1829 @Natural @Double @[]] = tproject2 h1774 in x1829) ; x1831 = x1830 * x1830 ; x1838 = let [x1832 @Natural @Double @[], x1833 @Natural @Double @[], x1834 @Natural @Double @[]] = tproject1 h1774 in x1834 * negate (sin (let [x1835 @Natural @Double @[], x1836 @Natural @Double @[], x1837 @Natural @Double @[]] = tproject2 h1774 in x1837)) in [let [x1839 @Natural @Double @[], x1840 @Natural @Double @[], x1841 @Natural @Double @[]] = tproject1 h1774 in x1839, x1824, ((x1838 * x1830 + x1838 * x1830) * negate (recip (x1831 * x1831))) * let [x1842 @Natural @Double @[], x1843 @Natural @Double @[], x1844 @Natural @Double @[]] = tproject2 h1774 in x1842 + let [x1845 @Natural @Double @[], x1846 @Natural @Double @[], x1847 @Natural @Double @[]] = tproject1 h1774 in x1845 * recip x1831]) (\\h1848 -> let [x1893 @Natural @Double @[], x1894 @Natural @Double @[], x1895 @Natural @Double @[]] = tproject1 h1848 in let x1899 = cos (let [x1896 @Natural @Double @[], x1897 @Natural @Double @[], x1898 @Natural @Double @[]] = tproject2 h1848 in x1898) ; x1900 = x1899 * x1899 ; x1904 = negate (recip (x1900 * x1900)) * (let [x1901 @Natural @Double @[], x1902 @Natural @Double @[], x1903 @Natural @Double @[]] = tproject2 h1848 in x1901 * x1895) in [x1894 + recip x1900 * x1895 + x1893, 0.0, negate (sin (let [x1905 @Natural @Double @[], x1906 @Natural @Double @[], x1907 @Natural @Double @[]] = tproject2 h1848 in x1907)) * (x1899 * x1904 + x1899 * x1904)]) [let [x1646 @Natural @Double @[], x1647 @Natural @Double @[], x1648 @Natural @Double @[]] = tproject2 h1602 in x1646] [v1645, rreplicate 22 (let [x1649 @Natural @Double @[], x1650 @Natural @Double @[], x1651 @Natural @Double @[]] = tproject2 h1602 in x1650)] in let [x1662 @Natural @Double @[], v1663 @Natural @Double @[22], v1664 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h1908 -> let [x1933 @Natural @Double @[]] = tproject1 h1908 in let [x1934 @Natural @Double @[], x1935 @Natural @Double @[], x1936 @Natural @Double @[], x1937 @Natural @Double @[]] = tproject2 h1908 in let x1938 = cos x1937 ; x1939 = x1938 * x1938 ; x1940 = negate (recip (x1939 * x1939)) * (x1935 * x1934) in [recip x1939 * x1934 + x1933, 0, negate (sin x1937) * (x1938 * x1940 + x1938 * x1940)]) (\\h1941 -> let x1998 = cos (let [x1993 @Natural @Double @[], x1994 @Natural @Double @[], x1995 @Natural @Double @[], x1996 @Natural @Double @[], x1997 @Natural @Double @[]] = tproject2 h1941 in x1997) ; x1999 = x1998 * x1998 ; x2000 = x1999 * x1999 ; x2001 = negate (recip x2000) ; x2012 = let [x2002 @Natural @Double @[], x2003 @Natural @Double @[], x2004 @Natural @Double @[], x2005 @Natural @Double @[], x2006 @Natural @Double @[]] = tproject2 h1941 in x2004 * let [x2007 @Natural @Double @[], x2008 @Natural @Double @[], x2009 @Natural @Double @[], x2010 @Natural @Double @[], x2011 @Natural @Double @[]] = tproject2 h1941 in x2008 ; x2013 = x2001 * x2012 ; x2024 = let [x2014 @Natural @Double @[], x2015 @Natural @Double @[], x2016 @Natural @Double @[], x2017 @Natural @Double @[], x2018 @Natural @Double @[]] = tproject1 h1941 in x2018 * negate (sin (let [x2019 @Natural @Double @[], x2020 @Natural @Double @[], x2021 @Natural @Double @[], x2022 @Natural @Double @[], x2023 @Natural @Double @[]] = tproject2 h1941 in x2023)) ; x2025 = x2024 * x1998 + x2024 * x1998 ; x2046 = (((x2025 * x1999 + x2025 * x1999) * negate (recip (x2000 * x2000))) * -1.0) * x2012 + (let [x2026 @Natural @Double @[], x2027 @Natural @Double @[], x2028 @Natural @Double @[], x2029 @Natural @Double @[], x2030 @Natural @Double @[]] = tproject1 h1941 in x2028 * let [x2031 @Natural @Double @[], x2032 @Natural @Double @[], x2033 @Natural @Double @[], x2034 @Natural @Double @[], x2035 @Natural @Double @[]] = tproject2 h1941 in x2032 + let [x2036 @Natural @Double @[], x2037 @Natural @Double @[], x2038 @Natural @Double @[], x2039 @Natural @Double @[], x2040 @Natural @Double @[]] = tproject1 h1941 in x2037 * let [x2041 @Natural @Double @[], x2042 @Natural @Double @[], x2043 @Natural @Double @[], x2044 @Natural @Double @[], x2045 @Natural @Double @[]] = tproject2 h1941 in x2043) * x2001 in [let [x2047 @Natural @Double @[], x2048 @Natural @Double @[], x2049 @Natural @Double @[], x2050 @Natural @Double @[], x2051 @Natural @Double @[]] = tproject1 h1941 in x2047 + (x2025 * negate (recip (x1999 * x1999))) * let [x2052 @Natural @Double @[], x2053 @Natural @Double @[], x2054 @Natural @Double @[], x2055 @Natural @Double @[], x2056 @Natural @Double @[]] = tproject2 h1941 in x2053 + let [x2057 @Natural @Double @[], x2058 @Natural @Double @[], x2059 @Natural @Double @[], x2060 @Natural @Double @[], x2061 @Natural @Double @[]] = tproject1 h1941 in x2058 * recip x1999, 0.0, ((let [x2062 @Natural @Double @[], x2063 @Natural @Double @[], x2064 @Natural @Double @[], x2065 @Natural @Double @[], x2066 @Natural @Double @[]] = tproject1 h1941 in x2066 * cos (let [x2067 @Natural @Double @[], x2068 @Natural @Double @[], x2069 @Natural @Double @[], x2070 @Natural @Double @[], x2071 @Natural @Double @[]] = tproject2 h1941 in x2071)) * -1.0) * (x1998 * x2013 + x1998 * x2013) + (x2024 * x2013 + x2046 * x1998 + x2024 * x2013 + x2046 * x1998) * negate (sin (let [x2072 @Natural @Double @[], x2073 @Natural @Double @[], x2074 @Natural @Double @[], x2075 @Natural @Double @[], x2076 @Natural @Double @[]] = tproject2 h1941 in x2076))]) (\\h2077 -> let x2123 = cos (let [x2118 @Natural @Double @[], x2119 @Natural @Double @[], x2120 @Natural @Double @[], x2121 @Natural @Double @[], x2122 @Natural @Double @[]] = tproject2 h2077 in x2122) ; x2124 = x2123 * x2123 ; x2125 = x2124 * x2124 ; x2126 = negate (recip x2125) ; x2137 = let [x2127 @Natural @Double @[], x2128 @Natural @Double @[], x2129 @Natural @Double @[], x2130 @Natural @Double @[], x2131 @Natural @Double @[]] = tproject2 h2077 in x2129 * let [x2132 @Natural @Double @[], x2133 @Natural @Double @[], x2134 @Natural @Double @[], x2135 @Natural @Double @[], x2136 @Natural @Double @[]] = tproject2 h2077 in x2133 ; x2138 = x2126 * x2137 ; x2147 = negate (sin (let [x2139 @Natural @Double @[], x2140 @Natural @Double @[], x2141 @Natural @Double @[], x2142 @Natural @Double @[], x2143 @Natural @Double @[]] = tproject2 h2077 in x2143)) * let [x2144 @Natural @Double @[], x2145 @Natural @Double @[], x2146 @Natural @Double @[]] = tproject1 h2077 in x2146 ; x2148 = x2123 * x2147 + x2123 * x2147 ; x2149 = x2126 * x2148 ; x2150 = negate (recip (x2125 * x2125)) * (-1.0 * (x2137 * x2148)) ; x2159 = x2124 * x2150 + x2124 * x2150 + negate (recip (x2124 * x2124)) * (let [x2151 @Natural @Double @[], x2152 @Natural @Double @[], x2153 @Natural @Double @[], x2154 @Natural @Double @[], x2155 @Natural @Double @[]] = tproject2 h2077 in x2152 * let [x2156 @Natural @Double @[], x2157 @Natural @Double @[], x2158 @Natural @Double @[]] = tproject1 h2077 in x2156) in [let [x2160 @Natural @Double @[], x2161 @Natural @Double @[], x2162 @Natural @Double @[]] = tproject1 h2077 in x2160, let [x2163 @Natural @Double @[], x2164 @Natural @Double @[], x2165 @Natural @Double @[], x2166 @Natural @Double @[], x2167 @Natural @Double @[]] = tproject2 h2077 in x2165 * x2149 + recip x2124 * let [x2168 @Natural @Double @[], x2169 @Natural @Double @[], x2170 @Natural @Double @[]] = tproject1 h2077 in x2168, let [x2171 @Natural @Double @[], x2172 @Natural @Double @[], x2173 @Natural @Double @[], x2174 @Natural @Double @[], x2175 @Natural @Double @[]] = tproject2 h2077 in x2172 * x2149, 0, negate (sin (let [x2176 @Natural @Double @[], x2177 @Natural @Double @[], x2178 @Natural @Double @[], x2179 @Natural @Double @[], x2180 @Natural @Double @[]] = tproject2 h2077 in x2180)) * (x2123 * x2159 + x2123 * x2159 + x2138 * x2147 + x2138 * x2147) + cos (let [x2181 @Natural @Double @[], x2182 @Natural @Double @[], x2183 @Natural @Double @[], x2184 @Natural @Double @[], x2185 @Natural @Double @[]] = tproject2 h2077 in x2185) * (-1.0 * ((x2123 * x2138 + x2123 * x2138) * let [x2186 @Natural @Double @[], x2187 @Natural @Double @[], x2188 @Natural @Double @[]] = tproject1 h2077 in x2188))]) [let [x1655 @Natural @Double @[], x1656 @Natural @Double @[]] = tproject1 h1602 in x1656] [rreplicate 22 (let [x1657 @Natural @Double @[], x1658 @Natural @Double @[]] = tproject1 h1602 in x1657), v1653, v1645, rreplicate 22 (let [x1659 @Natural @Double @[], x1660 @Natural @Double @[], x1661 @Natural @Double @[]] = tproject2 h1602 in x1660)] in let [x1668 @Natural @Double @[], v1669 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h2189 -> let [x2200 @Natural @Double @[]] = tproject1 h2189 in let [x2201 @Natural @Double @[], x2202 @Natural @Double @[], x2203 @Natural @Double @[]] = tproject2 h2189 in let x2204 = cos x2203 in [x2200 + x2201, recip (x2204 * x2204) * x2200]) (\\h2205 -> let x2230 = cos (let [x2226 @Natural @Double @[], x2227 @Natural @Double @[], x2228 @Natural @Double @[], x2229 @Natural @Double @[]] = tproject2 h2205 in x2229) ; x2231 = x2230 * x2230 ; x2240 = let [x2232 @Natural @Double @[], x2233 @Natural @Double @[], x2234 @Natural @Double @[], x2235 @Natural @Double @[]] = tproject1 h2205 in x2235 * negate (sin (let [x2236 @Natural @Double @[], x2237 @Natural @Double @[], x2238 @Natural @Double @[], x2239 @Natural @Double @[]] = tproject2 h2205 in x2239)) in [let [x2241 @Natural @Double @[], x2242 @Natural @Double @[], x2243 @Natural @Double @[], x2244 @Natural @Double @[]] = tproject1 h2205 in x2241 + let [x2245 @Natural @Double @[], x2246 @Natural @Double @[], x2247 @Natural @Double @[], x2248 @Natural @Double @[]] = tproject1 h2205 in x2246, ((x2240 * x2230 + x2240 * x2230) * negate (recip (x2231 * x2231))) * let [x2249 @Natural @Double @[], x2250 @Natural @Double @[], x2251 @Natural @Double @[], x2252 @Natural @Double @[]] = tproject2 h2205 in x2249 + let [x2253 @Natural @Double @[], x2254 @Natural @Double @[], x2255 @Natural @Double @[], x2256 @Natural @Double @[]] = tproject1 h2205 in x2253 * recip x2231]) (\\h2257 -> let x2278 = cos (let [x2274 @Natural @Double @[], x2275 @Natural @Double @[], x2276 @Natural @Double @[], x2277 @Natural @Double @[]] = tproject2 h2257 in x2277) ; x2279 = x2278 * x2278 ; x2286 = negate (recip (x2279 * x2279)) * (let [x2280 @Natural @Double @[], x2281 @Natural @Double @[], x2282 @Natural @Double @[], x2283 @Natural @Double @[]] = tproject2 h2257 in x2280 * let [x2284 @Natural @Double @[], x2285 @Natural @Double @[]] = tproject1 h2257 in x2285) in [let [x2287 @Natural @Double @[], x2288 @Natural @Double @[]] = tproject1 h2257 in x2287 + recip x2279 * let [x2289 @Natural @Double @[], x2290 @Natural @Double @[]] = tproject1 h2257 in x2290, let [x2291 @Natural @Double @[], x2292 @Natural @Double @[]] = tproject1 h2257 in x2291, 0, negate (sin (let [x2293 @Natural @Double @[], x2294 @Natural @Double @[], x2295 @Natural @Double @[], x2296 @Natural @Double @[]] = tproject2 h2257 in x2296)) * (x2278 * x2286 + x2278 * x2286)]) [0] [v1663, v1644, rreplicate 22 (let [x1665 @Natural @Double @[], x1666 @Natural @Double @[], x1667 @Natural @Double @[]] = tproject2 h1602 in x1666)] in [x1662, rsum v1669 + rsum v1664, x1668]) [1.0] [v13, rreplicate 11 1.1] in [rsum v18 + x17]"

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
      (simplifyInlineHVector
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 3_916

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
      (simplifyInlineHVector
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 49_179

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
       (simplifyInlineHVector
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 679_357

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
       (simplifyInlineHVector
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11_029_765

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
       (simplifyInlineHVector
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
       (simplifyInlineHVector
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
    (simplifyInlineHVector
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let [x11 @Natural @Double @[], v12 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h22 -> let [x31 @Natural @Double @[]] = tproject1 h22 in let [x34 @Natural @Double @[]] = let [x32 @Natural @Double @[]] = tproject1 h22 in let [x33 @Natural @Double @[]] = tproject2 h22 in dmapAccumLDer (SNat @2) (\\h35 -> let [x42 @Natural @Double @[]] = tproject1 h35 in let [x43 @Natural @Double @[]] = tproject2 h35 in [x42 + tan x43]) (\\h44 -> let x63 = cos (let [x61 @Natural @Double @[], x62 @Natural @Double @[]] = tproject2 h44 in x62) in [let [x64 @Natural @Double @[], x65 @Natural @Double @[]] = tproject1 h44 in x64 + let [x66 @Natural @Double @[], x67 @Natural @Double @[]] = tproject1 h44 in x67 * recip (x63 * x63)]) (\\h68 -> let x83 = cos (let [x81 @Natural @Double @[], x82 @Natural @Double @[]] = tproject2 h68 in x82) in [let [x84 @Natural @Double @[]] = tproject1 h68 in x84, recip (x83 * x83) * let [x85 @Natural @Double @[]] = tproject1 h68 in x85]) [x33] [rreplicate 2 x32] in [x34, x31]) (\\h86 -> let [x113 @Natural @Double @[], x114 @Natural @Double @[]] = tproject1 h86 in let [x128 @Natural @Double @[]] = let [x119 @Natural @Double @[], v120 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h129 -> let [x143 @Natural @Double @[]] = tproject1 h129 in let [x146 @Natural @Double @[]] = let [x144 @Natural @Double @[]] = tproject1 h129 in let [x145 @Natural @Double @[]] = tproject2 h129 in [x144 + tan x145] in [x146, x143]) (\\h147 -> let [x177 @Natural @Double @[], x178 @Natural @Double @[]] = tproject1 h147 in let x181 = cos (let [x179 @Natural @Double @[], x180 @Natural @Double @[]] = tproject2 h147 in x180) in [let [x182 @Natural @Double @[], x183 @Natural @Double @[]] = tproject1 h147 in x182 + let [x184 @Natural @Double @[], x185 @Natural @Double @[]] = tproject1 h147 in x185 * recip (x181 * x181), x177]) (\\h186 -> let [x209 @Natural @Double @[], x210 @Natural @Double @[]] = tproject1 h186 in let x213 = cos (let [x211 @Natural @Double @[], x212 @Natural @Double @[]] = tproject2 h186 in x212) in [x209 + x210, recip (x213 * x213) * x209]) [let [x115 @Natural @Double @[], x116 @Natural @Double @[]] = tproject2 h86 in x116] [rreplicate 2 (let [x117 @Natural @Double @[], x118 @Natural @Double @[]] = tproject2 h86 in x117)] in let [x127 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\h214 -> let [x240 @Natural @Double @[]] = tproject1 h214 in let [x241 @Natural @Double @[], x242 @Natural @Double @[], x243 @Natural @Double @[]] = tproject2 h214 in let h244 = [x240, x241] ; x245 = cos x243 in [let [x246 @Natural @Double @[], x247 @Natural @Double @[]] = h244 in x246 + let [x248 @Natural @Double @[], x249 @Natural @Double @[]] = h244 in x249 * recip (x245 * x245)]) (\\h250 -> let x313 = cos (let [x309 @Natural @Double @[], x310 @Natural @Double @[], x311 @Natural @Double @[], x312 @Natural @Double @[]] = tproject2 h250 in x312) ; x314 = x313 * x313 ; x323 = let [x315 @Natural @Double @[], x316 @Natural @Double @[], x317 @Natural @Double @[], x318 @Natural @Double @[]] = tproject1 h250 in x318 * negate (sin (let [x319 @Natural @Double @[], x320 @Natural @Double @[], x321 @Natural @Double @[], x322 @Natural @Double @[]] = tproject2 h250 in x322)) in [let [x324 @Natural @Double @[], x325 @Natural @Double @[], x326 @Natural @Double @[], x327 @Natural @Double @[]] = tproject1 h250 in x324 + let [x328 @Natural @Double @[], x329 @Natural @Double @[], x330 @Natural @Double @[], x331 @Natural @Double @[]] = tproject1 h250 in x329 * recip x314 + ((x323 * x313 + x323 * x313) * negate (recip (x314 * x314))) * let [x332 @Natural @Double @[], x333 @Natural @Double @[], x334 @Natural @Double @[], x335 @Natural @Double @[]] = tproject2 h250 in x333]) (\\h336 -> let x386 = cos (let [x382 @Natural @Double @[], x383 @Natural @Double @[], x384 @Natural @Double @[], x385 @Natural @Double @[]] = tproject2 h336 in x385) ; x387 = x386 * x386 ; x393 = negate (recip (x387 * x387)) * (let [x388 @Natural @Double @[], x389 @Natural @Double @[], x390 @Natural @Double @[], x391 @Natural @Double @[]] = tproject2 h336 in x389 * let [x392 @Natural @Double @[]] = tproject1 h336 in x392) in [let [x394 @Natural @Double @[]] = tproject1 h336 in x394, recip x387 * let [x395 @Natural @Double @[]] = tproject1 h336 in x395, 0, negate (sin (let [x396 @Natural @Double @[], x397 @Natural @Double @[], x398 @Natural @Double @[], x399 @Natural @Double @[]] = tproject2 h336 in x399)) * (x386 * x393 + x386 * x393)]) [let [x121 @Natural @Double @[], x122 @Natural @Double @[]] = tproject1 h86 in x122] [rreplicate 2 (let [x123 @Natural @Double @[], x124 @Natural @Double @[]] = tproject1 h86 in x123), v120, rreplicate 2 (let [x125 @Natural @Double @[], x126 @Natural @Double @[]] = tproject2 h86 in x125)] in [x127] in [x128, x113]) (\\h400 -> let [x427 @Natural @Double @[], x428 @Natural @Double @[]] = tproject1 h400 in let [x439 @Natural @Double @[], x440 @Natural @Double @[]] = let [x433 @Natural @Double @[], v434 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h441 -> let [x455 @Natural @Double @[]] = tproject1 h441 in let [x458 @Natural @Double @[]] = let [x456 @Natural @Double @[]] = tproject1 h441 in let [x457 @Natural @Double @[]] = tproject2 h441 in [x456 + tan x457] in [x458, x455]) (\\h459 -> let [x489 @Natural @Double @[], x490 @Natural @Double @[]] = tproject1 h459 in let x493 = cos (let [x491 @Natural @Double @[], x492 @Natural @Double @[]] = tproject2 h459 in x492) in [let [x494 @Natural @Double @[], x495 @Natural @Double @[]] = tproject1 h459 in x494 + let [x496 @Natural @Double @[], x497 @Natural @Double @[]] = tproject1 h459 in x497 * recip (x493 * x493), x489]) (\\h498 -> let [x521 @Natural @Double @[], x522 @Natural @Double @[]] = tproject1 h498 in let x525 = cos (let [x523 @Natural @Double @[], x524 @Natural @Double @[]] = tproject2 h498 in x524) in [x521 + x522, recip (x525 * x525) * x521]) [let [x429 @Natural @Double @[], x430 @Natural @Double @[]] = tproject2 h400 in x430] [rreplicate 2 (let [x431 @Natural @Double @[], x432 @Natural @Double @[]] = tproject2 h400 in x431)] in let [x437 @Natural @Double @[], v438 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h526 -> let [x542 @Natural @Double @[]] = tproject1 h526 in let [x543 @Natural @Double @[], x544 @Natural @Double @[]] = tproject2 h526 in let x545 = cos x544 in [x542, recip (x545 * x545) * x542]) (\\h546 -> let x594 = cos (let [x591 @Natural @Double @[], x592 @Natural @Double @[], x593 @Natural @Double @[]] = tproject2 h546 in x593) ; x595 = x594 * x594 ; x602 = let [x596 @Natural @Double @[], x597 @Natural @Double @[], x598 @Natural @Double @[]] = tproject1 h546 in x598 * negate (sin (let [x599 @Natural @Double @[], x600 @Natural @Double @[], x601 @Natural @Double @[]] = tproject2 h546 in x601)) in [let [x603 @Natural @Double @[], x604 @Natural @Double @[], x605 @Natural @Double @[]] = tproject1 h546 in x603, ((x602 * x594 + x602 * x594) * negate (recip (x595 * x595))) * let [x606 @Natural @Double @[], x607 @Natural @Double @[], x608 @Natural @Double @[]] = tproject2 h546 in x606 + let [x609 @Natural @Double @[], x610 @Natural @Double @[], x611 @Natural @Double @[]] = tproject1 h546 in x609 * recip x595]) (\\h612 -> let x654 = cos (let [x651 @Natural @Double @[], x652 @Natural @Double @[], x653 @Natural @Double @[]] = tproject2 h612 in x653) ; x655 = x654 * x654 ; x661 = negate (recip (x655 * x655)) * (let [x656 @Natural @Double @[], x657 @Natural @Double @[], x658 @Natural @Double @[]] = tproject2 h612 in x656 * let [x659 @Natural @Double @[], x660 @Natural @Double @[]] = tproject1 h612 in x660) in [recip x655 * let [x662 @Natural @Double @[], x663 @Natural @Double @[]] = tproject1 h612 in x663 + let [x664 @Natural @Double @[], x665 @Natural @Double @[]] = tproject1 h612 in x664, 0, negate (sin (let [x666 @Natural @Double @[], x667 @Natural @Double @[], x668 @Natural @Double @[]] = tproject2 h612 in x668)) * (x654 * x661 + x654 * x661)]) [x427] [v434, rreplicate 2 (let [x435 @Natural @Double @[], x436 @Natural @Double @[]] = tproject2 h400 in x435)] in [rsum v438, x437] in [x439 + x428, x440]) [1.1] [rreplicate 2 1.1] in let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h669 -> let [x686 @Natural @Double @[]] = tproject1 h669 in let [x687 @Natural @Double @[], x688 @Natural @Double @[]] = tproject2 h669 in let h689 = [x687, x688] in let [x694 @Natural @Double @[], v695 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h700 -> let [x706 @Natural @Double @[]] = tproject1 h700 in let [x709 @Natural @Double @[]] = let [x707 @Natural @Double @[]] = tproject1 h700 in let [x708 @Natural @Double @[]] = tproject2 h700 in [x707 + tan x708] in [x709, x706]) (\\h710 -> let [x721 @Natural @Double @[], x722 @Natural @Double @[]] = tproject1 h710 in let x725 = cos (let [x723 @Natural @Double @[], x724 @Natural @Double @[]] = tproject2 h710 in x724) in [let [x726 @Natural @Double @[], x727 @Natural @Double @[]] = tproject1 h710 in x726 + let [x728 @Natural @Double @[], x729 @Natural @Double @[]] = tproject1 h710 in x729 * recip (x725 * x725), x721]) (\\h730 -> let [x737 @Natural @Double @[], x738 @Natural @Double @[]] = tproject1 h730 in let x741 = cos (let [x739 @Natural @Double @[], x740 @Natural @Double @[]] = tproject2 h730 in x740) in [x737 + x738, recip (x741 * x741) * x737]) [let [x690 @Natural @Double @[], x691 @Natural @Double @[]] = h689 in x691] [rreplicate 2 (let [x692 @Natural @Double @[], x693 @Natural @Double @[]] = h689 in x692)] in let [x698 @Natural @Double @[], v699 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h742 -> let [x748 @Natural @Double @[]] = tproject1 h742 in let [x749 @Natural @Double @[], x750 @Natural @Double @[]] = tproject2 h742 in let x751 = cos x750 in [x748, recip (x751 * x751) * x748]) (\\h752 -> let x778 = cos (let [x775 @Natural @Double @[], x776 @Natural @Double @[], x777 @Natural @Double @[]] = tproject2 h752 in x777) ; x779 = x778 * x778 ; x786 = let [x780 @Natural @Double @[], x781 @Natural @Double @[], x782 @Natural @Double @[]] = tproject1 h752 in x782 * negate (sin (let [x783 @Natural @Double @[], x784 @Natural @Double @[], x785 @Natural @Double @[]] = tproject2 h752 in x785)) in [let [x787 @Natural @Double @[], x788 @Natural @Double @[], x789 @Natural @Double @[]] = tproject1 h752 in x787, ((x786 * x778 + x786 * x778) * negate (recip (x779 * x779))) * let [x790 @Natural @Double @[], x791 @Natural @Double @[], x792 @Natural @Double @[]] = tproject2 h752 in x790 + let [x793 @Natural @Double @[], x794 @Natural @Double @[], x795 @Natural @Double @[]] = tproject1 h752 in x793 * recip x779]) (\\h796 -> let x819 = cos (let [x816 @Natural @Double @[], x817 @Natural @Double @[], x818 @Natural @Double @[]] = tproject2 h796 in x818) ; x820 = x819 * x819 ; x826 = negate (recip (x820 * x820)) * (let [x821 @Natural @Double @[], x822 @Natural @Double @[], x823 @Natural @Double @[]] = tproject2 h796 in x821 * let [x824 @Natural @Double @[], x825 @Natural @Double @[]] = tproject1 h796 in x825) in [recip x820 * let [x827 @Natural @Double @[], x828 @Natural @Double @[]] = tproject1 h796 in x828 + let [x829 @Natural @Double @[], x830 @Natural @Double @[]] = tproject1 h796 in x829, 0, negate (sin (let [x831 @Natural @Double @[], x832 @Natural @Double @[], x833 @Natural @Double @[]] = tproject2 h796 in x833)) * (x819 * x826 + x819 * x826)]) [x686] [v695, rreplicate 2 (let [x696 @Natural @Double @[], x697 @Natural @Double @[]] = h689 in x696)] in [rsum v699, x698]) (\\h834 -> let [x875 @Natural @Double @[], v876 @Natural @Double @[2], v877 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h909 -> let [x923 @Natural @Double @[]] = tproject1 h909 in let [x928 @Natural @Double @[], x929 @Natural @Double @[]] = let [x924 @Natural @Double @[]] = tproject1 h909 in let [x927 @Natural @Double @[]] = let [x925 @Natural @Double @[]] = tproject1 h909 in let [x926 @Natural @Double @[]] = tproject2 h909 in [x925 + tan x926] in [x927, x924] in [x928, x923, x929]) (\\h930 -> let [x955 @Natural @Double @[], x956 @Natural @Double @[]] = tproject1 h930 in let [x966 @Natural @Double @[], x967 @Natural @Double @[]] = let [x957 @Natural @Double @[], x958 @Natural @Double @[]] = tproject1 h930 in let x961 = cos (let [x959 @Natural @Double @[], x960 @Natural @Double @[]] = tproject2 h930 in x960) in [let [x962 @Natural @Double @[], x963 @Natural @Double @[]] = tproject1 h930 in x962 + let [x964 @Natural @Double @[], x965 @Natural @Double @[]] = tproject1 h930 in x965 * recip (x961 * x961), x957] in [x966, x955, x967]) (\\h968 -> let [x986 @Natural @Double @[], x987 @Natural @Double @[], x988 @Natural @Double @[]] = tproject1 h968 in let x991 = cos (let [x989 @Natural @Double @[], x990 @Natural @Double @[]] = tproject2 h968 in x990) in [x987 + x986 + x988, recip (x991 * x991) * x986]) [let [x869 @Natural @Double @[], x870 @Natural @Double @[], x871 @Natural @Double @[]] = tproject2 h834 in x871] [rreplicate 2 (let [x872 @Natural @Double @[], x873 @Natural @Double @[], x874 @Natural @Double @[]] = tproject2 h834 in x873)] in let [x884 @Natural @Double @[], v885 @Natural @Double @[2], v886 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h992 -> let [x1006 @Natural @Double @[]] = tproject1 h992 in let [x1011 @Natural @Double @[], x1012 @Natural @Double @[]] = let [x1007 @Natural @Double @[]] = tproject1 h992 in let [x1008 @Natural @Double @[], x1009 @Natural @Double @[]] = tproject2 h992 in let x1010 = cos x1009 in [x1007, recip (x1010 * x1010) * x1007] in [x1011, x1006, x1012]) (\\h1013 -> let [x1063 @Natural @Double @[], x1064 @Natural @Double @[], x1065 @Natural @Double @[]] = tproject1 h1013 in let x1069 = cos (let [x1066 @Natural @Double @[], x1067 @Natural @Double @[], x1068 @Natural @Double @[]] = tproject2 h1013 in x1068) ; x1070 = x1069 * x1069 ; x1077 = let [x1071 @Natural @Double @[], x1072 @Natural @Double @[], x1073 @Natural @Double @[]] = tproject1 h1013 in x1073 * negate (sin (let [x1074 @Natural @Double @[], x1075 @Natural @Double @[], x1076 @Natural @Double @[]] = tproject2 h1013 in x1076)) in [let [x1078 @Natural @Double @[], x1079 @Natural @Double @[], x1080 @Natural @Double @[]] = tproject1 h1013 in x1078, x1063, ((x1077 * x1069 + x1077 * x1069) * negate (recip (x1070 * x1070))) * let [x1081 @Natural @Double @[], x1082 @Natural @Double @[], x1083 @Natural @Double @[]] = tproject2 h1013 in x1081 + let [x1084 @Natural @Double @[], x1085 @Natural @Double @[], x1086 @Natural @Double @[]] = tproject1 h1013 in x1084 * recip x1070]) (\\h1087 -> let [x1132 @Natural @Double @[], x1133 @Natural @Double @[], x1134 @Natural @Double @[]] = tproject1 h1087 in let x1138 = cos (let [x1135 @Natural @Double @[], x1136 @Natural @Double @[], x1137 @Natural @Double @[]] = tproject2 h1087 in x1137) ; x1139 = x1138 * x1138 ; x1143 = negate (recip (x1139 * x1139)) * (let [x1140 @Natural @Double @[], x1141 @Natural @Double @[], x1142 @Natural @Double @[]] = tproject2 h1087 in x1140 * x1134) in [x1133 + recip x1139 * x1134 + x1132, 0.0, negate (sin (let [x1144 @Natural @Double @[], x1145 @Natural @Double @[], x1146 @Natural @Double @[]] = tproject2 h1087 in x1146)) * (x1138 * x1143 + x1138 * x1143)]) [let [x878 @Natural @Double @[], x879 @Natural @Double @[], x880 @Natural @Double @[]] = tproject2 h834 in x878] [v877, rreplicate 2 (let [x881 @Natural @Double @[], x882 @Natural @Double @[], x883 @Natural @Double @[]] = tproject2 h834 in x882)] in let [x896 @Natural @Double @[], v897 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h1147 -> let [x1162 @Natural @Double @[]] = tproject1 h1147 in let [x1163 @Natural @Double @[], x1164 @Natural @Double @[], x1165 @Natural @Double @[]] = tproject2 h1147 in let x1166 = cos x1165 in [x1162 + x1163 * recip (x1166 * x1166), x1162]) (\\h1167 -> let x1196 = cos (let [x1192 @Natural @Double @[], x1193 @Natural @Double @[], x1194 @Natural @Double @[], x1195 @Natural @Double @[]] = tproject2 h1167 in x1195) ; x1197 = x1196 * x1196 ; x1206 = let [x1198 @Natural @Double @[], x1199 @Natural @Double @[], x1200 @Natural @Double @[], x1201 @Natural @Double @[]] = tproject1 h1167 in x1201 * negate (sin (let [x1202 @Natural @Double @[], x1203 @Natural @Double @[], x1204 @Natural @Double @[], x1205 @Natural @Double @[]] = tproject2 h1167 in x1205)) in [let [x1207 @Natural @Double @[], x1208 @Natural @Double @[], x1209 @Natural @Double @[], x1210 @Natural @Double @[]] = tproject1 h1167 in x1207 + let [x1211 @Natural @Double @[], x1212 @Natural @Double @[], x1213 @Natural @Double @[], x1214 @Natural @Double @[]] = tproject1 h1167 in x1212 * recip x1197 + ((x1206 * x1196 + x1206 * x1196) * negate (recip (x1197 * x1197))) * let [x1215 @Natural @Double @[], x1216 @Natural @Double @[], x1217 @Natural @Double @[], x1218 @Natural @Double @[]] = tproject2 h1167 in x1216, let [x1219 @Natural @Double @[], x1220 @Natural @Double @[], x1221 @Natural @Double @[], x1222 @Natural @Double @[]] = tproject1 h1167 in x1219]) (\\h1223 -> let x1248 = cos (let [x1244 @Natural @Double @[], x1245 @Natural @Double @[], x1246 @Natural @Double @[], x1247 @Natural @Double @[]] = tproject2 h1223 in x1247) ; x1249 = x1248 * x1248 ; x1256 = negate (recip (x1249 * x1249)) * (let [x1250 @Natural @Double @[], x1251 @Natural @Double @[], x1252 @Natural @Double @[], x1253 @Natural @Double @[]] = tproject2 h1223 in x1251 * let [x1254 @Natural @Double @[], x1255 @Natural @Double @[]] = tproject1 h1223 in x1254) in [let [x1257 @Natural @Double @[], x1258 @Natural @Double @[]] = tproject1 h1223 in x1257 + let [x1259 @Natural @Double @[], x1260 @Natural @Double @[]] = tproject1 h1223 in x1260, recip x1249 * let [x1261 @Natural @Double @[], x1262 @Natural @Double @[]] = tproject1 h1223 in x1261, 0, negate (sin (let [x1263 @Natural @Double @[], x1264 @Natural @Double @[], x1265 @Natural @Double @[], x1266 @Natural @Double @[]] = tproject2 h1223 in x1266)) * (x1248 * x1256 + x1248 * x1256)]) [let [x887 @Natural @Double @[], x888 @Natural @Double @[], x889 @Natural @Double @[]] = tproject1 h834 in x889] [rreplicate 2 (let [x890 @Natural @Double @[], x891 @Natural @Double @[], x892 @Natural @Double @[]] = tproject1 h834 in x891), v876, rreplicate 2 (let [x893 @Natural @Double @[], x894 @Natural @Double @[], x895 @Natural @Double @[]] = tproject2 h834 in x894)] in let [x907 @Natural @Double @[], v908 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h1267 -> let [x1296 @Natural @Double @[]] = tproject1 h1267 in let [x1297 @Natural @Double @[], x1298 @Natural @Double @[], x1299 @Natural @Double @[], x1300 @Natural @Double @[], x1301 @Natural @Double @[]] = tproject2 h1267 in let x1302 = cos x1301 ; x1303 = x1302 * x1302 ; x1304 = x1298 * negate (sin x1301) in [x1296, ((x1304 * x1302 + x1304 * x1302) * negate (recip (x1303 * x1303))) * x1299 + x1296 * recip x1303]) (\\h1305 -> let x1367 = cos (let [x1361 @Natural @Double @[], x1362 @Natural @Double @[], x1363 @Natural @Double @[], x1364 @Natural @Double @[], x1365 @Natural @Double @[], x1366 @Natural @Double @[]] = tproject2 h1305 in x1366) ; x1368 = x1367 * x1367 ; x1375 = negate (sin (let [x1369 @Natural @Double @[], x1370 @Natural @Double @[], x1371 @Natural @Double @[], x1372 @Natural @Double @[], x1373 @Natural @Double @[], x1374 @Natural @Double @[]] = tproject2 h1305 in x1374)) ; x1382 = let [x1376 @Natural @Double @[], x1377 @Natural @Double @[], x1378 @Natural @Double @[], x1379 @Natural @Double @[], x1380 @Natural @Double @[], x1381 @Natural @Double @[]] = tproject2 h1305 in x1378 * x1375 ; x1383 = x1368 * x1368 ; x1384 = x1382 * x1367 + x1382 * x1367 ; x1385 = negate (recip x1383) ; x1410 = let [x1386 @Natural @Double @[], x1387 @Natural @Double @[], x1388 @Natural @Double @[], x1389 @Natural @Double @[], x1390 @Natural @Double @[], x1391 @Natural @Double @[]] = tproject1 h1305 in x1388 * x1375 + ((let [x1392 @Natural @Double @[], x1393 @Natural @Double @[], x1394 @Natural @Double @[], x1395 @Natural @Double @[], x1396 @Natural @Double @[], x1397 @Natural @Double @[]] = tproject1 h1305 in x1397 * cos (let [x1398 @Natural @Double @[], x1399 @Natural @Double @[], x1400 @Natural @Double @[], x1401 @Natural @Double @[], x1402 @Natural @Double @[], x1403 @Natural @Double @[]] = tproject2 h1305 in x1403)) * -1.0) * let [x1404 @Natural @Double @[], x1405 @Natural @Double @[], x1406 @Natural @Double @[], x1407 @Natural @Double @[], x1408 @Natural @Double @[], x1409 @Natural @Double @[]] = tproject2 h1305 in x1406 ; x1423 = let [x1411 @Natural @Double @[], x1412 @Natural @Double @[], x1413 @Natural @Double @[], x1414 @Natural @Double @[], x1415 @Natural @Double @[], x1416 @Natural @Double @[]] = tproject1 h1305 in x1416 * negate (sin (let [x1417 @Natural @Double @[], x1418 @Natural @Double @[], x1419 @Natural @Double @[], x1420 @Natural @Double @[], x1421 @Natural @Double @[], x1422 @Natural @Double @[]] = tproject2 h1305 in x1422)) ; x1424 = x1423 * x1367 + x1423 * x1367 in [let [x1425 @Natural @Double @[], x1426 @Natural @Double @[], x1427 @Natural @Double @[], x1428 @Natural @Double @[], x1429 @Natural @Double @[], x1430 @Natural @Double @[]] = tproject1 h1305 in x1425, ((x1410 * x1367 + x1423 * x1382 + x1410 * x1367 + x1423 * x1382) * x1385 + (((x1424 * x1368 + x1424 * x1368) * negate (recip (x1383 * x1383))) * -1.0) * x1384) * let [x1431 @Natural @Double @[], x1432 @Natural @Double @[], x1433 @Natural @Double @[], x1434 @Natural @Double @[], x1435 @Natural @Double @[], x1436 @Natural @Double @[]] = tproject2 h1305 in x1434 + let [x1437 @Natural @Double @[], x1438 @Natural @Double @[], x1439 @Natural @Double @[], x1440 @Natural @Double @[], x1441 @Natural @Double @[], x1442 @Natural @Double @[]] = tproject1 h1305 in x1440 * (x1384 * x1385) + let [x1443 @Natural @Double @[], x1444 @Natural @Double @[], x1445 @Natural @Double @[], x1446 @Natural @Double @[], x1447 @Natural @Double @[], x1448 @Natural @Double @[]] = tproject1 h1305 in x1443 * recip x1368 + (x1424 * negate (recip (x1368 * x1368))) * let [x1449 @Natural @Double @[], x1450 @Natural @Double @[], x1451 @Natural @Double @[], x1452 @Natural @Double @[], x1453 @Natural @Double @[], x1454 @Natural @Double @[]] = tproject2 h1305 in x1449]) (\\h1455 -> let x1506 = cos (let [x1500 @Natural @Double @[], x1501 @Natural @Double @[], x1502 @Natural @Double @[], x1503 @Natural @Double @[], x1504 @Natural @Double @[], x1505 @Natural @Double @[]] = tproject2 h1455 in x1505) ; x1507 = x1506 * x1506 ; x1514 = negate (sin (let [x1508 @Natural @Double @[], x1509 @Natural @Double @[], x1510 @Natural @Double @[], x1511 @Natural @Double @[], x1512 @Natural @Double @[], x1513 @Natural @Double @[]] = tproject2 h1455 in x1513)) ; x1521 = let [x1515 @Natural @Double @[], x1516 @Natural @Double @[], x1517 @Natural @Double @[], x1518 @Natural @Double @[], x1519 @Natural @Double @[], x1520 @Natural @Double @[]] = tproject2 h1455 in x1517 * x1514 ; x1522 = x1507 * x1507 ; x1523 = x1521 * x1506 + x1521 * x1506 ; x1524 = negate (recip x1522) ; x1533 = let [x1525 @Natural @Double @[], x1526 @Natural @Double @[], x1527 @Natural @Double @[], x1528 @Natural @Double @[], x1529 @Natural @Double @[], x1530 @Natural @Double @[]] = tproject2 h1455 in x1528 * let [x1531 @Natural @Double @[], x1532 @Natural @Double @[]] = tproject1 h1455 in x1532 ; x1534 = negate (recip (x1522 * x1522)) * (-1.0 * (x1523 * x1533)) ; x1535 = x1524 * x1533 ; x1536 = x1506 * x1535 + x1506 * x1535 ; x1545 = x1507 * x1534 + x1507 * x1534 + negate (recip (x1507 * x1507)) * (let [x1537 @Natural @Double @[], x1538 @Natural @Double @[], x1539 @Natural @Double @[], x1540 @Natural @Double @[], x1541 @Natural @Double @[], x1542 @Natural @Double @[]] = tproject2 h1455 in x1537 * let [x1543 @Natural @Double @[], x1544 @Natural @Double @[]] = tproject1 h1455 in x1544) in [recip x1507 * let [x1546 @Natural @Double @[], x1547 @Natural @Double @[]] = tproject1 h1455 in x1547 + let [x1548 @Natural @Double @[], x1549 @Natural @Double @[]] = tproject1 h1455 in x1548, 0, x1514 * x1536, (x1523 * x1524) * let [x1550 @Natural @Double @[], x1551 @Natural @Double @[]] = tproject1 h1455 in x1551, 0, negate (sin (let [x1552 @Natural @Double @[], x1553 @Natural @Double @[], x1554 @Natural @Double @[], x1555 @Natural @Double @[], x1556 @Natural @Double @[], x1557 @Natural @Double @[]] = tproject2 h1455 in x1557)) * (x1506 * x1545 + x1506 * x1545 + x1521 * x1535 + x1521 * x1535) + cos (let [x1558 @Natural @Double @[], x1559 @Natural @Double @[], x1560 @Natural @Double @[], x1561 @Natural @Double @[], x1562 @Natural @Double @[], x1563 @Natural @Double @[]] = tproject2 h1455 in x1563) * (-1.0 * (let [x1564 @Natural @Double @[], x1565 @Natural @Double @[], x1566 @Natural @Double @[], x1567 @Natural @Double @[], x1568 @Natural @Double @[], x1569 @Natural @Double @[]] = tproject2 h1455 in x1566 * x1536))]) [let [x898 @Natural @Double @[], x899 @Natural @Double @[], x900 @Natural @Double @[]] = tproject1 h834 in x898] [v897, rreplicate 2 (let [x901 @Natural @Double @[], x902 @Natural @Double @[], x903 @Natural @Double @[]] = tproject1 h834 in x902), v885, v877, rreplicate 2 (let [x904 @Natural @Double @[], x905 @Natural @Double @[], x906 @Natural @Double @[]] = tproject2 h834 in x905)] in [rsum v908, x907]) (\\h1570 -> let [x1611 @Natural @Double @[], v1612 @Natural @Double @[2], v1613 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h1638 -> let [x1652 @Natural @Double @[]] = tproject1 h1638 in let [x1657 @Natural @Double @[], x1658 @Natural @Double @[]] = let [x1653 @Natural @Double @[]] = tproject1 h1638 in let [x1656 @Natural @Double @[]] = let [x1654 @Natural @Double @[]] = tproject1 h1638 in let [x1655 @Natural @Double @[]] = tproject2 h1638 in [x1654 + tan x1655] in [x1656, x1653] in [x1657, x1652, x1658]) (\\h1659 -> let [x1684 @Natural @Double @[], x1685 @Natural @Double @[]] = tproject1 h1659 in let [x1695 @Natural @Double @[], x1696 @Natural @Double @[]] = let [x1686 @Natural @Double @[], x1687 @Natural @Double @[]] = tproject1 h1659 in let x1690 = cos (let [x1688 @Natural @Double @[], x1689 @Natural @Double @[]] = tproject2 h1659 in x1689) in [let [x1691 @Natural @Double @[], x1692 @Natural @Double @[]] = tproject1 h1659 in x1691 + let [x1693 @Natural @Double @[], x1694 @Natural @Double @[]] = tproject1 h1659 in x1694 * recip (x1690 * x1690), x1686] in [x1695, x1684, x1696]) (\\h1697 -> let [x1715 @Natural @Double @[], x1716 @Natural @Double @[], x1717 @Natural @Double @[]] = tproject1 h1697 in let x1720 = cos (let [x1718 @Natural @Double @[], x1719 @Natural @Double @[]] = tproject2 h1697 in x1719) in [x1716 + x1715 + x1717, recip (x1720 * x1720) * x1715]) [let [x1605 @Natural @Double @[], x1606 @Natural @Double @[], x1607 @Natural @Double @[]] = tproject2 h1570 in x1607] [rreplicate 2 (let [x1608 @Natural @Double @[], x1609 @Natural @Double @[], x1610 @Natural @Double @[]] = tproject2 h1570 in x1609)] in let [x1620 @Natural @Double @[], v1621 @Natural @Double @[2], v1622 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h1721 -> let [x1735 @Natural @Double @[]] = tproject1 h1721 in let [x1740 @Natural @Double @[], x1741 @Natural @Double @[]] = let [x1736 @Natural @Double @[]] = tproject1 h1721 in let [x1737 @Natural @Double @[], x1738 @Natural @Double @[]] = tproject2 h1721 in let x1739 = cos x1738 in [x1736, recip (x1739 * x1739) * x1736] in [x1740, x1735, x1741]) (\\h1742 -> let [x1792 @Natural @Double @[], x1793 @Natural @Double @[], x1794 @Natural @Double @[]] = tproject1 h1742 in let x1798 = cos (let [x1795 @Natural @Double @[], x1796 @Natural @Double @[], x1797 @Natural @Double @[]] = tproject2 h1742 in x1797) ; x1799 = x1798 * x1798 ; x1806 = let [x1800 @Natural @Double @[], x1801 @Natural @Double @[], x1802 @Natural @Double @[]] = tproject1 h1742 in x1802 * negate (sin (let [x1803 @Natural @Double @[], x1804 @Natural @Double @[], x1805 @Natural @Double @[]] = tproject2 h1742 in x1805)) in [let [x1807 @Natural @Double @[], x1808 @Natural @Double @[], x1809 @Natural @Double @[]] = tproject1 h1742 in x1807, x1792, ((x1806 * x1798 + x1806 * x1798) * negate (recip (x1799 * x1799))) * let [x1810 @Natural @Double @[], x1811 @Natural @Double @[], x1812 @Natural @Double @[]] = tproject2 h1742 in x1810 + let [x1813 @Natural @Double @[], x1814 @Natural @Double @[], x1815 @Natural @Double @[]] = tproject1 h1742 in x1813 * recip x1799]) (\\h1816 -> let [x1861 @Natural @Double @[], x1862 @Natural @Double @[], x1863 @Natural @Double @[]] = tproject1 h1816 in let x1867 = cos (let [x1864 @Natural @Double @[], x1865 @Natural @Double @[], x1866 @Natural @Double @[]] = tproject2 h1816 in x1866) ; x1868 = x1867 * x1867 ; x1872 = negate (recip (x1868 * x1868)) * (let [x1869 @Natural @Double @[], x1870 @Natural @Double @[], x1871 @Natural @Double @[]] = tproject2 h1816 in x1869 * x1863) in [x1862 + recip x1868 * x1863 + x1861, 0.0, negate (sin (let [x1873 @Natural @Double @[], x1874 @Natural @Double @[], x1875 @Natural @Double @[]] = tproject2 h1816 in x1875)) * (x1867 * x1872 + x1867 * x1872)]) [let [x1614 @Natural @Double @[], x1615 @Natural @Double @[], x1616 @Natural @Double @[]] = tproject2 h1570 in x1614] [v1613, rreplicate 2 (let [x1617 @Natural @Double @[], x1618 @Natural @Double @[], x1619 @Natural @Double @[]] = tproject2 h1570 in x1618)] in let [x1630 @Natural @Double @[], v1631 @Natural @Double @[2], v1632 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h1876 -> let [x1901 @Natural @Double @[]] = tproject1 h1876 in let [x1902 @Natural @Double @[], x1903 @Natural @Double @[], x1904 @Natural @Double @[], x1905 @Natural @Double @[]] = tproject2 h1876 in let x1906 = cos x1905 ; x1907 = x1906 * x1906 ; x1908 = negate (recip (x1907 * x1907)) * (x1903 * x1902) in [recip x1907 * x1902 + x1901, 0, negate (sin x1905) * (x1906 * x1908 + x1906 * x1908)]) (\\h1909 -> let x1966 = cos (let [x1961 @Natural @Double @[], x1962 @Natural @Double @[], x1963 @Natural @Double @[], x1964 @Natural @Double @[], x1965 @Natural @Double @[]] = tproject2 h1909 in x1965) ; x1967 = x1966 * x1966 ; x1968 = x1967 * x1967 ; x1969 = negate (recip x1968) ; x1980 = let [x1970 @Natural @Double @[], x1971 @Natural @Double @[], x1972 @Natural @Double @[], x1973 @Natural @Double @[], x1974 @Natural @Double @[]] = tproject2 h1909 in x1972 * let [x1975 @Natural @Double @[], x1976 @Natural @Double @[], x1977 @Natural @Double @[], x1978 @Natural @Double @[], x1979 @Natural @Double @[]] = tproject2 h1909 in x1976 ; x1981 = x1969 * x1980 ; x1992 = let [x1982 @Natural @Double @[], x1983 @Natural @Double @[], x1984 @Natural @Double @[], x1985 @Natural @Double @[], x1986 @Natural @Double @[]] = tproject1 h1909 in x1986 * negate (sin (let [x1987 @Natural @Double @[], x1988 @Natural @Double @[], x1989 @Natural @Double @[], x1990 @Natural @Double @[], x1991 @Natural @Double @[]] = tproject2 h1909 in x1991)) ; x1993 = x1992 * x1966 + x1992 * x1966 ; x2014 = (((x1993 * x1967 + x1993 * x1967) * negate (recip (x1968 * x1968))) * -1.0) * x1980 + (let [x1994 @Natural @Double @[], x1995 @Natural @Double @[], x1996 @Natural @Double @[], x1997 @Natural @Double @[], x1998 @Natural @Double @[]] = tproject1 h1909 in x1996 * let [x1999 @Natural @Double @[], x2000 @Natural @Double @[], x2001 @Natural @Double @[], x2002 @Natural @Double @[], x2003 @Natural @Double @[]] = tproject2 h1909 in x2000 + let [x2004 @Natural @Double @[], x2005 @Natural @Double @[], x2006 @Natural @Double @[], x2007 @Natural @Double @[], x2008 @Natural @Double @[]] = tproject1 h1909 in x2005 * let [x2009 @Natural @Double @[], x2010 @Natural @Double @[], x2011 @Natural @Double @[], x2012 @Natural @Double @[], x2013 @Natural @Double @[]] = tproject2 h1909 in x2011) * x1969 in [let [x2015 @Natural @Double @[], x2016 @Natural @Double @[], x2017 @Natural @Double @[], x2018 @Natural @Double @[], x2019 @Natural @Double @[]] = tproject1 h1909 in x2015 + (x1993 * negate (recip (x1967 * x1967))) * let [x2020 @Natural @Double @[], x2021 @Natural @Double @[], x2022 @Natural @Double @[], x2023 @Natural @Double @[], x2024 @Natural @Double @[]] = tproject2 h1909 in x2021 + let [x2025 @Natural @Double @[], x2026 @Natural @Double @[], x2027 @Natural @Double @[], x2028 @Natural @Double @[], x2029 @Natural @Double @[]] = tproject1 h1909 in x2026 * recip x1967, 0.0, ((let [x2030 @Natural @Double @[], x2031 @Natural @Double @[], x2032 @Natural @Double @[], x2033 @Natural @Double @[], x2034 @Natural @Double @[]] = tproject1 h1909 in x2034 * cos (let [x2035 @Natural @Double @[], x2036 @Natural @Double @[], x2037 @Natural @Double @[], x2038 @Natural @Double @[], x2039 @Natural @Double @[]] = tproject2 h1909 in x2039)) * -1.0) * (x1966 * x1981 + x1966 * x1981) + (x1992 * x1981 + x2014 * x1966 + x1992 * x1981 + x2014 * x1966) * negate (sin (let [x2040 @Natural @Double @[], x2041 @Natural @Double @[], x2042 @Natural @Double @[], x2043 @Natural @Double @[], x2044 @Natural @Double @[]] = tproject2 h1909 in x2044))]) (\\h2045 -> let x2091 = cos (let [x2086 @Natural @Double @[], x2087 @Natural @Double @[], x2088 @Natural @Double @[], x2089 @Natural @Double @[], x2090 @Natural @Double @[]] = tproject2 h2045 in x2090) ; x2092 = x2091 * x2091 ; x2093 = x2092 * x2092 ; x2094 = negate (recip x2093) ; x2105 = let [x2095 @Natural @Double @[], x2096 @Natural @Double @[], x2097 @Natural @Double @[], x2098 @Natural @Double @[], x2099 @Natural @Double @[]] = tproject2 h2045 in x2097 * let [x2100 @Natural @Double @[], x2101 @Natural @Double @[], x2102 @Natural @Double @[], x2103 @Natural @Double @[], x2104 @Natural @Double @[]] = tproject2 h2045 in x2101 ; x2106 = x2094 * x2105 ; x2115 = negate (sin (let [x2107 @Natural @Double @[], x2108 @Natural @Double @[], x2109 @Natural @Double @[], x2110 @Natural @Double @[], x2111 @Natural @Double @[]] = tproject2 h2045 in x2111)) * let [x2112 @Natural @Double @[], x2113 @Natural @Double @[], x2114 @Natural @Double @[]] = tproject1 h2045 in x2114 ; x2116 = x2091 * x2115 + x2091 * x2115 ; x2117 = x2094 * x2116 ; x2118 = negate (recip (x2093 * x2093)) * (-1.0 * (x2105 * x2116)) ; x2127 = x2092 * x2118 + x2092 * x2118 + negate (recip (x2092 * x2092)) * (let [x2119 @Natural @Double @[], x2120 @Natural @Double @[], x2121 @Natural @Double @[], x2122 @Natural @Double @[], x2123 @Natural @Double @[]] = tproject2 h2045 in x2120 * let [x2124 @Natural @Double @[], x2125 @Natural @Double @[], x2126 @Natural @Double @[]] = tproject1 h2045 in x2124) in [let [x2128 @Natural @Double @[], x2129 @Natural @Double @[], x2130 @Natural @Double @[]] = tproject1 h2045 in x2128, let [x2131 @Natural @Double @[], x2132 @Natural @Double @[], x2133 @Natural @Double @[], x2134 @Natural @Double @[], x2135 @Natural @Double @[]] = tproject2 h2045 in x2133 * x2117 + recip x2092 * let [x2136 @Natural @Double @[], x2137 @Natural @Double @[], x2138 @Natural @Double @[]] = tproject1 h2045 in x2136, let [x2139 @Natural @Double @[], x2140 @Natural @Double @[], x2141 @Natural @Double @[], x2142 @Natural @Double @[], x2143 @Natural @Double @[]] = tproject2 h2045 in x2140 * x2117, 0, negate (sin (let [x2144 @Natural @Double @[], x2145 @Natural @Double @[], x2146 @Natural @Double @[], x2147 @Natural @Double @[], x2148 @Natural @Double @[]] = tproject2 h2045 in x2148)) * (x2091 * x2127 + x2091 * x2127 + x2106 * x2115 + x2106 * x2115) + cos (let [x2149 @Natural @Double @[], x2150 @Natural @Double @[], x2151 @Natural @Double @[], x2152 @Natural @Double @[], x2153 @Natural @Double @[]] = tproject2 h2045 in x2153) * (-1.0 * ((x2091 * x2106 + x2091 * x2106) * let [x2154 @Natural @Double @[], x2155 @Natural @Double @[], x2156 @Natural @Double @[]] = tproject1 h2045 in x2156))]) [let [x1623 @Natural @Double @[], x1624 @Natural @Double @[]] = tproject1 h1570 in x1624] [rreplicate 2 (let [x1625 @Natural @Double @[], x1626 @Natural @Double @[]] = tproject1 h1570 in x1625), v1621, v1613, rreplicate 2 (let [x1627 @Natural @Double @[], x1628 @Natural @Double @[], x1629 @Natural @Double @[]] = tproject2 h1570 in x1628)] in let [x1636 @Natural @Double @[], v1637 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h2157 -> let [x2168 @Natural @Double @[]] = tproject1 h2157 in let [x2169 @Natural @Double @[], x2170 @Natural @Double @[], x2171 @Natural @Double @[]] = tproject2 h2157 in let x2172 = cos x2171 in [x2168 + x2169, recip (x2172 * x2172) * x2168]) (\\h2173 -> let x2198 = cos (let [x2194 @Natural @Double @[], x2195 @Natural @Double @[], x2196 @Natural @Double @[], x2197 @Natural @Double @[]] = tproject2 h2173 in x2197) ; x2199 = x2198 * x2198 ; x2208 = let [x2200 @Natural @Double @[], x2201 @Natural @Double @[], x2202 @Natural @Double @[], x2203 @Natural @Double @[]] = tproject1 h2173 in x2203 * negate (sin (let [x2204 @Natural @Double @[], x2205 @Natural @Double @[], x2206 @Natural @Double @[], x2207 @Natural @Double @[]] = tproject2 h2173 in x2207)) in [let [x2209 @Natural @Double @[], x2210 @Natural @Double @[], x2211 @Natural @Double @[], x2212 @Natural @Double @[]] = tproject1 h2173 in x2209 + let [x2213 @Natural @Double @[], x2214 @Natural @Double @[], x2215 @Natural @Double @[], x2216 @Natural @Double @[]] = tproject1 h2173 in x2214, ((x2208 * x2198 + x2208 * x2198) * negate (recip (x2199 * x2199))) * let [x2217 @Natural @Double @[], x2218 @Natural @Double @[], x2219 @Natural @Double @[], x2220 @Natural @Double @[]] = tproject2 h2173 in x2217 + let [x2221 @Natural @Double @[], x2222 @Natural @Double @[], x2223 @Natural @Double @[], x2224 @Natural @Double @[]] = tproject1 h2173 in x2221 * recip x2199]) (\\h2225 -> let x2246 = cos (let [x2242 @Natural @Double @[], x2243 @Natural @Double @[], x2244 @Natural @Double @[], x2245 @Natural @Double @[]] = tproject2 h2225 in x2245) ; x2247 = x2246 * x2246 ; x2254 = negate (recip (x2247 * x2247)) * (let [x2248 @Natural @Double @[], x2249 @Natural @Double @[], x2250 @Natural @Double @[], x2251 @Natural @Double @[]] = tproject2 h2225 in x2248 * let [x2252 @Natural @Double @[], x2253 @Natural @Double @[]] = tproject1 h2225 in x2253) in [let [x2255 @Natural @Double @[], x2256 @Natural @Double @[]] = tproject1 h2225 in x2255 + recip x2247 * let [x2257 @Natural @Double @[], x2258 @Natural @Double @[]] = tproject1 h2225 in x2258, let [x2259 @Natural @Double @[], x2260 @Natural @Double @[]] = tproject1 h2225 in x2259, 0, negate (sin (let [x2261 @Natural @Double @[], x2262 @Natural @Double @[], x2263 @Natural @Double @[], x2264 @Natural @Double @[]] = tproject2 h2225 in x2264)) * (x2246 * x2254 + x2246 * x2254)]) [0] [v1631, v1612, rreplicate 2 (let [x1633 @Natural @Double @[], x1634 @Natural @Double @[], x1635 @Natural @Double @[]] = tproject2 h1570 in x1634)] in [x1630, rsum v1637 + rsum v1632, x1636]) [1.0] [v12, rreplicate 2 1.1] in [rsum v17 + x16]"

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
       (simplifyInlineHVector
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11024274

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
    @?= 124644

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
    (rev @_ @_ @(AstShaped FullSpan)
         (\(asD :: AstTensor FullSpan TKUntyped) ->
            sletHVectorIn asD (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))
