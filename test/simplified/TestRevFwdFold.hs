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
import HordeAd.Core.AstFreshId (rankedHVector, resetVarCounter)
import HordeAd.Core.TensorAst
import HordeAd.Core.TensorConcrete ()
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
-- TODO: see instance AdaptableHVector (AstRanked s) (AstTensor AstMethodLet s TKUntyped):  , testCase "4Sin0revhFold5S" testSin0revhFold5S
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
    @?= "let x16 = sin 2.2 ; x20 = 1.1 * x16 ; x27 = recip (3.3 * 3.3 + x20 * x20) ; x31 = sin 2.2 ; x39 = 3.3 * 1.0 ; x43 = (negate 3.3 * x27) * 1.0 in x16 * x43 + x31 * x39"

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
-- TODO: doesn't agree any more due to unsimplified projections:
--    @?= "1.0 * cos (1.0 * cos 1.1)"  -- agrees with the rrev1 version above
    @?= "let h11 = ttuple ([1.0], [1.0 * cos 1.1]) in rproject (tproject1 h11) 0 * cos (rproject (tproject2 h11) 0)"

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
                        x0 (srepl @'[1] 42)
            in rfromS . f . sfromR)) 1.1)

testSin0Fold2S :: Assertion
testSin0Fold2S = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sfold (\x _a -> sin x)
                        x0 (srepl @'[5] @Double 42)
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
    @?= "let h16 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])] [let [v13 @[Natural] @Double @[5], m14 @[Natural] @Double @[1,5]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1] in m14, sreplicate 1.1] in rfromS (sreshape (let [v17 @[Natural] @Double @[5], v18 @[Natural] @Double @[1]] = h16 in v18)) + rfromS (ssum (let [v19 @[Natural] @Double @[5], v20 @[Natural] @Double @[1]] = h16 in v19))"

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
    @?= "let h11 = [rconst (rfromListLinear [2] [42.0,42.0])] ; v14 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h15 = [0, rslice 1 2 v14] in let [x25 @Natural @Double @[], v26 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h28 -> let [x49 @Natural @Double @[]] = tproject1 h28 in let [x50 @Natural @Double @[], x51 @Natural @Double @[], x52 @Natural @Double @[]] = tproject2 h28 in let h53 = [x49, x50] in [cos x51 * (let [x57 @Natural @Double @[], x58 @Natural @Double @[]] = h53 in x58 + let [x59 @Natural @Double @[], x60 @Natural @Double @[]] = h53 in x59), 0]) (\\h61 -> let h93 = [let [x85 @Natural @Double @[], x86 @Natural @Double @[], x87 @Natural @Double @[], x88 @Natural @Double @[]] = tproject2 h61 in x85, let [x89 @Natural @Double @[], x90 @Natural @Double @[], x91 @Natural @Double @[], x92 @Natural @Double @[]] = tproject2 h61 in x90] ; h102 = [let [x94 @Natural @Double @[], x95 @Natural @Double @[], x96 @Natural @Double @[], x97 @Natural @Double @[]] = tproject2 h61 in x96, let [x98 @Natural @Double @[], x99 @Natural @Double @[], x100 @Natural @Double @[], x101 @Natural @Double @[]] = tproject2 h61 in x101] in [(let [x103 @Natural @Double @[], x104 @Natural @Double @[], x105 @Natural @Double @[], x106 @Natural @Double @[]] = tproject1 h61 in x105 * negate (sin (let [x107 @Natural @Double @[], x108 @Natural @Double @[]] = h102 in x107))) * (let [x109 @Natural @Double @[], x110 @Natural @Double @[]] = h93 in x110 + let [x111 @Natural @Double @[], x112 @Natural @Double @[]] = h93 in x111) + (let [x113 @Natural @Double @[], x114 @Natural @Double @[], x115 @Natural @Double @[], x116 @Natural @Double @[]] = tproject1 h61 in x114 + let [x117 @Natural @Double @[], x118 @Natural @Double @[], x119 @Natural @Double @[], x120 @Natural @Double @[]] = tproject1 h61 in x117) * cos (let [x121 @Natural @Double @[], x122 @Natural @Double @[]] = h102 in x121), 0.0]) (\\h123 -> let h153 = [let [x145 @Natural @Double @[], x146 @Natural @Double @[], x147 @Natural @Double @[], x148 @Natural @Double @[]] = tproject2 h123 in x145, let [x149 @Natural @Double @[], x150 @Natural @Double @[], x151 @Natural @Double @[], x152 @Natural @Double @[]] = tproject2 h123 in x150] ; h162 = [let [x154 @Natural @Double @[], x155 @Natural @Double @[], x156 @Natural @Double @[], x157 @Natural @Double @[]] = tproject2 h123 in x156, let [x158 @Natural @Double @[], x159 @Natural @Double @[], x160 @Natural @Double @[], x161 @Natural @Double @[]] = tproject2 h123 in x161] ; x167 = cos (let [x163 @Natural @Double @[], x164 @Natural @Double @[]] = h162 in x163) * let [x165 @Natural @Double @[], x166 @Natural @Double @[]] = tproject1 h123 in x165 in [x167, x167, negate (sin (let [x168 @Natural @Double @[], x169 @Natural @Double @[]] = h162 in x168)) * ((let [x170 @Natural @Double @[], x171 @Natural @Double @[]] = h153 in x171 + let [x172 @Natural @Double @[], x173 @Natural @Double @[]] = h153 in x172) * let [x174 @Natural @Double @[], x175 @Natural @Double @[]] = tproject1 h123 in x174), 0]) [let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = h15 in x16] [let [x18 @Natural @Double @[], v19 @Natural @Double @[2]] = h15 in v19, let [x20 @Natural @Double @[], v21 @Natural @Double @[2], v22 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h176 -> let [x188 @Natural @Double @[]] = tproject1 h176 in let [x192 @Natural @Double @[], x193 @Natural @Double @[]] = let [x189 @Natural @Double @[]] = tproject1 h176 in let [x190 @Natural @Double @[]] = tproject2 h176 in let x191 = sin x189 in [x191, x191] in [x192, x188, x193]) (\\h194 -> let [x213 @Natural @Double @[], x214 @Natural @Double @[]] = tproject1 h194 in let x219 = let [x215 @Natural @Double @[], x216 @Natural @Double @[]] = tproject1 h194 in x215 * cos (let [x217 @Natural @Double @[], x218 @Natural @Double @[]] = tproject2 h194 in x217) in [x219, x213, x219]) (\\h220 -> let [x234 @Natural @Double @[], x235 @Natural @Double @[], x236 @Natural @Double @[]] = tproject1 h220 in let h237 = [x234, x236] in [cos (let [x238 @Natural @Double @[], x239 @Natural @Double @[]] = tproject2 h220 in x238) * (let [x240 @Natural @Double @[], x241 @Natural @Double @[]] = h237 in x241 + let [x242 @Natural @Double @[], x243 @Natural @Double @[]] = h237 in x242) + x235, 0.0]) [1.1] h11 in v21, let [v23 @Natural @Double @[2]] = h11 in v23] in x25 + v14 ! [0]"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v8 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v8 ! [0]) + cos 1.1 * v8 ! [1] + v8 ! [2]"

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
    @?= "let h11 = [rconst (rfromListLinear [2] [5.0,7.0])] ; v14 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h15 = [0, rslice 1 2 v14] in let [x25 @Natural @Double @[], v26 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = h15 in x16] [let [x18 @Natural @Double @[], v19 @Natural @Double @[2]] = h15 in v19, let [x20 @Natural @Double @[], v21 @Natural @Double @[2], v22 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h11 in v21, let [v23 @Natural @Double @[2]] = h11 in v23] in x25 + v14 ! [0]"

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
    @?= "\\v7 x10 -> let h5 = [rconst (rfromListLinear [2] [5.0,7.0])] ; h8 = [0, rslice 1 2 v7] in [rproject (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [rproject h8 0] [rproject h8 1, rproject (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x10] h5) 1, rproject h5 0]) 0 + v7 ! [0]]"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0])
                 (rscalar 1.1)
  printArtifactPretty @(TKR Double 1) IM.empty (simplifyArtifact art)
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
    @?= "let h14 = [rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0])] ; v17 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h18 = [0, rslice 1 2 v17] ; h27 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x19 @Natural @Double @[], v20 @Natural @Double @[2]] = h18 in x19] [let [x21 @Natural @Double @[], v22 @Natural @Double @[2]] = h18 in v22, let [x23 @Natural @Double @[], v24 @Natural @Double @[2], v25 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h14 in v24, let [v26 @Natural @Double @[2]] = h14 in v26] ; v30 = let [x28 @Natural @Double @[], v29 @Natural @Double @[2]] = h27 in v29 in 5.0 * v30 ! [0] + 7.0 * v30 ! [1] + let [x31 @Natural @Double @[], v32 @Natural @Double @[2]] = h27 in x31 + v17 ! [0]"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v12 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; x13 = v12 ! [1] ; x14 = v12 ! [0] ; x15 = cos (sin 1.1 - 1.1 * 5.0) * x14 in cos 1.1 * x15 + 5.0 * (-1.0 * x15) + 7.0 * (-1.0 * x14) + cos 1.1 * x13 + 5.0 * (-1.0 * x13) + v12 ! [2]"

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
            , LetTensor ranked (ShapedOf ranked) )
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
      (unHVectorPseudoTensor $ dmapAccumL Proxy
         snat
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped eShs)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> HVectorOf f
              g acc e =
               unHVectorPseudoTensor
               $ tlet @_ @_ @_ @TKUntyped
                  (f (rfromD $ acc V.! 0) e)
                  (\res -> HVectorPseudoTensor $ dmkHVector
                           $ V.fromList
                               [ DynamicRanked @rn @n @f res
                               , DynamicRanked @rn @n @f res ])
          in g)
         (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked acc0)
         (HVectorPseudoTensor $ dmkHVector es))
      (\res -> rappend (rfromList [acc0]) (rfromD $ res V.! 1))

sscanZip :: forall rn sh k ranked shaped.
            ( GoodScalar rn, KnownShS sh, KnownNat k, ShapedTensor shaped
            , LetTensor ranked shaped
            , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
       => (forall f. ADReadyS f
           => f rn sh -> HVector (RankedOf f) -> f rn sh)
       -> VoidHVector
       -> shaped rn sh
       -> HVector ranked
       -> shaped rn (1 + k ': sh)
sscanZip f eShs acc0 es =
  sletHVectorIn
    (unHVectorPseudoTensor $ dmapAccumL Proxy
       (SNat @k)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped eShs)
       (let g :: forall f. ADReady f
              => HVector f -> HVector f -> HVectorOf f
            g acc e =
             unHVectorPseudoTensor
             $ tlet @_ @_ @_ @TKUntyped
                (f (sfromD $ acc V.! 0) e)
                (\res -> HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res
                             , DynamicShaped @rn @sh @f res ])
        in g)
       (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped acc0)
       (HVectorPseudoTensor $ dmkHVector es))
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[7]
              f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0))
                       $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])) $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = sletHVectorIn
                      (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD0RC :: Assertion
testSin0rmapAccumRD0RC = do
  assertEqualUpToEpsilon 1e-10
    1
    (crev (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x
                                        , DynamicRanked $ sin x ])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped x0, DynamicShaped x0])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD01SN :: Assertion
testSin0rmapAccumRD01SN = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[] (srepl 3)
                                      , DynamicShaped x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN2 :: Assertion
testSin0rmapAccumRD01SN2 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN3 :: Assertion
testSin0rmapAccumRD01SN3 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1, 3]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[2]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[1, 2] (srepl 0))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN4 :: Assertion
testSin0rmapAccumRD01SN4 = do
  assertEqualUpToEpsilon' 1e-10
    0.4535961214255773
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1, 3]
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[4, 3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped $ x0 / (srepl 1 + sfromIntegral (sconstant (sfromR j)))
                                      , DynamicShaped $ sreplicate @_ @3 x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
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
                      $ unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[6] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sreplicate @_ @3 (sfromIntegral (sconstant (sfromR j))))
                                      , DynamicShaped
                                        $ sreplicate @_ @6 (sfromIntegral (sconstant (sfromR i)))
                                          - sflatten (sappend x0 x0) ] )
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromR x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a = dmkHVector xh
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromD (x0 V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) [] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (let [x16 @[Natural] @Double @[], v17 @Natural @Double @[0]] = dmapAccumLDer (SNat @0) (\\h18 -> let [x30 @[Natural] @Double @[]] = tproject1 h18 in let [x31 @[Natural] @Double @[], x32 @Natural @Double @[]] = tproject2 h18 in [x30, 0]) (\\h34 -> [let [x44 @[Natural] @Double @[], x45 @[Natural] @Double @[], x46 @Natural @Double @[]] = tproject1 h34 in x44, 0.0]) (\\h47 -> [let [x57 @[Natural] @Double @[], x58 @Natural @Double @[]] = tproject1 h47 in x57, 0, 0]) [4.0] [let [x13 @[Natural] @Double @[], v14 @[Natural] @Double @[0]] = dmapAccumRDer (SNat @0) (\\h59 -> let [x68 @[Natural] @Double @[]] = tproject1 h59 in let [x71 @[Natural] @Double @[]] = let [x69 @[Natural] @Double @[]] = tproject1 h59 in let [x70 @Natural @Double @[]] = tproject2 h59 in [x69] in [x71, x68]) (\\h72 -> let [x84 @[Natural] @Double @[], x85 @Natural @Double @[]] = tproject1 h72 in [let [x86 @[Natural] @Double @[], x87 @Natural @Double @[]] = tproject1 h72 in x86, x84]) (\\h89 -> let [x96 @[Natural] @Double @[], x97 @[Natural] @Double @[]] = tproject1 h89 in [0.0 + x97 + x96, 0.0]) [1.1] [rconst (rfromListLinear [0] [])] in v14, rconst (rfromListLinear [0] [])] in x16)]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let h1 = ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]) in [sproject (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (sproject (tproject1 h1) 0))] [sproject (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 h1) 0] [sconst @[1] (sfromListLinear [1] [0.0])]) 1, sconst @[1] (sfromListLinear [1] [0.0])]) 0]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [1]) [0] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorSimple
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rletHVectorIn (dmapAccumLDer (SNat @1) (\\h18 -> dletHVectorInHVector (tproject1 h18) (\\[x30 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h18) (\\[x31 @Natural @Double @[], x32 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x30, DynamicRankedDummy])))) (\\h34 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h34) (\\[x44 @Natural @Double @[], x45 @Natural @Double @[], x46 @Natural @Double @[]] -> x44)), DynamicRanked 0.0])) (\\h47 -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h47) (\\[x57 @Natural @Double @[], x58 @Natural @Double @[]] -> x57)), DynamicRankedDummy, DynamicRankedDummy])) dmkHVector (fromList [DynamicRanked (rconstant 4.0)]) dmkHVector (fromList [DynamicRanked (rletHVectorIn (dmapAccumRDer (SNat @1) (\\h59 -> dletHVectorInHVector (tproject1 h59) (\\[x68 @Natural @Double @[]] -> dletHVectorInHVector (dletHVectorInHVector (tproject1 h59) (\\[x69 @Natural @Double @[]] -> dletHVectorInHVector (tproject2 h59) (\\[x70 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x69])))) (\\[x71 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x71, DynamicRanked x68])))) (\\h72 -> dletHVectorInHVector (tproject1 h72) (\\[x84 @Natural @Double @[], x85 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (rletHVectorIn (tproject1 h72) (\\[x86 @Natural @Double @[], x87 @Natural @Double @[]] -> x86)), DynamicRanked x84]))) (\\h89 -> dletHVectorInHVector (tproject1 h89) (\\[x96 @Natural @Double @[], x97 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (x96 + x97), DynamicRanked 0.0]))) dmkHVector (fromList [DynamicRanked (rconstant 1.1)]) dmkHVector (fromList [DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x13 @Natural @Double @[], v14 @Natural @Double @[1]] -> v14)), DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])) (\\[x16 @Natural @Double @[], v17 @Natural @Double @[1]] -> x16))])"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (x0 V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [0]) [] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (let [m25 @[Natural] @Double @[2,2], t26 @Natural @Double @[0,2,2]] = dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i19] -> [i19])] [let [m22 @[Natural] @Double @[2,2], t23 @[Natural] @Double @[0,2,2]] = dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in t23, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))] in m25)))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \j ->
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (x0 V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ]))))
                        $ \ !d -> sfromD $ d V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = srev f (V.singleton (voidFromShS @Double @'[]))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let h1 = ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]) in [ssum (ssum (sproject (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sproject (tproject1 h1) 0) (\\[i15] -> [i15])] [sproject (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate (sproject (tproject2 h1) 0)) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]) 1, stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]) 0))]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> HVectorOf g
                               h xh _a = dmkHVector xh
                           in h)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicRanked @Double @0
                               $ rfromIntegral (rconstant (i + j))
                                 + rfromD (x0 V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.Internal.rfromListPrimLinear (fromList [1]) [0] ]))))
                        $ \ !d -> rfromD $ d V.! 0
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g = rrev f (V.singleton (voidFromSh @Double ZSR))
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (let [m22 @Natural @Double @[2,2], t23 @Natural @Double @[1,2,2]] = dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] [let [m19 @Natural @Double @[2,2], t20 @Natural @Double @[1,2,2]] = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in t20, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))] in rgather [4] m22 (\\[i24] -> [remF (quotF i24 2) 2, remF i24 2]))]"

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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sfromIntegral (sconstant (sfromR j))) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sconstant (sfromR j))) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
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
                       (unHVectorPseudoTensor $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> HVectorOf (RankedOf g)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in dmkHVector
                                   $ V.fromList [ DynamicShaped x ]
                           in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])))
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN54 :: Assertion
testSin0rmapAccumRD01SN54 = do
  assertEqualUpToEpsilon' 1e-10
    1.538239371140263
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5, 3]
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0)))
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
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
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
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
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
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
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[2] knownShS [0.4989557335681351,1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[5] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.Internal.sfromListPrimLinear @_ @'[1] knownShS [1.1])
    (cfwd (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[1]
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[1] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN6 :: Assertion
testSin0rmapAccumRD01SN6 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReadyS f => f Double '[] -> HVector (RankedOf f)
               f x0 = dunHVector $ unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in HVectorPseudoTensor . f) (sscalar 1.1))

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReadyS f
                 => f Double '[] -> HVectorOf (RankedOf f)
               f x0 = unHVectorPseudoTensor
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
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
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in HVectorPseudoTensor . f @(ADVal OSArray)) (sscalar 1.1))

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
               $ dunHVector $ unHVectorPseudoTensor
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
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
                      (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5
                                      (rreplicate0N [1,1,1] 2 * a0)))
                      (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0))
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
    @?= "let h11 = [rconst (rfromListLinear [2] [42.0,42.0])] ; v14 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h15 = [0, rslice 1 2 v14] in let [x25 @Natural @Double @[], v26 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = h15 in x16] [let [x18 @Natural @Double @[], v19 @Natural @Double @[2]] = h15 in v19, let [x20 @Natural @Double @[], v21 @Natural @Double @[2], v22 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h11 in v21, let [v23 @Natural @Double @[2]] = h11 in v23] in x25 + v14 ! [0]"

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
    @?= "let h11 = [rconst (rfromListLinear [2] [5.0,7.0])] ; v14 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h15 = [0, rslice 1 2 v14] in let [x25 @Natural @Double @[], v26 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [let [x16 @Natural @Double @[], v17 @Natural @Double @[2]] = h15 in x16] [let [x18 @Natural @Double @[], v19 @Natural @Double @[2]] = h15 in v19, let [x20 @Natural @Double @[], v21 @Natural @Double @[2], v22 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] h11 in v21, let [v23 @Natural @Double @[2]] = h11 in v23] in x25 + v14 ! [0]"

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
               $ dunHVector $ unHVectorPseudoTensor
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
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
                      (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5 (2 * a0)))
                      (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0)) (rscalar 1.1))

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
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPretty
    IM.empty
    (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h13 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in v11, rreplicate 11 1.1] in [rsum (let [x14 @Natural @Double @[], v15 @Natural @Double @[11]] = h13 in v15) + let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = h13 in x16]"

testSin0FoldNestedR1SimpPP :: Assertion
testSin0FoldNestedR1SimpPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h13 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1] in v11, rreplicate 11 1.1] in [rsum (let [x14 @Natural @Double @[], v15 @Natural @Double @[11]] = h13 in v15) + let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = h13 in x16]"

testSin0FoldNestedR1SimpNestedPP :: Assertion
testSin0FoldNestedR1SimpNestedPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h13 = dmapAccumRDer (SNat @11) (\\h18 -> let [x46 @Natural @Double @[]] = tproject1 h18 in let [x47 @Natural @Double @[], x48 @Natural @Double @[]] = tproject2 h18 in let h49 = [x47, x48] ; h58 = dmapAccumRDer (SNat @22) (\\h63 -> let [x85 @Natural @Double @[]] = tproject1 h63 in let [x86 @Natural @Double @[], x87 @Natural @Double @[]] = tproject2 h63 in let x88 = cos x87 in [x85, recip (x88 * x88) * x85]) (\\h89 -> let h144 = [let [x138 @Natural @Double @[], x139 @Natural @Double @[], x140 @Natural @Double @[]] = tproject2 h89 in x139, let [x141 @Natural @Double @[], x142 @Natural @Double @[], x143 @Natural @Double @[]] = tproject2 h89 in x143] ; x147 = cos (let [x145 @Natural @Double @[], x146 @Natural @Double @[]] = h144 in x146) ; x148 = x147 * x147 ; x154 = let [x149 @Natural @Double @[], x150 @Natural @Double @[], x151 @Natural @Double @[]] = tproject1 h89 in x151 * negate (sin (let [x152 @Natural @Double @[], x153 @Natural @Double @[]] = h144 in x153)) in [let [x155 @Natural @Double @[], x156 @Natural @Double @[], x157 @Natural @Double @[]] = tproject1 h89 in x155, ((x154 * x147 + x154 * x147) * negate (recip (x148 * x148))) * let [x158 @Natural @Double @[], x159 @Natural @Double @[], x160 @Natural @Double @[]] = tproject2 h89 in x158 + let [x161 @Natural @Double @[], x162 @Natural @Double @[], x163 @Natural @Double @[]] = tproject1 h89 in x161 * recip x148]) (\\h164 -> let h213 = [let [x207 @Natural @Double @[], x208 @Natural @Double @[], x209 @Natural @Double @[]] = tproject2 h164 in x208, let [x210 @Natural @Double @[], x211 @Natural @Double @[], x212 @Natural @Double @[]] = tproject2 h164 in x212] ; x216 = cos (let [x214 @Natural @Double @[], x215 @Natural @Double @[]] = h213 in x215) ; x217 = x216 * x216 ; x223 = negate (recip (x217 * x217)) * (let [x218 @Natural @Double @[], x219 @Natural @Double @[], x220 @Natural @Double @[]] = tproject2 h164 in x218 * let [x221 @Natural @Double @[], x222 @Natural @Double @[]] = tproject1 h164 in x222) in [recip x217 * let [x224 @Natural @Double @[], x225 @Natural @Double @[]] = tproject1 h164 in x225 + let [x226 @Natural @Double @[], x227 @Natural @Double @[]] = tproject1 h164 in x226, 0, negate (sin (let [x228 @Natural @Double @[], x229 @Natural @Double @[]] = h213 in x229)) * (x216 * x223 + x216 * x223)]) [x46] [let [x54 @Natural @Double @[], v55 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h230 -> let [x244 @Natural @Double @[]] = tproject1 h230 in let [x247 @Natural @Double @[]] = let [x245 @Natural @Double @[]] = tproject1 h230 in let [x246 @Natural @Double @[]] = tproject2 h230 in [x245 + tan x246] in [x247, x244]) (\\h248 -> let [x278 @Natural @Double @[], x279 @Natural @Double @[]] = tproject1 h248 in let x282 = cos (let [x280 @Natural @Double @[], x281 @Natural @Double @[]] = tproject2 h248 in x281) in [let [x283 @Natural @Double @[], x284 @Natural @Double @[]] = tproject1 h248 in x283 + let [x285 @Natural @Double @[], x286 @Natural @Double @[]] = tproject1 h248 in x286 * recip (x282 * x282), x278]) (\\h287 -> let [x304 @Natural @Double @[], x305 @Natural @Double @[]] = tproject1 h287 in let x308 = cos (let [x306 @Natural @Double @[], x307 @Natural @Double @[]] = tproject2 h287 in x307) in [x304 + x305, recip (x308 * x308) * x304]) [let [x50 @Natural @Double @[], x51 @Natural @Double @[]] = h49 in x51] [rreplicate 22 (let [x52 @Natural @Double @[], x53 @Natural @Double @[]] = h49 in x52)] in v55, rreplicate 22 (let [x56 @Natural @Double @[], x57 @Natural @Double @[]] = h49 in x56)] in [rsum (let [x59 @Natural @Double @[], v60 @Natural @Double @[22]] = h58 in v60), let [x61 @Natural @Double @[], v62 @Natural @Double @[22]] = h58 in x61]) (\\h309 -> let h346 = [let [x340 @Natural @Double @[], x341 @Natural @Double @[], x342 @Natural @Double @[]] = tproject2 h309 in x341, let [x343 @Natural @Double @[], x344 @Natural @Double @[], x345 @Natural @Double @[]] = tproject2 h309 in x345] ; h351 = dmapAccumLDer (SNat @22) (\\h392 -> let [x406 @Natural @Double @[]] = tproject1 h392 in let [x411 @Natural @Double @[], x412 @Natural @Double @[]] = let [x407 @Natural @Double @[]] = tproject1 h392 in let [x410 @Natural @Double @[]] = let [x408 @Natural @Double @[]] = tproject1 h392 in let [x409 @Natural @Double @[]] = tproject2 h392 in [x408 + tan x409] in [x410, x407] in [x411, x406, x412]) (\\h413 -> let [x438 @Natural @Double @[], x439 @Natural @Double @[]] = tproject1 h413 in let [x449 @Natural @Double @[], x450 @Natural @Double @[]] = let [x440 @Natural @Double @[], x441 @Natural @Double @[]] = tproject1 h413 in let x444 = cos (let [x442 @Natural @Double @[], x443 @Natural @Double @[]] = tproject2 h413 in x443) in [let [x445 @Natural @Double @[], x446 @Natural @Double @[]] = tproject1 h413 in x445 + let [x447 @Natural @Double @[], x448 @Natural @Double @[]] = tproject1 h413 in x448 * recip (x444 * x444), x440] in [x449, x438, x450]) (\\h451 -> let [x469 @Natural @Double @[], x470 @Natural @Double @[], x471 @Natural @Double @[]] = tproject1 h451 in let x474 = cos (let [x472 @Natural @Double @[], x473 @Natural @Double @[]] = tproject2 h451 in x473) in [x470 + x469 + x471, recip (x474 * x474) * x469]) [let [x347 @Natural @Double @[], x348 @Natural @Double @[]] = h346 in x348] [rreplicate 22 (let [x349 @Natural @Double @[], x350 @Natural @Double @[]] = h346 in x349)] ; h357 = [let [x352 @Natural @Double @[], v353 @Natural @Double @[22], v354 @Natural @Double @[22]] = h351 in v354, rreplicate 22 (let [x355 @Natural @Double @[], x356 @Natural @Double @[]] = h346 in x355)] ; h387 = dmapAccumRDer (SNat @22) (\\h475 -> let [x536 @Natural @Double @[]] = tproject1 h475 in let [x537 @Natural @Double @[], x538 @Natural @Double @[], x539 @Natural @Double @[], x540 @Natural @Double @[], x541 @Natural @Double @[]] = tproject2 h475 in let h542 = [x540, x541] ; x545 = cos (let [x543 @Natural @Double @[], x544 @Natural @Double @[]] = h542 in x544) ; x546 = x545 * x545 ; x549 = x538 * negate (sin (let [x547 @Natural @Double @[], x548 @Natural @Double @[]] = h542 in x548)) in [x536, ((x549 * x545 + x549 * x545) * negate (recip (x546 * x546))) * x539 + x536 * recip x546]) (\\h550 -> let h626 = [let [x614 @Natural @Double @[], x615 @Natural @Double @[], x616 @Natural @Double @[], x617 @Natural @Double @[], x618 @Natural @Double @[], x619 @Natural @Double @[]] = tproject2 h550 in x618, let [x620 @Natural @Double @[], x621 @Natural @Double @[], x622 @Natural @Double @[], x623 @Natural @Double @[], x624 @Natural @Double @[], x625 @Natural @Double @[]] = tproject2 h550 in x625] ; x629 = cos (let [x627 @Natural @Double @[], x628 @Natural @Double @[]] = h626 in x628) ; x630 = x629 * x629 ; x633 = negate (sin (let [x631 @Natural @Double @[], x632 @Natural @Double @[]] = h626 in x632)) ; x640 = let [x634 @Natural @Double @[], x635 @Natural @Double @[], x636 @Natural @Double @[], x637 @Natural @Double @[], x638 @Natural @Double @[], x639 @Natural @Double @[]] = tproject2 h550 in x636 * x633 ; x641 = x630 * x630 ; x642 = x640 * x629 + x640 * x629 ; x643 = negate (recip x641) ; x664 = let [x644 @Natural @Double @[], x645 @Natural @Double @[], x646 @Natural @Double @[], x647 @Natural @Double @[], x648 @Natural @Double @[], x649 @Natural @Double @[]] = tproject1 h550 in x646 * x633 + ((let [x650 @Natural @Double @[], x651 @Natural @Double @[], x652 @Natural @Double @[], x653 @Natural @Double @[], x654 @Natural @Double @[], x655 @Natural @Double @[]] = tproject1 h550 in x655 * cos (let [x656 @Natural @Double @[], x657 @Natural @Double @[]] = h626 in x657)) * -1.0) * let [x658 @Natural @Double @[], x659 @Natural @Double @[], x660 @Natural @Double @[], x661 @Natural @Double @[], x662 @Natural @Double @[], x663 @Natural @Double @[]] = tproject2 h550 in x660 ; x673 = let [x665 @Natural @Double @[], x666 @Natural @Double @[], x667 @Natural @Double @[], x668 @Natural @Double @[], x669 @Natural @Double @[], x670 @Natural @Double @[]] = tproject1 h550 in x670 * negate (sin (let [x671 @Natural @Double @[], x672 @Natural @Double @[]] = h626 in x672)) ; x674 = x673 * x629 + x673 * x629 in [let [x675 @Natural @Double @[], x676 @Natural @Double @[], x677 @Natural @Double @[], x678 @Natural @Double @[], x679 @Natural @Double @[], x680 @Natural @Double @[]] = tproject1 h550 in x675, ((x664 * x629 + x673 * x640 + x664 * x629 + x673 * x640) * x643 + (((x674 * x630 + x674 * x630) * negate (recip (x641 * x641))) * -1.0) * x642) * let [x681 @Natural @Double @[], x682 @Natural @Double @[], x683 @Natural @Double @[], x684 @Natural @Double @[], x685 @Natural @Double @[], x686 @Natural @Double @[]] = tproject2 h550 in x684 + let [x687 @Natural @Double @[], x688 @Natural @Double @[], x689 @Natural @Double @[], x690 @Natural @Double @[], x691 @Natural @Double @[], x692 @Natural @Double @[]] = tproject1 h550 in x690 * (x642 * x643) + let [x693 @Natural @Double @[], x694 @Natural @Double @[], x695 @Natural @Double @[], x696 @Natural @Double @[], x697 @Natural @Double @[], x698 @Natural @Double @[]] = tproject1 h550 in x693 * recip x630 + (x674 * negate (recip (x630 * x630))) * let [x699 @Natural @Double @[], x700 @Natural @Double @[], x701 @Natural @Double @[], x702 @Natural @Double @[], x703 @Natural @Double @[], x704 @Natural @Double @[]] = tproject2 h550 in x699]) (\\h705 -> let h770 = [let [x758 @Natural @Double @[], x759 @Natural @Double @[], x760 @Natural @Double @[], x761 @Natural @Double @[], x762 @Natural @Double @[], x763 @Natural @Double @[]] = tproject2 h705 in x762, let [x764 @Natural @Double @[], x765 @Natural @Double @[], x766 @Natural @Double @[], x767 @Natural @Double @[], x768 @Natural @Double @[], x769 @Natural @Double @[]] = tproject2 h705 in x769] ; x773 = cos (let [x771 @Natural @Double @[], x772 @Natural @Double @[]] = h770 in x772) ; x774 = x773 * x773 ; x777 = negate (sin (let [x775 @Natural @Double @[], x776 @Natural @Double @[]] = h770 in x776)) ; x784 = let [x778 @Natural @Double @[], x779 @Natural @Double @[], x780 @Natural @Double @[], x781 @Natural @Double @[], x782 @Natural @Double @[], x783 @Natural @Double @[]] = tproject2 h705 in x780 * x777 ; x785 = x774 * x774 ; x786 = x784 * x773 + x784 * x773 ; x787 = negate (recip x785) ; x796 = let [x788 @Natural @Double @[], x789 @Natural @Double @[], x790 @Natural @Double @[], x791 @Natural @Double @[], x792 @Natural @Double @[], x793 @Natural @Double @[]] = tproject2 h705 in x791 * let [x794 @Natural @Double @[], x795 @Natural @Double @[]] = tproject1 h705 in x795 ; x797 = negate (recip (x785 * x785)) * (-1.0 * (x786 * x796)) ; x798 = x787 * x796 ; x799 = x773 * x798 + x773 * x798 ; x808 = x774 * x797 + x774 * x797 + negate (recip (x774 * x774)) * (let [x800 @Natural @Double @[], x801 @Natural @Double @[], x802 @Natural @Double @[], x803 @Natural @Double @[], x804 @Natural @Double @[], x805 @Natural @Double @[]] = tproject2 h705 in x800 * let [x806 @Natural @Double @[], x807 @Natural @Double @[]] = tproject1 h705 in x807) in [recip x774 * let [x809 @Natural @Double @[], x810 @Natural @Double @[]] = tproject1 h705 in x810 + let [x811 @Natural @Double @[], x812 @Natural @Double @[]] = tproject1 h705 in x811, 0, x777 * x799, (x786 * x787) * let [x813 @Natural @Double @[], x814 @Natural @Double @[]] = tproject1 h705 in x814, 0, negate (sin (let [x815 @Natural @Double @[], x816 @Natural @Double @[]] = h770 in x816)) * (x773 * x808 + x773 * x808 + x784 * x798 + x784 * x798) + cos (let [x817 @Natural @Double @[], x818 @Natural @Double @[]] = h770 in x818) * (-1.0 * (let [x819 @Natural @Double @[], x820 @Natural @Double @[], x821 @Natural @Double @[], x822 @Natural @Double @[], x823 @Natural @Double @[], x824 @Natural @Double @[]] = tproject2 h705 in x821 * x799))]) [let [x358 @Natural @Double @[], x359 @Natural @Double @[], x360 @Natural @Double @[]] = tproject1 h309 in x358] [let [x372 @Natural @Double @[], v373 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h825 -> let [x840 @Natural @Double @[]] = tproject1 h825 in let [x841 @Natural @Double @[], x842 @Natural @Double @[], x843 @Natural @Double @[]] = tproject2 h825 in let x844 = cos x843 in [x840 + x841 * recip (x844 * x844), x840]) (\\h845 -> let x874 = cos (let [x870 @Natural @Double @[], x871 @Natural @Double @[], x872 @Natural @Double @[], x873 @Natural @Double @[]] = tproject2 h845 in x873) ; x875 = x874 * x874 ; x884 = let [x876 @Natural @Double @[], x877 @Natural @Double @[], x878 @Natural @Double @[], x879 @Natural @Double @[]] = tproject1 h845 in x879 * negate (sin (let [x880 @Natural @Double @[], x881 @Natural @Double @[], x882 @Natural @Double @[], x883 @Natural @Double @[]] = tproject2 h845 in x883)) in [let [x885 @Natural @Double @[], x886 @Natural @Double @[], x887 @Natural @Double @[], x888 @Natural @Double @[]] = tproject1 h845 in x885 + let [x889 @Natural @Double @[], x890 @Natural @Double @[], x891 @Natural @Double @[], x892 @Natural @Double @[]] = tproject1 h845 in x890 * recip x875 + ((x884 * x874 + x884 * x874) * negate (recip (x875 * x875))) * let [x893 @Natural @Double @[], x894 @Natural @Double @[], x895 @Natural @Double @[], x896 @Natural @Double @[]] = tproject2 h845 in x894, let [x897 @Natural @Double @[], x898 @Natural @Double @[], x899 @Natural @Double @[], x900 @Natural @Double @[]] = tproject1 h845 in x897]) (\\h901 -> let x926 = cos (let [x922 @Natural @Double @[], x923 @Natural @Double @[], x924 @Natural @Double @[], x925 @Natural @Double @[]] = tproject2 h901 in x925) ; x927 = x926 * x926 ; x934 = negate (recip (x927 * x927)) * (let [x928 @Natural @Double @[], x929 @Natural @Double @[], x930 @Natural @Double @[], x931 @Natural @Double @[]] = tproject2 h901 in x929 * let [x932 @Natural @Double @[], x933 @Natural @Double @[]] = tproject1 h901 in x932) in [let [x935 @Natural @Double @[], x936 @Natural @Double @[]] = tproject1 h901 in x935 + let [x937 @Natural @Double @[], x938 @Natural @Double @[]] = tproject1 h901 in x938, recip x927 * let [x939 @Natural @Double @[], x940 @Natural @Double @[]] = tproject1 h901 in x939, 0, negate (sin (let [x941 @Natural @Double @[], x942 @Natural @Double @[], x943 @Natural @Double @[], x944 @Natural @Double @[]] = tproject2 h901 in x944)) * (x926 * x934 + x926 * x934)]) [let [x361 @Natural @Double @[], x362 @Natural @Double @[], x363 @Natural @Double @[]] = tproject1 h309 in x363] [rreplicate 22 (let [x364 @Natural @Double @[], x365 @Natural @Double @[], x366 @Natural @Double @[]] = tproject1 h309 in x365), let [x367 @Natural @Double @[], v368 @Natural @Double @[22], v369 @Natural @Double @[22]] = h351 in v368, rreplicate 22 (let [x370 @Natural @Double @[], x371 @Natural @Double @[]] = h346 in x370)] in v373, rreplicate 22 (let [x374 @Natural @Double @[], x375 @Natural @Double @[], x376 @Natural @Double @[]] = tproject1 h309 in x375), let [x380 @Natural @Double @[], v381 @Natural @Double @[22], v382 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h945 -> let [x959 @Natural @Double @[]] = tproject1 h945 in let [x964 @Natural @Double @[], x965 @Natural @Double @[]] = let [x960 @Natural @Double @[]] = tproject1 h945 in let [x961 @Natural @Double @[], x962 @Natural @Double @[]] = tproject2 h945 in let x963 = cos x962 in [x960, recip (x963 * x963) * x960] in [x964, x959, x965]) (\\h966 -> let [x999 @Natural @Double @[], x1000 @Natural @Double @[], x1001 @Natural @Double @[]] = tproject1 h966 in let h1008 = [let [x1002 @Natural @Double @[], x1003 @Natural @Double @[], x1004 @Natural @Double @[]] = tproject2 h966 in x1003, let [x1005 @Natural @Double @[], x1006 @Natural @Double @[], x1007 @Natural @Double @[]] = tproject2 h966 in x1007] ; x1011 = cos (let [x1009 @Natural @Double @[], x1010 @Natural @Double @[]] = h1008 in x1010) ; x1012 = x1011 * x1011 ; x1018 = let [x1013 @Natural @Double @[], x1014 @Natural @Double @[], x1015 @Natural @Double @[]] = tproject1 h966 in x1015 * negate (sin (let [x1016 @Natural @Double @[], x1017 @Natural @Double @[]] = h1008 in x1017)) in [let [x1019 @Natural @Double @[], x1020 @Natural @Double @[], x1021 @Natural @Double @[]] = tproject1 h966 in x1019, x999, ((x1018 * x1011 + x1018 * x1011) * negate (recip (x1012 * x1012))) * let [x1022 @Natural @Double @[], x1023 @Natural @Double @[], x1024 @Natural @Double @[]] = tproject2 h966 in x1022 + let [x1025 @Natural @Double @[], x1026 @Natural @Double @[], x1027 @Natural @Double @[]] = tproject1 h966 in x1025 * recip x1012]) (\\h1028 -> let [x1083 @Natural @Double @[], x1084 @Natural @Double @[], x1085 @Natural @Double @[]] = tproject1 h1028 in let h1092 = [let [x1086 @Natural @Double @[], x1087 @Natural @Double @[], x1088 @Natural @Double @[]] = tproject2 h1028 in x1087, let [x1089 @Natural @Double @[], x1090 @Natural @Double @[], x1091 @Natural @Double @[]] = tproject2 h1028 in x1091] ; x1095 = cos (let [x1093 @Natural @Double @[], x1094 @Natural @Double @[]] = h1092 in x1094) ; x1096 = x1095 * x1095 ; x1100 = negate (recip (x1096 * x1096)) * (let [x1097 @Natural @Double @[], x1098 @Natural @Double @[], x1099 @Natural @Double @[]] = tproject2 h1028 in x1097 * x1085) in [x1084 + recip x1096 * x1085 + x1083, 0.0, negate (sin (let [x1101 @Natural @Double @[], x1102 @Natural @Double @[]] = h1092 in x1102)) * (x1095 * x1100 + x1095 * x1100)]) [let [x377 @Natural @Double @[], x378 @Natural @Double @[], x379 @Natural @Double @[]] = tproject2 h309 in x377] h357 in v381, let [v383 @Natural @Double @[22], v384 @Natural @Double @[22]] = h357 in v383, let [v385 @Natural @Double @[22], v386 @Natural @Double @[22]] = h357 in v386] in [rsum (let [x388 @Natural @Double @[], v389 @Natural @Double @[22]] = h387 in v389), let [x390 @Natural @Double @[], v391 @Natural @Double @[22]] = h387 in x390]) (\\h1103 -> let h1143 = [let [x1137 @Natural @Double @[], x1138 @Natural @Double @[], x1139 @Natural @Double @[]] = tproject2 h1103 in x1138, let [x1140 @Natural @Double @[], x1141 @Natural @Double @[], x1142 @Natural @Double @[]] = tproject2 h1103 in x1142] ; h1148 = dmapAccumLDer (SNat @22) (\\h1209 -> let [x1223 @Natural @Double @[]] = tproject1 h1209 in let [x1228 @Natural @Double @[], x1229 @Natural @Double @[]] = let [x1224 @Natural @Double @[]] = tproject1 h1209 in let [x1227 @Natural @Double @[]] = let [x1225 @Natural @Double @[]] = tproject1 h1209 in let [x1226 @Natural @Double @[]] = tproject2 h1209 in [x1225 + tan x1226] in [x1227, x1224] in [x1228, x1223, x1229]) (\\h1230 -> let [x1255 @Natural @Double @[], x1256 @Natural @Double @[]] = tproject1 h1230 in let [x1266 @Natural @Double @[], x1267 @Natural @Double @[]] = let [x1257 @Natural @Double @[], x1258 @Natural @Double @[]] = tproject1 h1230 in let x1261 = cos (let [x1259 @Natural @Double @[], x1260 @Natural @Double @[]] = tproject2 h1230 in x1260) in [let [x1262 @Natural @Double @[], x1263 @Natural @Double @[]] = tproject1 h1230 in x1262 + let [x1264 @Natural @Double @[], x1265 @Natural @Double @[]] = tproject1 h1230 in x1265 * recip (x1261 * x1261), x1257] in [x1266, x1255, x1267]) (\\h1268 -> let [x1286 @Natural @Double @[], x1287 @Natural @Double @[], x1288 @Natural @Double @[]] = tproject1 h1268 in let x1291 = cos (let [x1289 @Natural @Double @[], x1290 @Natural @Double @[]] = tproject2 h1268 in x1290) in [x1287 + x1286 + x1288, recip (x1291 * x1291) * x1286]) [let [x1144 @Natural @Double @[], x1145 @Natural @Double @[]] = h1143 in x1145] [rreplicate 22 (let [x1146 @Natural @Double @[], x1147 @Natural @Double @[]] = h1143 in x1146)] ; h1154 = [let [x1149 @Natural @Double @[], v1150 @Natural @Double @[22], v1151 @Natural @Double @[22]] = h1148 in v1151, rreplicate 22 (let [x1152 @Natural @Double @[], x1153 @Natural @Double @[]] = h1143 in x1152)] ; h1157 = [let [x1155 @Natural @Double @[], x1156 @Natural @Double @[]] = tproject1 h1103 in x1156, 0] ; h1160 = [0, rreplicate 22 (let [x1158 @Natural @Double @[], x1159 @Natural @Double @[]] = tproject1 h1103 in x1158)] ; h1169 = [let [x1161 @Natural @Double @[], v1162 @Natural @Double @[22]] = h1160 in x1161 + let [x1163 @Natural @Double @[], v1164 @Natural @Double @[22]] = h1157 in x1163, let [x1165 @Natural @Double @[], v1166 @Natural @Double @[22]] = h1160 in v1166 + let [x1167 @Natural @Double @[], v1168 @Natural @Double @[22]] = h1157 in v1168] ; h1184 = dmapAccumLDer (SNat @22) (\\h1292 -> let [x1346 @Natural @Double @[]] = tproject1 h1292 in let [x1347 @Natural @Double @[], x1348 @Natural @Double @[], x1349 @Natural @Double @[], x1350 @Natural @Double @[]] = tproject2 h1292 in let h1351 = [x1349, x1350] ; x1354 = cos (let [x1352 @Natural @Double @[], x1353 @Natural @Double @[]] = h1351 in x1353) ; x1355 = x1354 * x1354 ; x1356 = negate (recip (x1355 * x1355)) * (x1348 * x1347) in [recip x1355 * x1347 + x1346, 0, negate (sin (let [x1357 @Natural @Double @[], x1358 @Natural @Double @[]] = h1351 in x1358)) * (x1354 * x1356 + x1354 * x1356)]) (\\h1359 -> let h1429 = [let [x1419 @Natural @Double @[], x1420 @Natural @Double @[], x1421 @Natural @Double @[], x1422 @Natural @Double @[], x1423 @Natural @Double @[]] = tproject2 h1359 in x1422, let [x1424 @Natural @Double @[], x1425 @Natural @Double @[], x1426 @Natural @Double @[], x1427 @Natural @Double @[], x1428 @Natural @Double @[]] = tproject2 h1359 in x1428] ; x1432 = cos (let [x1430 @Natural @Double @[], x1431 @Natural @Double @[]] = h1429 in x1431) ; x1433 = x1432 * x1432 ; x1434 = x1433 * x1433 ; x1435 = negate (recip x1434) ; x1446 = let [x1436 @Natural @Double @[], x1437 @Natural @Double @[], x1438 @Natural @Double @[], x1439 @Natural @Double @[], x1440 @Natural @Double @[]] = tproject2 h1359 in x1438 * let [x1441 @Natural @Double @[], x1442 @Natural @Double @[], x1443 @Natural @Double @[], x1444 @Natural @Double @[], x1445 @Natural @Double @[]] = tproject2 h1359 in x1442 ; x1447 = x1435 * x1446 ; x1455 = let [x1448 @Natural @Double @[], x1449 @Natural @Double @[], x1450 @Natural @Double @[], x1451 @Natural @Double @[], x1452 @Natural @Double @[]] = tproject1 h1359 in x1452 * negate (sin (let [x1453 @Natural @Double @[], x1454 @Natural @Double @[]] = h1429 in x1454)) ; x1456 = x1455 * x1432 + x1455 * x1432 ; x1477 = (((x1456 * x1433 + x1456 * x1433) * negate (recip (x1434 * x1434))) * -1.0) * x1446 + (let [x1457 @Natural @Double @[], x1458 @Natural @Double @[], x1459 @Natural @Double @[], x1460 @Natural @Double @[], x1461 @Natural @Double @[]] = tproject1 h1359 in x1459 * let [x1462 @Natural @Double @[], x1463 @Natural @Double @[], x1464 @Natural @Double @[], x1465 @Natural @Double @[], x1466 @Natural @Double @[]] = tproject2 h1359 in x1463 + let [x1467 @Natural @Double @[], x1468 @Natural @Double @[], x1469 @Natural @Double @[], x1470 @Natural @Double @[], x1471 @Natural @Double @[]] = tproject1 h1359 in x1468 * let [x1472 @Natural @Double @[], x1473 @Natural @Double @[], x1474 @Natural @Double @[], x1475 @Natural @Double @[], x1476 @Natural @Double @[]] = tproject2 h1359 in x1474) * x1435 in [let [x1478 @Natural @Double @[], x1479 @Natural @Double @[], x1480 @Natural @Double @[], x1481 @Natural @Double @[], x1482 @Natural @Double @[]] = tproject1 h1359 in x1478 + (x1456 * negate (recip (x1433 * x1433))) * let [x1483 @Natural @Double @[], x1484 @Natural @Double @[], x1485 @Natural @Double @[], x1486 @Natural @Double @[], x1487 @Natural @Double @[]] = tproject2 h1359 in x1484 + let [x1488 @Natural @Double @[], x1489 @Natural @Double @[], x1490 @Natural @Double @[], x1491 @Natural @Double @[], x1492 @Natural @Double @[]] = tproject1 h1359 in x1489 * recip x1433, 0.0, ((let [x1493 @Natural @Double @[], x1494 @Natural @Double @[], x1495 @Natural @Double @[], x1496 @Natural @Double @[], x1497 @Natural @Double @[]] = tproject1 h1359 in x1497 * cos (let [x1498 @Natural @Double @[], x1499 @Natural @Double @[]] = h1429 in x1499)) * -1.0) * (x1432 * x1447 + x1432 * x1447) + (x1455 * x1447 + x1477 * x1432 + x1455 * x1447 + x1477 * x1432) * negate (sin (let [x1500 @Natural @Double @[], x1501 @Natural @Double @[]] = h1429 in x1501))]) (\\h1502 -> let h1561 = [let [x1551 @Natural @Double @[], x1552 @Natural @Double @[], x1553 @Natural @Double @[], x1554 @Natural @Double @[], x1555 @Natural @Double @[]] = tproject2 h1502 in x1554, let [x1556 @Natural @Double @[], x1557 @Natural @Double @[], x1558 @Natural @Double @[], x1559 @Natural @Double @[], x1560 @Natural @Double @[]] = tproject2 h1502 in x1560] ; x1564 = cos (let [x1562 @Natural @Double @[], x1563 @Natural @Double @[]] = h1561 in x1563) ; x1565 = x1564 * x1564 ; x1566 = x1565 * x1565 ; x1567 = negate (recip x1566) ; x1578 = let [x1568 @Natural @Double @[], x1569 @Natural @Double @[], x1570 @Natural @Double @[], x1571 @Natural @Double @[], x1572 @Natural @Double @[]] = tproject2 h1502 in x1570 * let [x1573 @Natural @Double @[], x1574 @Natural @Double @[], x1575 @Natural @Double @[], x1576 @Natural @Double @[], x1577 @Natural @Double @[]] = tproject2 h1502 in x1574 ; x1579 = x1567 * x1578 ; x1585 = negate (sin (let [x1580 @Natural @Double @[], x1581 @Natural @Double @[]] = h1561 in x1581)) * let [x1582 @Natural @Double @[], x1583 @Natural @Double @[], x1584 @Natural @Double @[]] = tproject1 h1502 in x1584 ; x1586 = x1564 * x1585 + x1564 * x1585 ; x1587 = x1567 * x1586 ; x1588 = negate (recip (x1566 * x1566)) * (-1.0 * (x1578 * x1586)) ; x1597 = x1565 * x1588 + x1565 * x1588 + negate (recip (x1565 * x1565)) * (let [x1589 @Natural @Double @[], x1590 @Natural @Double @[], x1591 @Natural @Double @[], x1592 @Natural @Double @[], x1593 @Natural @Double @[]] = tproject2 h1502 in x1590 * let [x1594 @Natural @Double @[], x1595 @Natural @Double @[], x1596 @Natural @Double @[]] = tproject1 h1502 in x1594) in [let [x1598 @Natural @Double @[], x1599 @Natural @Double @[], x1600 @Natural @Double @[]] = tproject1 h1502 in x1598, let [x1601 @Natural @Double @[], x1602 @Natural @Double @[], x1603 @Natural @Double @[], x1604 @Natural @Double @[], x1605 @Natural @Double @[]] = tproject2 h1502 in x1603 * x1587 + recip x1565 * let [x1606 @Natural @Double @[], x1607 @Natural @Double @[], x1608 @Natural @Double @[]] = tproject1 h1502 in x1606, let [x1609 @Natural @Double @[], x1610 @Natural @Double @[], x1611 @Natural @Double @[], x1612 @Natural @Double @[], x1613 @Natural @Double @[]] = tproject2 h1502 in x1610 * x1587, 0, negate (sin (let [x1614 @Natural @Double @[], x1615 @Natural @Double @[]] = h1561 in x1615)) * (x1564 * x1597 + x1564 * x1597 + x1579 * x1585 + x1579 * x1585) + cos (let [x1616 @Natural @Double @[], x1617 @Natural @Double @[]] = h1561 in x1617) * (-1.0 * ((x1564 * x1579 + x1564 * x1579) * let [x1618 @Natural @Double @[], x1619 @Natural @Double @[], x1620 @Natural @Double @[]] = tproject1 h1502 in x1620))]) [let [x1170 @Natural @Double @[], v1171 @Natural @Double @[22]] = h1169 in x1170] [let [x1172 @Natural @Double @[], v1173 @Natural @Double @[22]] = h1169 in v1173, let [x1177 @Natural @Double @[], v1178 @Natural @Double @[22], v1179 @Natural @Double @[22]] = dmapAccumRDer (SNat @22) (\\h1621 -> let [x1635 @Natural @Double @[]] = tproject1 h1621 in let [x1640 @Natural @Double @[], x1641 @Natural @Double @[]] = let [x1636 @Natural @Double @[]] = tproject1 h1621 in let [x1637 @Natural @Double @[], x1638 @Natural @Double @[]] = tproject2 h1621 in let x1639 = cos x1638 in [x1636, recip (x1639 * x1639) * x1636] in [x1640, x1635, x1641]) (\\h1642 -> let [x1702 @Natural @Double @[], x1703 @Natural @Double @[], x1704 @Natural @Double @[]] = tproject1 h1642 in let h1711 = [let [x1705 @Natural @Double @[], x1706 @Natural @Double @[], x1707 @Natural @Double @[]] = tproject2 h1642 in x1706, let [x1708 @Natural @Double @[], x1709 @Natural @Double @[], x1710 @Natural @Double @[]] = tproject2 h1642 in x1710] ; x1714 = cos (let [x1712 @Natural @Double @[], x1713 @Natural @Double @[]] = h1711 in x1713) ; x1715 = x1714 * x1714 ; x1721 = let [x1716 @Natural @Double @[], x1717 @Natural @Double @[], x1718 @Natural @Double @[]] = tproject1 h1642 in x1718 * negate (sin (let [x1719 @Natural @Double @[], x1720 @Natural @Double @[]] = h1711 in x1720)) in [let [x1722 @Natural @Double @[], x1723 @Natural @Double @[], x1724 @Natural @Double @[]] = tproject1 h1642 in x1722, x1702, ((x1721 * x1714 + x1721 * x1714) * negate (recip (x1715 * x1715))) * let [x1725 @Natural @Double @[], x1726 @Natural @Double @[], x1727 @Natural @Double @[]] = tproject2 h1642 in x1725 + let [x1728 @Natural @Double @[], x1729 @Natural @Double @[], x1730 @Natural @Double @[]] = tproject1 h1642 in x1728 * recip x1715]) (\\h1731 -> let [x1762 @Natural @Double @[], x1763 @Natural @Double @[], x1764 @Natural @Double @[]] = tproject1 h1731 in let h1771 = [let [x1765 @Natural @Double @[], x1766 @Natural @Double @[], x1767 @Natural @Double @[]] = tproject2 h1731 in x1766, let [x1768 @Natural @Double @[], x1769 @Natural @Double @[], x1770 @Natural @Double @[]] = tproject2 h1731 in x1770] ; x1774 = cos (let [x1772 @Natural @Double @[], x1773 @Natural @Double @[]] = h1771 in x1773) ; x1775 = x1774 * x1774 ; x1779 = negate (recip (x1775 * x1775)) * (let [x1776 @Natural @Double @[], x1777 @Natural @Double @[], x1778 @Natural @Double @[]] = tproject2 h1731 in x1776 * x1764) in [x1763 + recip x1775 * x1764 + x1762, 0.0, negate (sin (let [x1780 @Natural @Double @[], x1781 @Natural @Double @[]] = h1771 in x1781)) * (x1774 * x1779 + x1774 * x1779)]) [let [x1174 @Natural @Double @[], x1175 @Natural @Double @[], x1176 @Natural @Double @[]] = tproject2 h1103 in x1174] h1154 in v1178, let [v1180 @Natural @Double @[22], v1181 @Natural @Double @[22]] = h1154 in v1180, let [v1182 @Natural @Double @[22], v1183 @Natural @Double @[22]] = h1154 in v1183] ; h1188 = [0, let [x1185 @Natural @Double @[], v1186 @Natural @Double @[22], v1187 @Natural @Double @[22]] = h1184 in v1186] ; h1198 = dmapAccumRDer (SNat @22) (\\h1782 -> let [x1793 @Natural @Double @[]] = tproject1 h1782 in let [x1794 @Natural @Double @[], x1795 @Natural @Double @[], x1796 @Natural @Double @[]] = tproject2 h1782 in let x1797 = cos x1796 in [x1793 + x1794, recip (x1797 * x1797) * x1793]) (\\h1798 -> let x1823 = cos (let [x1819 @Natural @Double @[], x1820 @Natural @Double @[], x1821 @Natural @Double @[], x1822 @Natural @Double @[]] = tproject2 h1798 in x1822) ; x1824 = x1823 * x1823 ; x1833 = let [x1825 @Natural @Double @[], x1826 @Natural @Double @[], x1827 @Natural @Double @[], x1828 @Natural @Double @[]] = tproject1 h1798 in x1828 * negate (sin (let [x1829 @Natural @Double @[], x1830 @Natural @Double @[], x1831 @Natural @Double @[], x1832 @Natural @Double @[]] = tproject2 h1798 in x1832)) in [let [x1834 @Natural @Double @[], x1835 @Natural @Double @[], x1836 @Natural @Double @[], x1837 @Natural @Double @[]] = tproject1 h1798 in x1834 + let [x1838 @Natural @Double @[], x1839 @Natural @Double @[], x1840 @Natural @Double @[], x1841 @Natural @Double @[]] = tproject1 h1798 in x1839, ((x1833 * x1823 + x1833 * x1823) * negate (recip (x1824 * x1824))) * let [x1842 @Natural @Double @[], x1843 @Natural @Double @[], x1844 @Natural @Double @[], x1845 @Natural @Double @[]] = tproject2 h1798 in x1842 + let [x1846 @Natural @Double @[], x1847 @Natural @Double @[], x1848 @Natural @Double @[], x1849 @Natural @Double @[]] = tproject1 h1798 in x1846 * recip x1824]) (\\h1850 -> let x1871 = cos (let [x1867 @Natural @Double @[], x1868 @Natural @Double @[], x1869 @Natural @Double @[], x1870 @Natural @Double @[]] = tproject2 h1850 in x1870) ; x1872 = x1871 * x1871 ; x1879 = negate (recip (x1872 * x1872)) * (let [x1873 @Natural @Double @[], x1874 @Natural @Double @[], x1875 @Natural @Double @[], x1876 @Natural @Double @[]] = tproject2 h1850 in x1873 * let [x1877 @Natural @Double @[], x1878 @Natural @Double @[]] = tproject1 h1850 in x1878) in [let [x1880 @Natural @Double @[], x1881 @Natural @Double @[]] = tproject1 h1850 in x1880 + recip x1872 * let [x1882 @Natural @Double @[], x1883 @Natural @Double @[]] = tproject1 h1850 in x1883, let [x1884 @Natural @Double @[], x1885 @Natural @Double @[]] = tproject1 h1850 in x1884, 0, negate (sin (let [x1886 @Natural @Double @[], x1887 @Natural @Double @[], x1888 @Natural @Double @[], x1889 @Natural @Double @[]] = tproject2 h1850 in x1889)) * (x1871 * x1879 + x1871 * x1879)]) [let [x1189 @Natural @Double @[], v1190 @Natural @Double @[22]] = h1188 in x1189] [let [x1191 @Natural @Double @[], v1192 @Natural @Double @[22]] = h1188 in v1192, let [x1193 @Natural @Double @[], v1194 @Natural @Double @[22], v1195 @Natural @Double @[22]] = h1148 in v1194, rreplicate 22 (let [x1196 @Natural @Double @[], x1197 @Natural @Double @[]] = h1143 in x1196)] in [let [x1199 @Natural @Double @[], v1200 @Natural @Double @[22], v1201 @Natural @Double @[22]] = h1184 in x1199, rsum (let [x1202 @Natural @Double @[], v1203 @Natural @Double @[22]] = h1198 in v1203) + rsum (let [x1204 @Natural @Double @[], v1205 @Natural @Double @[22], v1206 @Natural @Double @[22]] = h1184 in v1206), let [x1207 @Natural @Double @[], v1208 @Natural @Double @[22]] = h1198 in x1207]) [1.0] [let [x10 @Natural @Double @[], v11 @Natural @Double @[11]] = dmapAccumLDer (SNat @11) (\\h1890 -> let [x1901 @Natural @Double @[]] = tproject1 h1890 in let [x1905 @Natural @Double @[]] = let [x1902 @Natural @Double @[]] = tproject1 h1890 in let [x1903 @Natural @Double @[]] = tproject2 h1890 in [let [x1904 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h1906 -> let [x1913 @Natural @Double @[]] = tproject1 h1906 in let [x1914 @Natural @Double @[]] = tproject2 h1906 in [x1913 + tan x1914]) (\\h1915 -> let x1934 = cos (let [x1932 @Natural @Double @[], x1933 @Natural @Double @[]] = tproject2 h1915 in x1933) in [let [x1935 @Natural @Double @[], x1936 @Natural @Double @[]] = tproject1 h1915 in x1935 + let [x1937 @Natural @Double @[], x1938 @Natural @Double @[]] = tproject1 h1915 in x1938 * recip (x1934 * x1934)]) (\\h1939 -> let x1954 = cos (let [x1952 @Natural @Double @[], x1953 @Natural @Double @[]] = tproject2 h1939 in x1953) in [let [x1955 @Natural @Double @[]] = tproject1 h1939 in x1955, recip (x1954 * x1954) * let [x1956 @Natural @Double @[]] = tproject1 h1939 in x1956]) [x1903] [rreplicate 22 x1902] in x1904] in [x1905, x1901]) (\\h1957 -> let [x1983 @Natural @Double @[], x1984 @Natural @Double @[]] = tproject1 h1957 in [let [x1997 @Natural @Double @[]] = dmapAccumLDer (SNat @22) (\\h1999 -> let [x2033 @Natural @Double @[]] = tproject1 h1999 in let [x2034 @Natural @Double @[], x2035 @Natural @Double @[], x2036 @Natural @Double @[]] = tproject2 h1999 in let h2037 = [x2033, x2034] ; x2038 = cos x2036 in [let [x2039 @Natural @Double @[], x2040 @Natural @Double @[]] = h2037 in x2039 + let [x2041 @Natural @Double @[], x2042 @Natural @Double @[]] = h2037 in x2042 * recip (x2038 * x2038)]) (\\h2043 -> let h2113 = [let [x2105 @Natural @Double @[], x2106 @Natural @Double @[], x2107 @Natural @Double @[], x2108 @Natural @Double @[]] = tproject2 h2043 in x2107, let [x2109 @Natural @Double @[], x2110 @Natural @Double @[], x2111 @Natural @Double @[], x2112 @Natural @Double @[]] = tproject2 h2043 in x2112] ; x2116 = cos (let [x2114 @Natural @Double @[], x2115 @Natural @Double @[]] = h2113 in x2115) ; x2117 = x2116 * x2116 ; x2124 = let [x2118 @Natural @Double @[], x2119 @Natural @Double @[], x2120 @Natural @Double @[], x2121 @Natural @Double @[]] = tproject1 h2043 in x2121 * negate (sin (let [x2122 @Natural @Double @[], x2123 @Natural @Double @[]] = h2113 in x2123)) in [let [x2125 @Natural @Double @[], x2126 @Natural @Double @[], x2127 @Natural @Double @[], x2128 @Natural @Double @[]] = tproject1 h2043 in x2125 + let [x2129 @Natural @Double @[], x2130 @Natural @Double @[], x2131 @Natural @Double @[], x2132 @Natural @Double @[]] = tproject1 h2043 in x2130 * recip x2117 + ((x2124 * x2116 + x2124 * x2116) * negate (recip (x2117 * x2117))) * let [x2133 @Natural @Double @[], x2134 @Natural @Double @[], x2135 @Natural @Double @[], x2136 @Natural @Double @[]] = tproject2 h2043 in x2134]) (\\h2137 -> let h2194 = [let [x2186 @Natural @Double @[], x2187 @Natural @Double @[], x2188 @Natural @Double @[], x2189 @Natural @Double @[]] = tproject2 h2137 in x2188, let [x2190 @Natural @Double @[], x2191 @Natural @Double @[], x2192 @Natural @Double @[], x2193 @Natural @Double @[]] = tproject2 h2137 in x2193] ; x2197 = cos (let [x2195 @Natural @Double @[], x2196 @Natural @Double @[]] = h2194 in x2196) ; x2198 = x2197 * x2197 ; x2204 = negate (recip (x2198 * x2198)) * (let [x2199 @Natural @Double @[], x2200 @Natural @Double @[], x2201 @Natural @Double @[], x2202 @Natural @Double @[]] = tproject2 h2137 in x2200 * let [x2203 @Natural @Double @[]] = tproject1 h2137 in x2203) in [let [x2205 @Natural @Double @[]] = tproject1 h2137 in x2205, recip x2198 * let [x2206 @Natural @Double @[]] = tproject1 h2137 in x2206, 0, negate (sin (let [x2207 @Natural @Double @[], x2208 @Natural @Double @[]] = h2194 in x2208)) * (x2197 * x2204 + x2197 * x2204)]) [let [x1985 @Natural @Double @[], x1986 @Natural @Double @[]] = tproject1 h1957 in x1986] [rreplicate 22 (let [x1987 @Natural @Double @[], x1988 @Natural @Double @[]] = tproject1 h1957 in x1987), let [x1993 @Natural @Double @[], v1994 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h2209 -> let [x2223 @Natural @Double @[]] = tproject1 h2209 in let [x2226 @Natural @Double @[]] = let [x2224 @Natural @Double @[]] = tproject1 h2209 in let [x2225 @Natural @Double @[]] = tproject2 h2209 in [x2224 + tan x2225] in [x2226, x2223]) (\\h2227 -> let [x2249 @Natural @Double @[], x2250 @Natural @Double @[]] = tproject1 h2227 in let x2253 = cos (let [x2251 @Natural @Double @[], x2252 @Natural @Double @[]] = tproject2 h2227 in x2252) in [let [x2254 @Natural @Double @[], x2255 @Natural @Double @[]] = tproject1 h2227 in x2254 + let [x2256 @Natural @Double @[], x2257 @Natural @Double @[]] = tproject1 h2227 in x2257 * recip (x2253 * x2253), x2249]) (\\h2258 -> let [x2281 @Natural @Double @[], x2282 @Natural @Double @[]] = tproject1 h2258 in let x2285 = cos (let [x2283 @Natural @Double @[], x2284 @Natural @Double @[]] = tproject2 h2258 in x2284) in [x2281 + x2282, recip (x2285 * x2285) * x2281]) [let [x1989 @Natural @Double @[], x1990 @Natural @Double @[]] = tproject2 h1957 in x1990] [rreplicate 22 (let [x1991 @Natural @Double @[], x1992 @Natural @Double @[]] = tproject2 h1957 in x1991)] in v1994, rreplicate 22 (let [x1995 @Natural @Double @[], x1996 @Natural @Double @[]] = tproject2 h1957 in x1995)] in x1997, x1983]) (\\h2286 -> let [x2306 @Natural @Double @[], x2307 @Natural @Double @[]] = tproject1 h2286 in let h2316 = dmapAccumRDer (SNat @22) (\\h2323 -> let [x2329 @Natural @Double @[]] = tproject1 h2323 in let [x2330 @Natural @Double @[], x2331 @Natural @Double @[]] = tproject2 h2323 in let x2332 = cos x2331 in [x2329, recip (x2332 * x2332) * x2329]) (\\h2333 -> let h2367 = [let [x2361 @Natural @Double @[], x2362 @Natural @Double @[], x2363 @Natural @Double @[]] = tproject2 h2333 in x2362, let [x2364 @Natural @Double @[], x2365 @Natural @Double @[], x2366 @Natural @Double @[]] = tproject2 h2333 in x2366] ; x2370 = cos (let [x2368 @Natural @Double @[], x2369 @Natural @Double @[]] = h2367 in x2369) ; x2371 = x2370 * x2370 ; x2377 = let [x2372 @Natural @Double @[], x2373 @Natural @Double @[], x2374 @Natural @Double @[]] = tproject1 h2333 in x2374 * negate (sin (let [x2375 @Natural @Double @[], x2376 @Natural @Double @[]] = h2367 in x2376)) in [let [x2378 @Natural @Double @[], x2379 @Natural @Double @[], x2380 @Natural @Double @[]] = tproject1 h2333 in x2378, ((x2377 * x2370 + x2377 * x2370) * negate (recip (x2371 * x2371))) * let [x2381 @Natural @Double @[], x2382 @Natural @Double @[], x2383 @Natural @Double @[]] = tproject2 h2333 in x2381 + let [x2384 @Natural @Double @[], x2385 @Natural @Double @[], x2386 @Natural @Double @[]] = tproject1 h2333 in x2384 * recip x2371]) (\\h2387 -> let h2418 = [let [x2412 @Natural @Double @[], x2413 @Natural @Double @[], x2414 @Natural @Double @[]] = tproject2 h2387 in x2413, let [x2415 @Natural @Double @[], x2416 @Natural @Double @[], x2417 @Natural @Double @[]] = tproject2 h2387 in x2417] ; x2421 = cos (let [x2419 @Natural @Double @[], x2420 @Natural @Double @[]] = h2418 in x2420) ; x2422 = x2421 * x2421 ; x2428 = negate (recip (x2422 * x2422)) * (let [x2423 @Natural @Double @[], x2424 @Natural @Double @[], x2425 @Natural @Double @[]] = tproject2 h2387 in x2423 * let [x2426 @Natural @Double @[], x2427 @Natural @Double @[]] = tproject1 h2387 in x2427) in [recip x2422 * let [x2429 @Natural @Double @[], x2430 @Natural @Double @[]] = tproject1 h2387 in x2430 + let [x2431 @Natural @Double @[], x2432 @Natural @Double @[]] = tproject1 h2387 in x2431, 0, negate (sin (let [x2433 @Natural @Double @[], x2434 @Natural @Double @[]] = h2418 in x2434)) * (x2421 * x2428 + x2421 * x2428)]) [x2306] [let [x2312 @Natural @Double @[], v2313 @Natural @Double @[22]] = dmapAccumLDer (SNat @22) (\\h2435 -> let [x2441 @Natural @Double @[]] = tproject1 h2435 in let [x2444 @Natural @Double @[]] = let [x2442 @Natural @Double @[]] = tproject1 h2435 in let [x2443 @Natural @Double @[]] = tproject2 h2435 in [x2442 + tan x2443] in [x2444, x2441]) (\\h2445 -> let [x2456 @Natural @Double @[], x2457 @Natural @Double @[]] = tproject1 h2445 in let x2460 = cos (let [x2458 @Natural @Double @[], x2459 @Natural @Double @[]] = tproject2 h2445 in x2459) in [let [x2461 @Natural @Double @[], x2462 @Natural @Double @[]] = tproject1 h2445 in x2461 + let [x2463 @Natural @Double @[], x2464 @Natural @Double @[]] = tproject1 h2445 in x2464 * recip (x2460 * x2460), x2456]) (\\h2465 -> let [x2472 @Natural @Double @[], x2473 @Natural @Double @[]] = tproject1 h2465 in let x2476 = cos (let [x2474 @Natural @Double @[], x2475 @Natural @Double @[]] = tproject2 h2465 in x2475) in [x2472 + x2473, recip (x2476 * x2476) * x2472]) [let [x2308 @Natural @Double @[], x2309 @Natural @Double @[]] = tproject2 h2286 in x2309] [rreplicate 22 (let [x2310 @Natural @Double @[], x2311 @Natural @Double @[]] = tproject2 h2286 in x2310)] in v2313, rreplicate 22 (let [x2314 @Natural @Double @[], x2315 @Natural @Double @[]] = tproject2 h2286 in x2314)] in [rsum (let [x2317 @Natural @Double @[], v2318 @Natural @Double @[22]] = h2316 in v2318) + x2307, let [x2320 @Natural @Double @[], v2321 @Natural @Double @[22]] = h2316 in x2320]) [1.1] [rreplicate 11 1.1] in v11, rreplicate 11 1.1] in [rsum (let [x14 @Natural @Double @[], v15 @Natural @Double @[11]] = h13 in v15) + let [x16 @Natural @Double @[], v17 @Natural @Double @[11]] = h13 in x16]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyInline
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4_471

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
      IM.empty
      (simplifyInline
       $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 54_457

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
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 738_959

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
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11_819_579

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
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
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
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
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
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 -> let y = rfromD @Double @0 $ x2 V.! 0
                                    w = rfromD @Double @0 $ a2 V.! 0
                                in dmkHVector $ V.singleton
                                   $ DynamicRanked $ y + tan w)
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  printAstHVectorPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h12 = dmapAccumRDer (SNat @2) (\\h17 -> let [x44 @Natural @Double @[]] = tproject1 h17 in let [x45 @Natural @Double @[], x46 @Natural @Double @[]] = tproject2 h17 in let h47 = [x45, x46] ; h56 = dmapAccumRDer (SNat @2) (\\h61 -> let [x83 @Natural @Double @[]] = tproject1 h61 in let [x84 @Natural @Double @[], x85 @Natural @Double @[]] = tproject2 h61 in let x86 = cos x85 in [x83, recip (x86 * x86) * x83]) (\\h87 -> let h142 = [let [x136 @Natural @Double @[], x137 @Natural @Double @[], x138 @Natural @Double @[]] = tproject2 h87 in x137, let [x139 @Natural @Double @[], x140 @Natural @Double @[], x141 @Natural @Double @[]] = tproject2 h87 in x141] ; x145 = cos (let [x143 @Natural @Double @[], x144 @Natural @Double @[]] = h142 in x144) ; x146 = x145 * x145 ; x152 = let [x147 @Natural @Double @[], x148 @Natural @Double @[], x149 @Natural @Double @[]] = tproject1 h87 in x149 * negate (sin (let [x150 @Natural @Double @[], x151 @Natural @Double @[]] = h142 in x151)) in [let [x153 @Natural @Double @[], x154 @Natural @Double @[], x155 @Natural @Double @[]] = tproject1 h87 in x153, ((x152 * x145 + x152 * x145) * negate (recip (x146 * x146))) * let [x156 @Natural @Double @[], x157 @Natural @Double @[], x158 @Natural @Double @[]] = tproject2 h87 in x156 + let [x159 @Natural @Double @[], x160 @Natural @Double @[], x161 @Natural @Double @[]] = tproject1 h87 in x159 * recip x146]) (\\h162 -> let h211 = [let [x205 @Natural @Double @[], x206 @Natural @Double @[], x207 @Natural @Double @[]] = tproject2 h162 in x206, let [x208 @Natural @Double @[], x209 @Natural @Double @[], x210 @Natural @Double @[]] = tproject2 h162 in x210] ; x214 = cos (let [x212 @Natural @Double @[], x213 @Natural @Double @[]] = h211 in x213) ; x215 = x214 * x214 ; x221 = negate (recip (x215 * x215)) * (let [x216 @Natural @Double @[], x217 @Natural @Double @[], x218 @Natural @Double @[]] = tproject2 h162 in x216 * let [x219 @Natural @Double @[], x220 @Natural @Double @[]] = tproject1 h162 in x220) in [recip x215 * let [x222 @Natural @Double @[], x223 @Natural @Double @[]] = tproject1 h162 in x223 + let [x224 @Natural @Double @[], x225 @Natural @Double @[]] = tproject1 h162 in x224, 0, negate (sin (let [x226 @Natural @Double @[], x227 @Natural @Double @[]] = h211 in x227)) * (x214 * x221 + x214 * x221)]) [x44] [let [x52 @Natural @Double @[], v53 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h228 -> let [x242 @Natural @Double @[]] = tproject1 h228 in let [x245 @Natural @Double @[]] = let [x243 @Natural @Double @[]] = tproject1 h228 in let [x244 @Natural @Double @[]] = tproject2 h228 in [x243 + tan x244] in [x245, x242]) (\\h246 -> let [x276 @Natural @Double @[], x277 @Natural @Double @[]] = tproject1 h246 in let x280 = cos (let [x278 @Natural @Double @[], x279 @Natural @Double @[]] = tproject2 h246 in x279) in [let [x281 @Natural @Double @[], x282 @Natural @Double @[]] = tproject1 h246 in x281 + let [x283 @Natural @Double @[], x284 @Natural @Double @[]] = tproject1 h246 in x284 * recip (x280 * x280), x276]) (\\h285 -> let [x302 @Natural @Double @[], x303 @Natural @Double @[]] = tproject1 h285 in let x306 = cos (let [x304 @Natural @Double @[], x305 @Natural @Double @[]] = tproject2 h285 in x305) in [x302 + x303, recip (x306 * x306) * x302]) [let [x48 @Natural @Double @[], x49 @Natural @Double @[]] = h47 in x49] [rreplicate 2 (let [x50 @Natural @Double @[], x51 @Natural @Double @[]] = h47 in x50)] in v53, rreplicate 2 (let [x54 @Natural @Double @[], x55 @Natural @Double @[]] = h47 in x54)] in [rsum (let [x57 @Natural @Double @[], v58 @Natural @Double @[2]] = h56 in v58), let [x59 @Natural @Double @[], v60 @Natural @Double @[2]] = h56 in x59]) (\\h307 -> let h344 = [let [x338 @Natural @Double @[], x339 @Natural @Double @[], x340 @Natural @Double @[]] = tproject2 h307 in x339, let [x341 @Natural @Double @[], x342 @Natural @Double @[], x343 @Natural @Double @[]] = tproject2 h307 in x343] ; h349 = dmapAccumLDer (SNat @2) (\\h390 -> let [x404 @Natural @Double @[]] = tproject1 h390 in let [x409 @Natural @Double @[], x410 @Natural @Double @[]] = let [x405 @Natural @Double @[]] = tproject1 h390 in let [x408 @Natural @Double @[]] = let [x406 @Natural @Double @[]] = tproject1 h390 in let [x407 @Natural @Double @[]] = tproject2 h390 in [x406 + tan x407] in [x408, x405] in [x409, x404, x410]) (\\h411 -> let [x436 @Natural @Double @[], x437 @Natural @Double @[]] = tproject1 h411 in let [x447 @Natural @Double @[], x448 @Natural @Double @[]] = let [x438 @Natural @Double @[], x439 @Natural @Double @[]] = tproject1 h411 in let x442 = cos (let [x440 @Natural @Double @[], x441 @Natural @Double @[]] = tproject2 h411 in x441) in [let [x443 @Natural @Double @[], x444 @Natural @Double @[]] = tproject1 h411 in x443 + let [x445 @Natural @Double @[], x446 @Natural @Double @[]] = tproject1 h411 in x446 * recip (x442 * x442), x438] in [x447, x436, x448]) (\\h449 -> let [x467 @Natural @Double @[], x468 @Natural @Double @[], x469 @Natural @Double @[]] = tproject1 h449 in let x472 = cos (let [x470 @Natural @Double @[], x471 @Natural @Double @[]] = tproject2 h449 in x471) in [x468 + x467 + x469, recip (x472 * x472) * x467]) [let [x345 @Natural @Double @[], x346 @Natural @Double @[]] = h344 in x346] [rreplicate 2 (let [x347 @Natural @Double @[], x348 @Natural @Double @[]] = h344 in x347)] ; h355 = [let [x350 @Natural @Double @[], v351 @Natural @Double @[2], v352 @Natural @Double @[2]] = h349 in v352, rreplicate 2 (let [x353 @Natural @Double @[], x354 @Natural @Double @[]] = h344 in x353)] ; h385 = dmapAccumRDer (SNat @2) (\\h473 -> let [x534 @Natural @Double @[]] = tproject1 h473 in let [x535 @Natural @Double @[], x536 @Natural @Double @[], x537 @Natural @Double @[], x538 @Natural @Double @[], x539 @Natural @Double @[]] = tproject2 h473 in let h540 = [x538, x539] ; x543 = cos (let [x541 @Natural @Double @[], x542 @Natural @Double @[]] = h540 in x542) ; x544 = x543 * x543 ; x547 = x536 * negate (sin (let [x545 @Natural @Double @[], x546 @Natural @Double @[]] = h540 in x546)) in [x534, ((x547 * x543 + x547 * x543) * negate (recip (x544 * x544))) * x537 + x534 * recip x544]) (\\h548 -> let h624 = [let [x612 @Natural @Double @[], x613 @Natural @Double @[], x614 @Natural @Double @[], x615 @Natural @Double @[], x616 @Natural @Double @[], x617 @Natural @Double @[]] = tproject2 h548 in x616, let [x618 @Natural @Double @[], x619 @Natural @Double @[], x620 @Natural @Double @[], x621 @Natural @Double @[], x622 @Natural @Double @[], x623 @Natural @Double @[]] = tproject2 h548 in x623] ; x627 = cos (let [x625 @Natural @Double @[], x626 @Natural @Double @[]] = h624 in x626) ; x628 = x627 * x627 ; x631 = negate (sin (let [x629 @Natural @Double @[], x630 @Natural @Double @[]] = h624 in x630)) ; x638 = let [x632 @Natural @Double @[], x633 @Natural @Double @[], x634 @Natural @Double @[], x635 @Natural @Double @[], x636 @Natural @Double @[], x637 @Natural @Double @[]] = tproject2 h548 in x634 * x631 ; x639 = x628 * x628 ; x640 = x638 * x627 + x638 * x627 ; x641 = negate (recip x639) ; x662 = let [x642 @Natural @Double @[], x643 @Natural @Double @[], x644 @Natural @Double @[], x645 @Natural @Double @[], x646 @Natural @Double @[], x647 @Natural @Double @[]] = tproject1 h548 in x644 * x631 + ((let [x648 @Natural @Double @[], x649 @Natural @Double @[], x650 @Natural @Double @[], x651 @Natural @Double @[], x652 @Natural @Double @[], x653 @Natural @Double @[]] = tproject1 h548 in x653 * cos (let [x654 @Natural @Double @[], x655 @Natural @Double @[]] = h624 in x655)) * -1.0) * let [x656 @Natural @Double @[], x657 @Natural @Double @[], x658 @Natural @Double @[], x659 @Natural @Double @[], x660 @Natural @Double @[], x661 @Natural @Double @[]] = tproject2 h548 in x658 ; x671 = let [x663 @Natural @Double @[], x664 @Natural @Double @[], x665 @Natural @Double @[], x666 @Natural @Double @[], x667 @Natural @Double @[], x668 @Natural @Double @[]] = tproject1 h548 in x668 * negate (sin (let [x669 @Natural @Double @[], x670 @Natural @Double @[]] = h624 in x670)) ; x672 = x671 * x627 + x671 * x627 in [let [x673 @Natural @Double @[], x674 @Natural @Double @[], x675 @Natural @Double @[], x676 @Natural @Double @[], x677 @Natural @Double @[], x678 @Natural @Double @[]] = tproject1 h548 in x673, ((x662 * x627 + x671 * x638 + x662 * x627 + x671 * x638) * x641 + (((x672 * x628 + x672 * x628) * negate (recip (x639 * x639))) * -1.0) * x640) * let [x679 @Natural @Double @[], x680 @Natural @Double @[], x681 @Natural @Double @[], x682 @Natural @Double @[], x683 @Natural @Double @[], x684 @Natural @Double @[]] = tproject2 h548 in x682 + let [x685 @Natural @Double @[], x686 @Natural @Double @[], x687 @Natural @Double @[], x688 @Natural @Double @[], x689 @Natural @Double @[], x690 @Natural @Double @[]] = tproject1 h548 in x688 * (x640 * x641) + let [x691 @Natural @Double @[], x692 @Natural @Double @[], x693 @Natural @Double @[], x694 @Natural @Double @[], x695 @Natural @Double @[], x696 @Natural @Double @[]] = tproject1 h548 in x691 * recip x628 + (x672 * negate (recip (x628 * x628))) * let [x697 @Natural @Double @[], x698 @Natural @Double @[], x699 @Natural @Double @[], x700 @Natural @Double @[], x701 @Natural @Double @[], x702 @Natural @Double @[]] = tproject2 h548 in x697]) (\\h703 -> let h768 = [let [x756 @Natural @Double @[], x757 @Natural @Double @[], x758 @Natural @Double @[], x759 @Natural @Double @[], x760 @Natural @Double @[], x761 @Natural @Double @[]] = tproject2 h703 in x760, let [x762 @Natural @Double @[], x763 @Natural @Double @[], x764 @Natural @Double @[], x765 @Natural @Double @[], x766 @Natural @Double @[], x767 @Natural @Double @[]] = tproject2 h703 in x767] ; x771 = cos (let [x769 @Natural @Double @[], x770 @Natural @Double @[]] = h768 in x770) ; x772 = x771 * x771 ; x775 = negate (sin (let [x773 @Natural @Double @[], x774 @Natural @Double @[]] = h768 in x774)) ; x782 = let [x776 @Natural @Double @[], x777 @Natural @Double @[], x778 @Natural @Double @[], x779 @Natural @Double @[], x780 @Natural @Double @[], x781 @Natural @Double @[]] = tproject2 h703 in x778 * x775 ; x783 = x772 * x772 ; x784 = x782 * x771 + x782 * x771 ; x785 = negate (recip x783) ; x794 = let [x786 @Natural @Double @[], x787 @Natural @Double @[], x788 @Natural @Double @[], x789 @Natural @Double @[], x790 @Natural @Double @[], x791 @Natural @Double @[]] = tproject2 h703 in x789 * let [x792 @Natural @Double @[], x793 @Natural @Double @[]] = tproject1 h703 in x793 ; x795 = negate (recip (x783 * x783)) * (-1.0 * (x784 * x794)) ; x796 = x785 * x794 ; x797 = x771 * x796 + x771 * x796 ; x806 = x772 * x795 + x772 * x795 + negate (recip (x772 * x772)) * (let [x798 @Natural @Double @[], x799 @Natural @Double @[], x800 @Natural @Double @[], x801 @Natural @Double @[], x802 @Natural @Double @[], x803 @Natural @Double @[]] = tproject2 h703 in x798 * let [x804 @Natural @Double @[], x805 @Natural @Double @[]] = tproject1 h703 in x805) in [recip x772 * let [x807 @Natural @Double @[], x808 @Natural @Double @[]] = tproject1 h703 in x808 + let [x809 @Natural @Double @[], x810 @Natural @Double @[]] = tproject1 h703 in x809, 0, x775 * x797, (x784 * x785) * let [x811 @Natural @Double @[], x812 @Natural @Double @[]] = tproject1 h703 in x812, 0, negate (sin (let [x813 @Natural @Double @[], x814 @Natural @Double @[]] = h768 in x814)) * (x771 * x806 + x771 * x806 + x782 * x796 + x782 * x796) + cos (let [x815 @Natural @Double @[], x816 @Natural @Double @[]] = h768 in x816) * (-1.0 * (let [x817 @Natural @Double @[], x818 @Natural @Double @[], x819 @Natural @Double @[], x820 @Natural @Double @[], x821 @Natural @Double @[], x822 @Natural @Double @[]] = tproject2 h703 in x819 * x797))]) [let [x356 @Natural @Double @[], x357 @Natural @Double @[], x358 @Natural @Double @[]] = tproject1 h307 in x356] [let [x370 @Natural @Double @[], v371 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h823 -> let [x838 @Natural @Double @[]] = tproject1 h823 in let [x839 @Natural @Double @[], x840 @Natural @Double @[], x841 @Natural @Double @[]] = tproject2 h823 in let x842 = cos x841 in [x838 + x839 * recip (x842 * x842), x838]) (\\h843 -> let x872 = cos (let [x868 @Natural @Double @[], x869 @Natural @Double @[], x870 @Natural @Double @[], x871 @Natural @Double @[]] = tproject2 h843 in x871) ; x873 = x872 * x872 ; x882 = let [x874 @Natural @Double @[], x875 @Natural @Double @[], x876 @Natural @Double @[], x877 @Natural @Double @[]] = tproject1 h843 in x877 * negate (sin (let [x878 @Natural @Double @[], x879 @Natural @Double @[], x880 @Natural @Double @[], x881 @Natural @Double @[]] = tproject2 h843 in x881)) in [let [x883 @Natural @Double @[], x884 @Natural @Double @[], x885 @Natural @Double @[], x886 @Natural @Double @[]] = tproject1 h843 in x883 + let [x887 @Natural @Double @[], x888 @Natural @Double @[], x889 @Natural @Double @[], x890 @Natural @Double @[]] = tproject1 h843 in x888 * recip x873 + ((x882 * x872 + x882 * x872) * negate (recip (x873 * x873))) * let [x891 @Natural @Double @[], x892 @Natural @Double @[], x893 @Natural @Double @[], x894 @Natural @Double @[]] = tproject2 h843 in x892, let [x895 @Natural @Double @[], x896 @Natural @Double @[], x897 @Natural @Double @[], x898 @Natural @Double @[]] = tproject1 h843 in x895]) (\\h899 -> let x924 = cos (let [x920 @Natural @Double @[], x921 @Natural @Double @[], x922 @Natural @Double @[], x923 @Natural @Double @[]] = tproject2 h899 in x923) ; x925 = x924 * x924 ; x932 = negate (recip (x925 * x925)) * (let [x926 @Natural @Double @[], x927 @Natural @Double @[], x928 @Natural @Double @[], x929 @Natural @Double @[]] = tproject2 h899 in x927 * let [x930 @Natural @Double @[], x931 @Natural @Double @[]] = tproject1 h899 in x930) in [let [x933 @Natural @Double @[], x934 @Natural @Double @[]] = tproject1 h899 in x933 + let [x935 @Natural @Double @[], x936 @Natural @Double @[]] = tproject1 h899 in x936, recip x925 * let [x937 @Natural @Double @[], x938 @Natural @Double @[]] = tproject1 h899 in x937, 0, negate (sin (let [x939 @Natural @Double @[], x940 @Natural @Double @[], x941 @Natural @Double @[], x942 @Natural @Double @[]] = tproject2 h899 in x942)) * (x924 * x932 + x924 * x932)]) [let [x359 @Natural @Double @[], x360 @Natural @Double @[], x361 @Natural @Double @[]] = tproject1 h307 in x361] [rreplicate 2 (let [x362 @Natural @Double @[], x363 @Natural @Double @[], x364 @Natural @Double @[]] = tproject1 h307 in x363), let [x365 @Natural @Double @[], v366 @Natural @Double @[2], v367 @Natural @Double @[2]] = h349 in v366, rreplicate 2 (let [x368 @Natural @Double @[], x369 @Natural @Double @[]] = h344 in x368)] in v371, rreplicate 2 (let [x372 @Natural @Double @[], x373 @Natural @Double @[], x374 @Natural @Double @[]] = tproject1 h307 in x373), let [x378 @Natural @Double @[], v379 @Natural @Double @[2], v380 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h943 -> let [x957 @Natural @Double @[]] = tproject1 h943 in let [x962 @Natural @Double @[], x963 @Natural @Double @[]] = let [x958 @Natural @Double @[]] = tproject1 h943 in let [x959 @Natural @Double @[], x960 @Natural @Double @[]] = tproject2 h943 in let x961 = cos x960 in [x958, recip (x961 * x961) * x958] in [x962, x957, x963]) (\\h964 -> let [x997 @Natural @Double @[], x998 @Natural @Double @[], x999 @Natural @Double @[]] = tproject1 h964 in let h1006 = [let [x1000 @Natural @Double @[], x1001 @Natural @Double @[], x1002 @Natural @Double @[]] = tproject2 h964 in x1001, let [x1003 @Natural @Double @[], x1004 @Natural @Double @[], x1005 @Natural @Double @[]] = tproject2 h964 in x1005] ; x1009 = cos (let [x1007 @Natural @Double @[], x1008 @Natural @Double @[]] = h1006 in x1008) ; x1010 = x1009 * x1009 ; x1016 = let [x1011 @Natural @Double @[], x1012 @Natural @Double @[], x1013 @Natural @Double @[]] = tproject1 h964 in x1013 * negate (sin (let [x1014 @Natural @Double @[], x1015 @Natural @Double @[]] = h1006 in x1015)) in [let [x1017 @Natural @Double @[], x1018 @Natural @Double @[], x1019 @Natural @Double @[]] = tproject1 h964 in x1017, x997, ((x1016 * x1009 + x1016 * x1009) * negate (recip (x1010 * x1010))) * let [x1020 @Natural @Double @[], x1021 @Natural @Double @[], x1022 @Natural @Double @[]] = tproject2 h964 in x1020 + let [x1023 @Natural @Double @[], x1024 @Natural @Double @[], x1025 @Natural @Double @[]] = tproject1 h964 in x1023 * recip x1010]) (\\h1026 -> let [x1081 @Natural @Double @[], x1082 @Natural @Double @[], x1083 @Natural @Double @[]] = tproject1 h1026 in let h1090 = [let [x1084 @Natural @Double @[], x1085 @Natural @Double @[], x1086 @Natural @Double @[]] = tproject2 h1026 in x1085, let [x1087 @Natural @Double @[], x1088 @Natural @Double @[], x1089 @Natural @Double @[]] = tproject2 h1026 in x1089] ; x1093 = cos (let [x1091 @Natural @Double @[], x1092 @Natural @Double @[]] = h1090 in x1092) ; x1094 = x1093 * x1093 ; x1098 = negate (recip (x1094 * x1094)) * (let [x1095 @Natural @Double @[], x1096 @Natural @Double @[], x1097 @Natural @Double @[]] = tproject2 h1026 in x1095 * x1083) in [x1082 + recip x1094 * x1083 + x1081, 0.0, negate (sin (let [x1099 @Natural @Double @[], x1100 @Natural @Double @[]] = h1090 in x1100)) * (x1093 * x1098 + x1093 * x1098)]) [let [x375 @Natural @Double @[], x376 @Natural @Double @[], x377 @Natural @Double @[]] = tproject2 h307 in x375] h355 in v379, let [v381 @Natural @Double @[2], v382 @Natural @Double @[2]] = h355 in v381, let [v383 @Natural @Double @[2], v384 @Natural @Double @[2]] = h355 in v384] in [rsum (let [x386 @Natural @Double @[], v387 @Natural @Double @[2]] = h385 in v387), let [x388 @Natural @Double @[], v389 @Natural @Double @[2]] = h385 in x388]) (\\h1101 -> let h1141 = [let [x1135 @Natural @Double @[], x1136 @Natural @Double @[], x1137 @Natural @Double @[]] = tproject2 h1101 in x1136, let [x1138 @Natural @Double @[], x1139 @Natural @Double @[], x1140 @Natural @Double @[]] = tproject2 h1101 in x1140] ; h1146 = dmapAccumLDer (SNat @2) (\\h1207 -> let [x1221 @Natural @Double @[]] = tproject1 h1207 in let [x1226 @Natural @Double @[], x1227 @Natural @Double @[]] = let [x1222 @Natural @Double @[]] = tproject1 h1207 in let [x1225 @Natural @Double @[]] = let [x1223 @Natural @Double @[]] = tproject1 h1207 in let [x1224 @Natural @Double @[]] = tproject2 h1207 in [x1223 + tan x1224] in [x1225, x1222] in [x1226, x1221, x1227]) (\\h1228 -> let [x1253 @Natural @Double @[], x1254 @Natural @Double @[]] = tproject1 h1228 in let [x1264 @Natural @Double @[], x1265 @Natural @Double @[]] = let [x1255 @Natural @Double @[], x1256 @Natural @Double @[]] = tproject1 h1228 in let x1259 = cos (let [x1257 @Natural @Double @[], x1258 @Natural @Double @[]] = tproject2 h1228 in x1258) in [let [x1260 @Natural @Double @[], x1261 @Natural @Double @[]] = tproject1 h1228 in x1260 + let [x1262 @Natural @Double @[], x1263 @Natural @Double @[]] = tproject1 h1228 in x1263 * recip (x1259 * x1259), x1255] in [x1264, x1253, x1265]) (\\h1266 -> let [x1284 @Natural @Double @[], x1285 @Natural @Double @[], x1286 @Natural @Double @[]] = tproject1 h1266 in let x1289 = cos (let [x1287 @Natural @Double @[], x1288 @Natural @Double @[]] = tproject2 h1266 in x1288) in [x1285 + x1284 + x1286, recip (x1289 * x1289) * x1284]) [let [x1142 @Natural @Double @[], x1143 @Natural @Double @[]] = h1141 in x1143] [rreplicate 2 (let [x1144 @Natural @Double @[], x1145 @Natural @Double @[]] = h1141 in x1144)] ; h1152 = [let [x1147 @Natural @Double @[], v1148 @Natural @Double @[2], v1149 @Natural @Double @[2]] = h1146 in v1149, rreplicate 2 (let [x1150 @Natural @Double @[], x1151 @Natural @Double @[]] = h1141 in x1150)] ; h1155 = [let [x1153 @Natural @Double @[], x1154 @Natural @Double @[]] = tproject1 h1101 in x1154, 0] ; h1158 = [0, rreplicate 2 (let [x1156 @Natural @Double @[], x1157 @Natural @Double @[]] = tproject1 h1101 in x1156)] ; h1167 = [let [x1159 @Natural @Double @[], v1160 @Natural @Double @[2]] = h1158 in x1159 + let [x1161 @Natural @Double @[], v1162 @Natural @Double @[2]] = h1155 in x1161, let [x1163 @Natural @Double @[], v1164 @Natural @Double @[2]] = h1158 in v1164 + let [x1165 @Natural @Double @[], v1166 @Natural @Double @[2]] = h1155 in v1166] ; h1182 = dmapAccumLDer (SNat @2) (\\h1290 -> let [x1344 @Natural @Double @[]] = tproject1 h1290 in let [x1345 @Natural @Double @[], x1346 @Natural @Double @[], x1347 @Natural @Double @[], x1348 @Natural @Double @[]] = tproject2 h1290 in let h1349 = [x1347, x1348] ; x1352 = cos (let [x1350 @Natural @Double @[], x1351 @Natural @Double @[]] = h1349 in x1351) ; x1353 = x1352 * x1352 ; x1354 = negate (recip (x1353 * x1353)) * (x1346 * x1345) in [recip x1353 * x1345 + x1344, 0, negate (sin (let [x1355 @Natural @Double @[], x1356 @Natural @Double @[]] = h1349 in x1356)) * (x1352 * x1354 + x1352 * x1354)]) (\\h1357 -> let h1427 = [let [x1417 @Natural @Double @[], x1418 @Natural @Double @[], x1419 @Natural @Double @[], x1420 @Natural @Double @[], x1421 @Natural @Double @[]] = tproject2 h1357 in x1420, let [x1422 @Natural @Double @[], x1423 @Natural @Double @[], x1424 @Natural @Double @[], x1425 @Natural @Double @[], x1426 @Natural @Double @[]] = tproject2 h1357 in x1426] ; x1430 = cos (let [x1428 @Natural @Double @[], x1429 @Natural @Double @[]] = h1427 in x1429) ; x1431 = x1430 * x1430 ; x1432 = x1431 * x1431 ; x1433 = negate (recip x1432) ; x1444 = let [x1434 @Natural @Double @[], x1435 @Natural @Double @[], x1436 @Natural @Double @[], x1437 @Natural @Double @[], x1438 @Natural @Double @[]] = tproject2 h1357 in x1436 * let [x1439 @Natural @Double @[], x1440 @Natural @Double @[], x1441 @Natural @Double @[], x1442 @Natural @Double @[], x1443 @Natural @Double @[]] = tproject2 h1357 in x1440 ; x1445 = x1433 * x1444 ; x1453 = let [x1446 @Natural @Double @[], x1447 @Natural @Double @[], x1448 @Natural @Double @[], x1449 @Natural @Double @[], x1450 @Natural @Double @[]] = tproject1 h1357 in x1450 * negate (sin (let [x1451 @Natural @Double @[], x1452 @Natural @Double @[]] = h1427 in x1452)) ; x1454 = x1453 * x1430 + x1453 * x1430 ; x1475 = (((x1454 * x1431 + x1454 * x1431) * negate (recip (x1432 * x1432))) * -1.0) * x1444 + (let [x1455 @Natural @Double @[], x1456 @Natural @Double @[], x1457 @Natural @Double @[], x1458 @Natural @Double @[], x1459 @Natural @Double @[]] = tproject1 h1357 in x1457 * let [x1460 @Natural @Double @[], x1461 @Natural @Double @[], x1462 @Natural @Double @[], x1463 @Natural @Double @[], x1464 @Natural @Double @[]] = tproject2 h1357 in x1461 + let [x1465 @Natural @Double @[], x1466 @Natural @Double @[], x1467 @Natural @Double @[], x1468 @Natural @Double @[], x1469 @Natural @Double @[]] = tproject1 h1357 in x1466 * let [x1470 @Natural @Double @[], x1471 @Natural @Double @[], x1472 @Natural @Double @[], x1473 @Natural @Double @[], x1474 @Natural @Double @[]] = tproject2 h1357 in x1472) * x1433 in [let [x1476 @Natural @Double @[], x1477 @Natural @Double @[], x1478 @Natural @Double @[], x1479 @Natural @Double @[], x1480 @Natural @Double @[]] = tproject1 h1357 in x1476 + (x1454 * negate (recip (x1431 * x1431))) * let [x1481 @Natural @Double @[], x1482 @Natural @Double @[], x1483 @Natural @Double @[], x1484 @Natural @Double @[], x1485 @Natural @Double @[]] = tproject2 h1357 in x1482 + let [x1486 @Natural @Double @[], x1487 @Natural @Double @[], x1488 @Natural @Double @[], x1489 @Natural @Double @[], x1490 @Natural @Double @[]] = tproject1 h1357 in x1487 * recip x1431, 0.0, ((let [x1491 @Natural @Double @[], x1492 @Natural @Double @[], x1493 @Natural @Double @[], x1494 @Natural @Double @[], x1495 @Natural @Double @[]] = tproject1 h1357 in x1495 * cos (let [x1496 @Natural @Double @[], x1497 @Natural @Double @[]] = h1427 in x1497)) * -1.0) * (x1430 * x1445 + x1430 * x1445) + (x1453 * x1445 + x1475 * x1430 + x1453 * x1445 + x1475 * x1430) * negate (sin (let [x1498 @Natural @Double @[], x1499 @Natural @Double @[]] = h1427 in x1499))]) (\\h1500 -> let h1559 = [let [x1549 @Natural @Double @[], x1550 @Natural @Double @[], x1551 @Natural @Double @[], x1552 @Natural @Double @[], x1553 @Natural @Double @[]] = tproject2 h1500 in x1552, let [x1554 @Natural @Double @[], x1555 @Natural @Double @[], x1556 @Natural @Double @[], x1557 @Natural @Double @[], x1558 @Natural @Double @[]] = tproject2 h1500 in x1558] ; x1562 = cos (let [x1560 @Natural @Double @[], x1561 @Natural @Double @[]] = h1559 in x1561) ; x1563 = x1562 * x1562 ; x1564 = x1563 * x1563 ; x1565 = negate (recip x1564) ; x1576 = let [x1566 @Natural @Double @[], x1567 @Natural @Double @[], x1568 @Natural @Double @[], x1569 @Natural @Double @[], x1570 @Natural @Double @[]] = tproject2 h1500 in x1568 * let [x1571 @Natural @Double @[], x1572 @Natural @Double @[], x1573 @Natural @Double @[], x1574 @Natural @Double @[], x1575 @Natural @Double @[]] = tproject2 h1500 in x1572 ; x1577 = x1565 * x1576 ; x1583 = negate (sin (let [x1578 @Natural @Double @[], x1579 @Natural @Double @[]] = h1559 in x1579)) * let [x1580 @Natural @Double @[], x1581 @Natural @Double @[], x1582 @Natural @Double @[]] = tproject1 h1500 in x1582 ; x1584 = x1562 * x1583 + x1562 * x1583 ; x1585 = x1565 * x1584 ; x1586 = negate (recip (x1564 * x1564)) * (-1.0 * (x1576 * x1584)) ; x1595 = x1563 * x1586 + x1563 * x1586 + negate (recip (x1563 * x1563)) * (let [x1587 @Natural @Double @[], x1588 @Natural @Double @[], x1589 @Natural @Double @[], x1590 @Natural @Double @[], x1591 @Natural @Double @[]] = tproject2 h1500 in x1588 * let [x1592 @Natural @Double @[], x1593 @Natural @Double @[], x1594 @Natural @Double @[]] = tproject1 h1500 in x1592) in [let [x1596 @Natural @Double @[], x1597 @Natural @Double @[], x1598 @Natural @Double @[]] = tproject1 h1500 in x1596, let [x1599 @Natural @Double @[], x1600 @Natural @Double @[], x1601 @Natural @Double @[], x1602 @Natural @Double @[], x1603 @Natural @Double @[]] = tproject2 h1500 in x1601 * x1585 + recip x1563 * let [x1604 @Natural @Double @[], x1605 @Natural @Double @[], x1606 @Natural @Double @[]] = tproject1 h1500 in x1604, let [x1607 @Natural @Double @[], x1608 @Natural @Double @[], x1609 @Natural @Double @[], x1610 @Natural @Double @[], x1611 @Natural @Double @[]] = tproject2 h1500 in x1608 * x1585, 0, negate (sin (let [x1612 @Natural @Double @[], x1613 @Natural @Double @[]] = h1559 in x1613)) * (x1562 * x1595 + x1562 * x1595 + x1577 * x1583 + x1577 * x1583) + cos (let [x1614 @Natural @Double @[], x1615 @Natural @Double @[]] = h1559 in x1615) * (-1.0 * ((x1562 * x1577 + x1562 * x1577) * let [x1616 @Natural @Double @[], x1617 @Natural @Double @[], x1618 @Natural @Double @[]] = tproject1 h1500 in x1618))]) [let [x1168 @Natural @Double @[], v1169 @Natural @Double @[2]] = h1167 in x1168] [let [x1170 @Natural @Double @[], v1171 @Natural @Double @[2]] = h1167 in v1171, let [x1175 @Natural @Double @[], v1176 @Natural @Double @[2], v1177 @Natural @Double @[2]] = dmapAccumRDer (SNat @2) (\\h1619 -> let [x1633 @Natural @Double @[]] = tproject1 h1619 in let [x1638 @Natural @Double @[], x1639 @Natural @Double @[]] = let [x1634 @Natural @Double @[]] = tproject1 h1619 in let [x1635 @Natural @Double @[], x1636 @Natural @Double @[]] = tproject2 h1619 in let x1637 = cos x1636 in [x1634, recip (x1637 * x1637) * x1634] in [x1638, x1633, x1639]) (\\h1640 -> let [x1700 @Natural @Double @[], x1701 @Natural @Double @[], x1702 @Natural @Double @[]] = tproject1 h1640 in let h1709 = [let [x1703 @Natural @Double @[], x1704 @Natural @Double @[], x1705 @Natural @Double @[]] = tproject2 h1640 in x1704, let [x1706 @Natural @Double @[], x1707 @Natural @Double @[], x1708 @Natural @Double @[]] = tproject2 h1640 in x1708] ; x1712 = cos (let [x1710 @Natural @Double @[], x1711 @Natural @Double @[]] = h1709 in x1711) ; x1713 = x1712 * x1712 ; x1719 = let [x1714 @Natural @Double @[], x1715 @Natural @Double @[], x1716 @Natural @Double @[]] = tproject1 h1640 in x1716 * negate (sin (let [x1717 @Natural @Double @[], x1718 @Natural @Double @[]] = h1709 in x1718)) in [let [x1720 @Natural @Double @[], x1721 @Natural @Double @[], x1722 @Natural @Double @[]] = tproject1 h1640 in x1720, x1700, ((x1719 * x1712 + x1719 * x1712) * negate (recip (x1713 * x1713))) * let [x1723 @Natural @Double @[], x1724 @Natural @Double @[], x1725 @Natural @Double @[]] = tproject2 h1640 in x1723 + let [x1726 @Natural @Double @[], x1727 @Natural @Double @[], x1728 @Natural @Double @[]] = tproject1 h1640 in x1726 * recip x1713]) (\\h1729 -> let [x1760 @Natural @Double @[], x1761 @Natural @Double @[], x1762 @Natural @Double @[]] = tproject1 h1729 in let h1769 = [let [x1763 @Natural @Double @[], x1764 @Natural @Double @[], x1765 @Natural @Double @[]] = tproject2 h1729 in x1764, let [x1766 @Natural @Double @[], x1767 @Natural @Double @[], x1768 @Natural @Double @[]] = tproject2 h1729 in x1768] ; x1772 = cos (let [x1770 @Natural @Double @[], x1771 @Natural @Double @[]] = h1769 in x1771) ; x1773 = x1772 * x1772 ; x1777 = negate (recip (x1773 * x1773)) * (let [x1774 @Natural @Double @[], x1775 @Natural @Double @[], x1776 @Natural @Double @[]] = tproject2 h1729 in x1774 * x1762) in [x1761 + recip x1773 * x1762 + x1760, 0.0, negate (sin (let [x1778 @Natural @Double @[], x1779 @Natural @Double @[]] = h1769 in x1779)) * (x1772 * x1777 + x1772 * x1777)]) [let [x1172 @Natural @Double @[], x1173 @Natural @Double @[], x1174 @Natural @Double @[]] = tproject2 h1101 in x1172] h1152 in v1176, let [v1178 @Natural @Double @[2], v1179 @Natural @Double @[2]] = h1152 in v1178, let [v1180 @Natural @Double @[2], v1181 @Natural @Double @[2]] = h1152 in v1181] ; h1186 = [0, let [x1183 @Natural @Double @[], v1184 @Natural @Double @[2], v1185 @Natural @Double @[2]] = h1182 in v1184] ; h1196 = dmapAccumRDer (SNat @2) (\\h1780 -> let [x1791 @Natural @Double @[]] = tproject1 h1780 in let [x1792 @Natural @Double @[], x1793 @Natural @Double @[], x1794 @Natural @Double @[]] = tproject2 h1780 in let x1795 = cos x1794 in [x1791 + x1792, recip (x1795 * x1795) * x1791]) (\\h1796 -> let x1821 = cos (let [x1817 @Natural @Double @[], x1818 @Natural @Double @[], x1819 @Natural @Double @[], x1820 @Natural @Double @[]] = tproject2 h1796 in x1820) ; x1822 = x1821 * x1821 ; x1831 = let [x1823 @Natural @Double @[], x1824 @Natural @Double @[], x1825 @Natural @Double @[], x1826 @Natural @Double @[]] = tproject1 h1796 in x1826 * negate (sin (let [x1827 @Natural @Double @[], x1828 @Natural @Double @[], x1829 @Natural @Double @[], x1830 @Natural @Double @[]] = tproject2 h1796 in x1830)) in [let [x1832 @Natural @Double @[], x1833 @Natural @Double @[], x1834 @Natural @Double @[], x1835 @Natural @Double @[]] = tproject1 h1796 in x1832 + let [x1836 @Natural @Double @[], x1837 @Natural @Double @[], x1838 @Natural @Double @[], x1839 @Natural @Double @[]] = tproject1 h1796 in x1837, ((x1831 * x1821 + x1831 * x1821) * negate (recip (x1822 * x1822))) * let [x1840 @Natural @Double @[], x1841 @Natural @Double @[], x1842 @Natural @Double @[], x1843 @Natural @Double @[]] = tproject2 h1796 in x1840 + let [x1844 @Natural @Double @[], x1845 @Natural @Double @[], x1846 @Natural @Double @[], x1847 @Natural @Double @[]] = tproject1 h1796 in x1844 * recip x1822]) (\\h1848 -> let x1869 = cos (let [x1865 @Natural @Double @[], x1866 @Natural @Double @[], x1867 @Natural @Double @[], x1868 @Natural @Double @[]] = tproject2 h1848 in x1868) ; x1870 = x1869 * x1869 ; x1877 = negate (recip (x1870 * x1870)) * (let [x1871 @Natural @Double @[], x1872 @Natural @Double @[], x1873 @Natural @Double @[], x1874 @Natural @Double @[]] = tproject2 h1848 in x1871 * let [x1875 @Natural @Double @[], x1876 @Natural @Double @[]] = tproject1 h1848 in x1876) in [let [x1878 @Natural @Double @[], x1879 @Natural @Double @[]] = tproject1 h1848 in x1878 + recip x1870 * let [x1880 @Natural @Double @[], x1881 @Natural @Double @[]] = tproject1 h1848 in x1881, let [x1882 @Natural @Double @[], x1883 @Natural @Double @[]] = tproject1 h1848 in x1882, 0, negate (sin (let [x1884 @Natural @Double @[], x1885 @Natural @Double @[], x1886 @Natural @Double @[], x1887 @Natural @Double @[]] = tproject2 h1848 in x1887)) * (x1869 * x1877 + x1869 * x1877)]) [let [x1187 @Natural @Double @[], v1188 @Natural @Double @[2]] = h1186 in x1187] [let [x1189 @Natural @Double @[], v1190 @Natural @Double @[2]] = h1186 in v1190, let [x1191 @Natural @Double @[], v1192 @Natural @Double @[2], v1193 @Natural @Double @[2]] = h1146 in v1192, rreplicate 2 (let [x1194 @Natural @Double @[], x1195 @Natural @Double @[]] = h1141 in x1194)] in [let [x1197 @Natural @Double @[], v1198 @Natural @Double @[2], v1199 @Natural @Double @[2]] = h1182 in x1197, rsum (let [x1200 @Natural @Double @[], v1201 @Natural @Double @[2]] = h1196 in v1201) + rsum (let [x1202 @Natural @Double @[], v1203 @Natural @Double @[2], v1204 @Natural @Double @[2]] = h1182 in v1204), let [x1205 @Natural @Double @[], v1206 @Natural @Double @[2]] = h1196 in x1205]) [1.0] [let [x9 @Natural @Double @[], v10 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h1888 -> let [x1897 @Natural @Double @[]] = tproject1 h1888 in let [x1900 @Natural @Double @[]] = let [x1898 @Natural @Double @[]] = tproject1 h1888 in let [x1899 @Natural @Double @[]] = tproject2 h1888 in dmapAccumLDer (SNat @2) (\\h1901 -> let [x1908 @Natural @Double @[]] = tproject1 h1901 in let [x1909 @Natural @Double @[]] = tproject2 h1901 in [x1908 + tan x1909]) (\\h1910 -> let x1929 = cos (let [x1927 @Natural @Double @[], x1928 @Natural @Double @[]] = tproject2 h1910 in x1928) in [let [x1930 @Natural @Double @[], x1931 @Natural @Double @[]] = tproject1 h1910 in x1930 + let [x1932 @Natural @Double @[], x1933 @Natural @Double @[]] = tproject1 h1910 in x1933 * recip (x1929 * x1929)]) (\\h1934 -> let x1949 = cos (let [x1947 @Natural @Double @[], x1948 @Natural @Double @[]] = tproject2 h1934 in x1948) in [let [x1950 @Natural @Double @[]] = tproject1 h1934 in x1950, recip (x1949 * x1949) * let [x1951 @Natural @Double @[]] = tproject1 h1934 in x1951]) [x1899] [rreplicate 2 x1898] in [x1900, x1897]) (\\h1952 -> let [x1977 @Natural @Double @[], x1978 @Natural @Double @[]] = tproject1 h1952 in [let [x1991 @Natural @Double @[]] = dmapAccumLDer (SNat @2) (\\h1993 -> let [x2027 @Natural @Double @[]] = tproject1 h1993 in let [x2028 @Natural @Double @[], x2029 @Natural @Double @[], x2030 @Natural @Double @[]] = tproject2 h1993 in let h2031 = [x2027, x2028] ; x2032 = cos x2030 in [let [x2033 @Natural @Double @[], x2034 @Natural @Double @[]] = h2031 in x2033 + let [x2035 @Natural @Double @[], x2036 @Natural @Double @[]] = h2031 in x2036 * recip (x2032 * x2032)]) (\\h2037 -> let h2107 = [let [x2099 @Natural @Double @[], x2100 @Natural @Double @[], x2101 @Natural @Double @[], x2102 @Natural @Double @[]] = tproject2 h2037 in x2101, let [x2103 @Natural @Double @[], x2104 @Natural @Double @[], x2105 @Natural @Double @[], x2106 @Natural @Double @[]] = tproject2 h2037 in x2106] ; x2110 = cos (let [x2108 @Natural @Double @[], x2109 @Natural @Double @[]] = h2107 in x2109) ; x2111 = x2110 * x2110 ; x2118 = let [x2112 @Natural @Double @[], x2113 @Natural @Double @[], x2114 @Natural @Double @[], x2115 @Natural @Double @[]] = tproject1 h2037 in x2115 * negate (sin (let [x2116 @Natural @Double @[], x2117 @Natural @Double @[]] = h2107 in x2117)) in [let [x2119 @Natural @Double @[], x2120 @Natural @Double @[], x2121 @Natural @Double @[], x2122 @Natural @Double @[]] = tproject1 h2037 in x2119 + let [x2123 @Natural @Double @[], x2124 @Natural @Double @[], x2125 @Natural @Double @[], x2126 @Natural @Double @[]] = tproject1 h2037 in x2124 * recip x2111 + ((x2118 * x2110 + x2118 * x2110) * negate (recip (x2111 * x2111))) * let [x2127 @Natural @Double @[], x2128 @Natural @Double @[], x2129 @Natural @Double @[], x2130 @Natural @Double @[]] = tproject2 h2037 in x2128]) (\\h2131 -> let h2188 = [let [x2180 @Natural @Double @[], x2181 @Natural @Double @[], x2182 @Natural @Double @[], x2183 @Natural @Double @[]] = tproject2 h2131 in x2182, let [x2184 @Natural @Double @[], x2185 @Natural @Double @[], x2186 @Natural @Double @[], x2187 @Natural @Double @[]] = tproject2 h2131 in x2187] ; x2191 = cos (let [x2189 @Natural @Double @[], x2190 @Natural @Double @[]] = h2188 in x2190) ; x2192 = x2191 * x2191 ; x2198 = negate (recip (x2192 * x2192)) * (let [x2193 @Natural @Double @[], x2194 @Natural @Double @[], x2195 @Natural @Double @[], x2196 @Natural @Double @[]] = tproject2 h2131 in x2194 * let [x2197 @Natural @Double @[]] = tproject1 h2131 in x2197) in [let [x2199 @Natural @Double @[]] = tproject1 h2131 in x2199, recip x2192 * let [x2200 @Natural @Double @[]] = tproject1 h2131 in x2200, 0, negate (sin (let [x2201 @Natural @Double @[], x2202 @Natural @Double @[]] = h2188 in x2202)) * (x2191 * x2198 + x2191 * x2198)]) [let [x1979 @Natural @Double @[], x1980 @Natural @Double @[]] = tproject1 h1952 in x1980] [rreplicate 2 (let [x1981 @Natural @Double @[], x1982 @Natural @Double @[]] = tproject1 h1952 in x1981), let [x1987 @Natural @Double @[], v1988 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h2203 -> let [x2217 @Natural @Double @[]] = tproject1 h2203 in let [x2220 @Natural @Double @[]] = let [x2218 @Natural @Double @[]] = tproject1 h2203 in let [x2219 @Natural @Double @[]] = tproject2 h2203 in [x2218 + tan x2219] in [x2220, x2217]) (\\h2221 -> let [x2243 @Natural @Double @[], x2244 @Natural @Double @[]] = tproject1 h2221 in let x2247 = cos (let [x2245 @Natural @Double @[], x2246 @Natural @Double @[]] = tproject2 h2221 in x2246) in [let [x2248 @Natural @Double @[], x2249 @Natural @Double @[]] = tproject1 h2221 in x2248 + let [x2250 @Natural @Double @[], x2251 @Natural @Double @[]] = tproject1 h2221 in x2251 * recip (x2247 * x2247), x2243]) (\\h2252 -> let [x2275 @Natural @Double @[], x2276 @Natural @Double @[]] = tproject1 h2252 in let x2279 = cos (let [x2277 @Natural @Double @[], x2278 @Natural @Double @[]] = tproject2 h2252 in x2278) in [x2275 + x2276, recip (x2279 * x2279) * x2275]) [let [x1983 @Natural @Double @[], x1984 @Natural @Double @[]] = tproject2 h1952 in x1984] [rreplicate 2 (let [x1985 @Natural @Double @[], x1986 @Natural @Double @[]] = tproject2 h1952 in x1985)] in v1988, rreplicate 2 (let [x1989 @Natural @Double @[], x1990 @Natural @Double @[]] = tproject2 h1952 in x1989)] in x1991, x1977]) (\\h2280 -> let [x2300 @Natural @Double @[], x2301 @Natural @Double @[]] = tproject1 h2280 in let h2310 = dmapAccumRDer (SNat @2) (\\h2317 -> let [x2323 @Natural @Double @[]] = tproject1 h2317 in let [x2324 @Natural @Double @[], x2325 @Natural @Double @[]] = tproject2 h2317 in let x2326 = cos x2325 in [x2323, recip (x2326 * x2326) * x2323]) (\\h2327 -> let h2361 = [let [x2355 @Natural @Double @[], x2356 @Natural @Double @[], x2357 @Natural @Double @[]] = tproject2 h2327 in x2356, let [x2358 @Natural @Double @[], x2359 @Natural @Double @[], x2360 @Natural @Double @[]] = tproject2 h2327 in x2360] ; x2364 = cos (let [x2362 @Natural @Double @[], x2363 @Natural @Double @[]] = h2361 in x2363) ; x2365 = x2364 * x2364 ; x2371 = let [x2366 @Natural @Double @[], x2367 @Natural @Double @[], x2368 @Natural @Double @[]] = tproject1 h2327 in x2368 * negate (sin (let [x2369 @Natural @Double @[], x2370 @Natural @Double @[]] = h2361 in x2370)) in [let [x2372 @Natural @Double @[], x2373 @Natural @Double @[], x2374 @Natural @Double @[]] = tproject1 h2327 in x2372, ((x2371 * x2364 + x2371 * x2364) * negate (recip (x2365 * x2365))) * let [x2375 @Natural @Double @[], x2376 @Natural @Double @[], x2377 @Natural @Double @[]] = tproject2 h2327 in x2375 + let [x2378 @Natural @Double @[], x2379 @Natural @Double @[], x2380 @Natural @Double @[]] = tproject1 h2327 in x2378 * recip x2365]) (\\h2381 -> let h2412 = [let [x2406 @Natural @Double @[], x2407 @Natural @Double @[], x2408 @Natural @Double @[]] = tproject2 h2381 in x2407, let [x2409 @Natural @Double @[], x2410 @Natural @Double @[], x2411 @Natural @Double @[]] = tproject2 h2381 in x2411] ; x2415 = cos (let [x2413 @Natural @Double @[], x2414 @Natural @Double @[]] = h2412 in x2414) ; x2416 = x2415 * x2415 ; x2422 = negate (recip (x2416 * x2416)) * (let [x2417 @Natural @Double @[], x2418 @Natural @Double @[], x2419 @Natural @Double @[]] = tproject2 h2381 in x2417 * let [x2420 @Natural @Double @[], x2421 @Natural @Double @[]] = tproject1 h2381 in x2421) in [recip x2416 * let [x2423 @Natural @Double @[], x2424 @Natural @Double @[]] = tproject1 h2381 in x2424 + let [x2425 @Natural @Double @[], x2426 @Natural @Double @[]] = tproject1 h2381 in x2425, 0, negate (sin (let [x2427 @Natural @Double @[], x2428 @Natural @Double @[]] = h2412 in x2428)) * (x2415 * x2422 + x2415 * x2422)]) [x2300] [let [x2306 @Natural @Double @[], v2307 @Natural @Double @[2]] = dmapAccumLDer (SNat @2) (\\h2429 -> let [x2435 @Natural @Double @[]] = tproject1 h2429 in let [x2438 @Natural @Double @[]] = let [x2436 @Natural @Double @[]] = tproject1 h2429 in let [x2437 @Natural @Double @[]] = tproject2 h2429 in [x2436 + tan x2437] in [x2438, x2435]) (\\h2439 -> let [x2450 @Natural @Double @[], x2451 @Natural @Double @[]] = tproject1 h2439 in let x2454 = cos (let [x2452 @Natural @Double @[], x2453 @Natural @Double @[]] = tproject2 h2439 in x2453) in [let [x2455 @Natural @Double @[], x2456 @Natural @Double @[]] = tproject1 h2439 in x2455 + let [x2457 @Natural @Double @[], x2458 @Natural @Double @[]] = tproject1 h2439 in x2458 * recip (x2454 * x2454), x2450]) (\\h2459 -> let [x2466 @Natural @Double @[], x2467 @Natural @Double @[]] = tproject1 h2459 in let x2470 = cos (let [x2468 @Natural @Double @[], x2469 @Natural @Double @[]] = tproject2 h2459 in x2469) in [x2466 + x2467, recip (x2470 * x2470) * x2466]) [let [x2302 @Natural @Double @[], x2303 @Natural @Double @[]] = tproject2 h2280 in x2303] [rreplicate 2 (let [x2304 @Natural @Double @[], x2305 @Natural @Double @[]] = tproject2 h2280 in x2304)] in v2307, rreplicate 2 (let [x2308 @Natural @Double @[], x2309 @Natural @Double @[]] = tproject2 h2280 in x2308)] in [rsum (let [x2311 @Natural @Double @[], v2312 @Natural @Double @[2]] = h2310 in v2312) + x2301, let [x2314 @Natural @Double @[], v2315 @Natural @Double @[2]] = h2310 in x2314]) [1.1] [rreplicate 2 1.1] in v10, rreplicate 2 1.1] in [rsum (let [x13 @Natural @Double @[], v14 @Natural @Double @[2]] = h12 in v14) + let [x15 @Natural @Double @[], v16 @Natural @Double @[2]] = h12 in x15]"

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 -> let y = rfromD @Double @0 $ x4 V.! 0
                                        w = rfromD @Double @0 $ a4 V.! 0
                                    in dmkHVector $ V.singleton
                                       $ DynamicRanked $ y + tan w)
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZSR))
                 x
  length
    (printAstHVectorSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 11814321

testSin0MapAccumNestedR4 :: Assertion
testSin0MapAccumNestedR4 = do
 assertEqualUpToEpsilon' 1e-10
  (1.0410225027528066 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 -> let y = rfromD @Double @0 $ x5 V.! 0
                                          w = rfromD @Double @0 $ a5 V.! 0
                                      in dmkHVector $ V.singleton
                                         $ DynamicRanked $ rscalar 0.01 * y + tan w)
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001)

-- Takes 200s, probably due to some of the pipelines forcing all derivs.
_testSin0MapAccumNestedR5 :: Assertion
_testSin0MapAccumNestedR5 = do
 assertEqualUpToEpsilon' 1e-10
  (2.2173831481990922e20 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in dmkHVector $ V.singleton
                                           $ DynamicRanked $ y + tan w)
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 1.1)

testSin0MapAccumNestedR5r :: Assertion
testSin0MapAccumNestedR5r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.0837278549794862 :: ORArray Double 0)
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in dmkHVector $ V.singleton
                                           $ DynamicRanked $ rscalar 0.01 * y + tan w)
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10r :: Assertion
testSin0MapAccumNestedR10r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781 :: ORArray Double 0)
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ rscalar 0.01 * y + tan w)
                                       (HVectorPseudoTensor $ dmkHVector a10) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x10))
                                     (HVectorPseudoTensor $ dmkHVector a9) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x9))
                                   (HVectorPseudoTensor $ dmkHVector a8) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x8))
                                 (HVectorPseudoTensor $ dmkHVector a7) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x7))
                               (HVectorPseudoTensor $ dmkHVector a6) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x6))
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10f :: Assertion
testSin0MapAccumNestedR10f = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781e-4 :: ORArray Double 0)
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ rscalar 0.01 * y + tan w)
                                       (HVectorPseudoTensor $ dmkHVector a10) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x10))
                                     (HVectorPseudoTensor $ dmkHVector a9) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x9))
                                   (HVectorPseudoTensor $ dmkHVector a8) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x8))
                                 (HVectorPseudoTensor $ dmkHVector a7) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x7))
                               (HVectorPseudoTensor $ dmkHVector a6) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x6))
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10fN :: Assertion
testSin0MapAccumNestedR10fN = do
 assertEqualUpToEpsilon 1e-10
  ( srepl 1.379370673816781e-4 :: OSArray Float '[1]
  , rscalar 1.379370673816781e-4 :: ORArray Double 0)
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      g :: forall f. ADReady f => f Double 0 -> f Double 0
      g z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ rscalar 0.01 * y + tan w)
                                       (HVectorPseudoTensor $ dmkHVector a10) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x10))
                                     (HVectorPseudoTensor $ dmkHVector a9) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x9))
                                   (HVectorPseudoTensor $ dmkHVector a8) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x8))
                                 (HVectorPseudoTensor $ dmkHVector a7) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x7))
                               (HVectorPseudoTensor $ dmkHVector a6) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x6))
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      f :: forall f. ADReady f => f Double 0
        -> InterpretationTarget f (TKProduct (TKS Float '[1]) (TKR Double 0))
      f x = ttuple (sfromList [scast $ sfromR $ g x]) (g x + rscalar 0.2)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10rf :: Assertion
testSin0MapAccumNestedR10rf = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: ORArray Double 0)
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ rscalar 0.01 * y + tan w)
                                       (HVectorPseudoTensor $ dmkHVector a10) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x10))
                                     (HVectorPseudoTensor $ dmkHVector a9) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x9))
                                   (HVectorPseudoTensor $ dmkHVector a8) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x8))
                                 (HVectorPseudoTensor $ dmkHVector a7) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x7))
                               (HVectorPseudoTensor $ dmkHVector a6) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x6))
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rfwd1 f) (rscalar 0.0001))

testSin0MapAccumNestedR10rr :: Assertion
testSin0MapAccumNestedR10rr = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: ORArray Double 0)
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ unHVectorPseudoTensor $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                     unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 ->
                       unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                             (\x6 a6 ->
                         unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                               (\x7 a7 ->
                           unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                 (\x8 a8 ->
                             unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                   (\x9 a9 ->
                               unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                     (\x10 a10 ->
                                 unHVectorPseudoTensor $ dmapAccumL Proxy (SNat @2) shs1 she shs1
                                       (\x11 a11 ->
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in dmkHVector $ V.singleton
                                             $ DynamicRanked
                                             $ rscalar 0.01 * y + tan w)
                                       (HVectorPseudoTensor $ dmkHVector a10) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x10))
                                     (HVectorPseudoTensor $ dmkHVector a9) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x9))
                                   (HVectorPseudoTensor $ dmkHVector a8) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x8))
                                 (HVectorPseudoTensor $ dmkHVector a7) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x7))
                               (HVectorPseudoTensor $ dmkHVector a6) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x6))
                             (HVectorPseudoTensor $ dmkHVector a5) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x5))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
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
    @?= 148769

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. (LetTensor g (ShapedOf g))
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
  let f :: forall g. (LetTensor g (ShapedOf g))
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
  let f :: forall g. (LetTensor g (ShapedOf g))
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZSR))
             x
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
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
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[] (sscalar $ -0.8912073600614354))
    (crev (h @ORArray) (V.singleton $ DynamicShaped @Double @'[] (srepl 1.1)))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (LetTensor g (ShapedOf g), RankedTensor g, ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1 (rscanZip const doms 5)
               doms3 x (ringestData1 [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0])
    (crev (h @ORArray)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (LetTensor g (ShapedOf g), ShapedTensor (ShapedOf g), ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4] (sscanZip const doms (srepl 5))
               doms3 x (ingestData [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0])
    (crev (h @ORArray)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (LetTensor g (ShapedOf g), RankedTensor g, ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        rrevDt @g @_ @Double @1
               (\v -> rscanZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 v)
                doms3 x (ringestData1 [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ ringestData1 [4.0,6.0,8.0])
    (crev (h @ORArray)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (LetTensor g (ShapedOf g), ShapedTensor (ShapedOf g), ProductTensor g)
        => HVector g -> HVectorOf g
      f x =
        srevDt @g @_ @Double @'[4]
               (\v -> sscanZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms (srepl 5) v)
               doms3 x (ingestData [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [4.0,6.0,8.0])
    (crev (h @ORArray)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV8 :: Assertion
testSin0revhV8 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f = dmkHVector
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> HVectorPseudoTensor (ADVal g) Float '()
      h = HVectorPseudoTensor . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [1, 1, 1])
    (crev @_ @TKUntyped
          (h @ORArray)
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
        -> HVectorPseudoTensor (ADVal ranked) Float '()
      h = HVectorPseudoTensor . fFoldZipRX @(ADVal ORArray)
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
      h :: HVector (AstGeneric AstMethodLet FullSpan)
        -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
      h = g @(AstRanked FullSpan) . rankedHVector
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
    (rev (\(asD :: HVector (AstGeneric AstMethodLet FullSpan)) ->
             fFoldSX (sfromD (rankedHVector asD V.! 1)))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))

{-
testSin0revhFold5S :: Assertion
testSin0revhFold5S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ srepl (-7.313585321642452e-2) ])
    (rev (\(asD :: AstTensor AstMethodLet FullSpan TKUntyped) ->
            sletHVectorIn asD (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))
-}
