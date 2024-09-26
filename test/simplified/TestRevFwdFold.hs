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
  , testCase "4fooRrevPP2" testFooRrevPP2
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
  , testCase "4Sin0RfwdPP4Dual" testSin0RfwdPP4Dual
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
  , testCase "4Sin0FoldB1" testSin0FoldB1
  , testCase "4Sin0FoldB1PP" testSin0FoldB1PP
  , testCase "4Sin0FoldB2" testSin0FoldB2
  , testCase "4Sin0FoldB3" testSin0FoldB3
  , testCase "4Sin0FoldB4" testSin0FoldB4
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
  , testCase "4Sin0Fold182Srev" testSin0Fold182Srev
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
-- empty tensors ambiguity:  , testCase "4Sin0rmapAccumRD00S" testSin0rmapAccumRD00S
-- empty tensors ambiguity:  , testCase "4Sin0rmapAccumRD00S7" testSin0rmapAccumRD00S7
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
-- empty tensors ambiguity:  , testCase "4Sin0rmapAccumRD01SN531Slice" testSin0rmapAccumRD01SN531Slice
  , testCase "4Sin0rmapAccumRD01SN54" testSin0rmapAccumRD01SN54
-- empty tensors ambiguity:  , testCase "4Sin0rmapAccumRD01SN55" testSin0rmapAccumRD01SN55
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
-- takes too long:    , testCase "4Sin0FoldNestedR4LengthPPs" testSin0FoldNestedR4LengthPPs
-- takes too long:    , testCase "4Sin0FoldNestedR5LengthPPs" testSin0FoldNestedR5LengthPPs
  , testCase "4Sin0FoldNestedR2LengthPPsDummy7" testSin0FoldNestedR2LengthPPsDummy7
  , testCase "4Sin0FoldNestedR2Dummy7" testSin0FoldNestedR2Dummy7
  , testCase "4Sin0FoldNestedR2Tan" testSin0FoldNestedR2Tan
  , testCase "4Sin0MapAccumNestedR1PP" testSin0MapAccumNestedR1PP
  , testCase "4Sin0MapAccumNestedR3LengthPP" testSin0MapAccumNestedR3LengthPP
  , testCase "4Sin0MapAccumNestedR4" testSin0MapAccumNestedR4
  , testCase "4Sin0MapAccumNestedR5" testSin0MapAccumNestedR5
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
  , testCase "4Sin0FoldNestedS5" testSin0FoldNestedS5
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
-- TODO: see `instance AdaptableHVector (AstRanked s) (AstTensor AstMethodLet s TKUntyped)`:  , testCase "4Sin0revhFold5S" testSin0revhFold5S
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
  let (a1, _, _) = fooRrev @(AstRanked PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstPretty IM.empty a1
    @?= "let x61 = sin 2.2 ; x65 = 1.1 * x61 ; x66 = recip (3.3 * 3.3 + x65 * x65) ; x103 = sin 2.2 ; x108 = 3.3 * 1.0 ; x109 = (negate 3.3 * x66) * 1.0 in x61 * x109 + x103 * x108"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rlet (sin 2.2) (\\x191 -> rlet (1.1 * x191) (\\x195 -> rlet (recip (3.3 * 3.3 + x195 * x195)) (\\x196 -> rlet (sin 2.2) (\\x233 -> rlet (3.3 * 1.0) (\\x238 -> rlet ((negate 3.3 * x196) * 1.0) (\\x239 -> x191 * x239 + x233 * x238))))))"

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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "cos 1.1 * 1.0"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstSimple IM.empty a1
    @?= "cos 1.1 * 1.0"

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
  let a1 = (rrev1 sin . rrev1 @(AstRanked PrimalSpan) @Double @0 @0 sin) (rscalar 1.1)
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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @0 (rrev1 sin) (rscalar 1.1)
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
    @?= "(\\x1 -> let x2 = tproject1 x1 ; x3 = tproject2 x1 in x2 * cos x3) (ttuple (1.0, 1.1))"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (ttuple (1.0, 1.1))"

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

testSin0RfwdPP4Dual :: Assertion
testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "(\\x18 -> tproject1 x18 * cos (tproject2 x18)) (ttuple (rdualPart 1.0, (\\x14 -> tproject1 x14 * cos (tproject2 x14)) (ttuple (rdualPart 1.0, rdualPart 1.1))))"

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
    @?= "negate (sin 1.1) * 1.0"

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
                        x0 (rrepl @Double @1 [1] 42)) 1.1)

testSin0FoldB1 :: Assertion
testSin0FoldB1 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: ORArray Double 0)
    (rrev1 (let f :: forall f. ADReady f => f Double 0 -> f Double 0
                f x0 = rfold (\_x _a -> 7)
                         (rscalar 5) (rreplicate 1 x0)
            in f) (rscalar 1.1))

testSin0FoldB1PP :: Assertion
testSin0FoldB1PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan)
             (let f :: forall f. ADReady f => f Double 0 -> f Double 0
                  f x0 = rfold (\_x _a -> 7)
                           (rscalar 5) (rreplicate 1 x0)
              in f) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rsum (rproject (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [5.0] [rreplicate 1 1.1])), [rreplicate 1 1.1]))))) 0)"

testSin0FoldB2 :: Assertion
testSin0FoldB2 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: ORArray Double 0)
    (rev (let f :: forall f. ADReady f => f Double 0 -> f Double 0
              f x0 = rfold (\_x _a -> 7)
                       (rscalar 5) (rreplicate 1 x0)
          in f) (rscalar 1.1))

testSin0FoldB3 :: Assertion
testSin0FoldB3 = do
  assertEqualUpToEpsilon' 1e-10
    (0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = rfold (\_x _a -> 7)
                        (rscalar 5) (rreplicate 1 x0)
           in f) 1.1)

testSin0FoldB4 :: Assertion
testSin0FoldB4 = do
  assertEqualUpToEpsilon' 1e-10
    (0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = rfold (\_x _a -> 7)
                        x0 (rrepl @Double @1 [1] 42)
           in f) 1.1)

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (0.12389721944941383 :: OR.Array 0 Double)
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @Double @1 [5] 42)) 1.1)

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

testSin0Fold182Srev :: Assertion
testSin0Fold182Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.4409160296923509) :: ORArray Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
                f a0 = sfold @_ @f @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold182SrevPP :: Assertion
testSin0Fold182SrevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan)
           (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[5]
                f a0 = sfold @_ @f @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "let h12 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1])), [sreplicate 1.1]))) in rfromS (ssum (sproject (tproject1 h12) 0)) + rfromS (sreshape (sproject (tproject2 h12) 0))"

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
                        x0 (rrepl @Double @1 [1] 42))
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
                        x0 (rrepl @Double @1 [5] 42))
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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let v18 = rconst (rfromListLinear [2] [42.0,42.0]) ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) (\\h19 -> ttuple ([cos (rproject (tproject1 (tproject2 (tproject2 h19))) 0) * (rproject (tproject1 (tproject2 h19)) 0 + rproject (tproject1 h19) 0)], [0.0])) (\\h28 -> ttuple ([(rproject (tproject1 (tproject2 (tproject2 (tproject1 h28)))) 0 * negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0))) * (rproject (tproject1 (tproject2 (tproject2 h28))) 0 + rproject (tproject1 (tproject2 h28)) 0) + (rproject (tproject1 (tproject2 (tproject1 h28))) 0 + rproject (tproject1 (tproject1 h28)) 0) * cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0)], [0.0])) (\\h39 -> let x47 = cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h39)))) 0) * rproject (tproject1 (tproject1 h39)) 0 in ttuple ([0.0 + x47], ttuple ([0.0 + x47], ttuple ([0.0 + negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h39)))) 0)) * ((rproject (tproject1 (tproject2 (tproject2 h39))) 0 + rproject (tproject1 (tproject2 h39)) 0) * rproject (tproject1 (tproject1 h39)) 0)], [0.0])))) [0.0] (ttuple ([rslice 1 2 v13], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h48 -> let x52 = sin (rproject (tproject1 h48) 0) in ttuple ([x52], ttuple (tproject1 h48, [x52]))) (\\h54 -> let x63 = rproject (tproject1 (tproject1 h54)) 0 * cos (rproject (tproject1 (tproject2 h54)) 0) in ttuple ([x63], ttuple (tproject1 (tproject1 h54), [x63]))) (\\h65 -> ttuple ([cos (rproject (tproject1 (tproject2 h65)) 0) * (rproject (tproject2 (tproject2 (tproject1 h65))) 0 + rproject (tproject1 (tproject1 h65)) 0) + rproject (tproject1 (tproject2 (tproject1 h65))) 0], [0.0])) [1.1] [v18])), [v18]))))) 0 + v13 ! [0]"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v4 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v4 ! [0]) + cos 1.1 * v4 ! [1] + v4 ! [2]"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let v17 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h18 -> let x27 = rproject (tproject1 h18) 0 * cos (rproject (tproject1 (tproject2 (tproject2 h18))) 0) in ttuple ([x27], [x27])) (\\h28 -> let x37 = rproject (tproject1 (tproject1 h28)) 0 * cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0) + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h28)))) 0 * negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0))) * rproject (tproject1 (tproject2 h28)) 0 in ttuple ([x37], [x37])) (\\h38 -> let x46 = rproject (tproject2 (tproject1 h38)) 0 + rproject (tproject1 (tproject1 h38)) 0 in ttuple ([0.0 + cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h38)))) 0) * x46], ttuple ([0.0], ttuple ([0.0 + negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h38)))) 0)) * (rproject (tproject1 (tproject2 h38)) 0 * x46)], [0.0])))) [1.0] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h47 -> let x51 = sin (rproject (tproject1 h47) 0) in ttuple ([x51], ttuple (tproject1 h47, [x51]))) (\\h53 -> let x56 = rproject (tproject1 (tproject1 h53)) 0 * cos (rproject (tproject1 (tproject2 h53)) 0) in ttuple ([x56], ttuple (tproject1 (tproject1 h53), [x56]))) (\\h58 -> ttuple ([cos (rproject (tproject1 (tproject2 h58)) 0) * (rproject (tproject2 (tproject2 (tproject1 h58))) 0 + rproject (tproject1 (tproject1 h58)) 0) + rproject (tproject1 (tproject2 (tproject1 h58))) 0], [0.0])) [1.1] [v17])), [v17]))))) 0)"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "(\\x1 -> let v17 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 (tproject1 x1)) (rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h18 -> let x27 = rproject (tproject1 h18) 0 * cos (rproject (tproject1 (tproject2 (tproject2 h18))) 0) in ttuple ([x27], [x27])) (\\h28 -> let x37 = rproject (tproject1 (tproject1 h28)) 0 * cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0) + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h28)))) 0 * negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h28)))) 0))) * rproject (tproject1 (tproject2 h28)) 0 in ttuple ([x37], [x37])) (\\h38 -> let x46 = rproject (tproject2 (tproject1 h38)) 0 + rproject (tproject1 (tproject1 h38)) 0 in ttuple ([0.0 + cos (rproject (tproject1 (tproject2 (tproject2 (tproject2 h38)))) 0) * x46], ttuple ([0.0], ttuple ([0.0 + negate (sin (rproject (tproject1 (tproject2 (tproject2 (tproject2 h38)))) 0)) * (rproject (tproject1 (tproject2 h38)) 0 * x46)], [0.0])))) [tproject1 x1] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h47 -> let x51 = sin (rproject (tproject1 h47) 0) in ttuple ([x51], ttuple (tproject1 h47, [x51]))) (\\h53 -> let x56 = rproject (tproject1 (tproject1 h53)) 0 * cos (rproject (tproject1 (tproject2 h53)) 0) in ttuple ([x56], ttuple (tproject1 (tproject1 h53), [x56]))) (\\h58 -> ttuple ([cos (rproject (tproject1 (tproject2 h58)) 0) * (rproject (tproject2 (tproject2 (tproject1 h58))) 0 + rproject (tproject1 (tproject1 h58)) 0) + rproject (tproject1 (tproject2 (tproject1 h58))) 0], [0.0])) [tproject2 x1] [v17])), [v17]))))) 0)) (ttuple (1.0, 1.1))"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v18 = rconst (rfromListLinear [2] [5.0,7.0]) ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v13], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v18])), [v18]))))) 0 + v13 ! [0]"

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
    @?= "\\v13 x19 -> let v17 = rconst (rfromListLinear [2] [5.0,7.0]) in [rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v13], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x19] [v17])), [v17]))))) 0 + v13 ! [0]]"

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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v19 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) ; v13 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h14 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v13], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v19])), [v19]))) in 5.0 * rproject (tproject2 h14) 0 ! [0] + 7.0 * rproject (tproject2 h14) 0 ! [1] + rproject (tproject1 h14) 0 + v13 ! [0]"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v4 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; x5 = v4 ! [1] ; x6 = v4 ! [0] ; x7 = cos (sin 1.1 - 1.1 * 5.0) * x6 in cos 1.1 * x7 + 5.0 * (-1.0 * x7) + 7.0 * (-1.0 * x6) + cos 1.1 * x5 + 5.0 * (-1.0 * x5) + v4 ! [2]"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v20 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0])], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v20])), [v20]))))) 0)"

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
                  x0 (rrepl @Double @1 [1] 42))
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
      a1 = rbuild1 @(AstRanked PrimalSpan) @Double @1 k
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
      a1 = unitriangular1 @3 @Double @(AstRanked PrimalSpan) k sh
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
      a1 = unitriangular2 @3 @Double @(AstRanked PrimalSpan) k sh
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromVector (fromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))])) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4])"

rscanZip :: forall rn n ranked. (GoodScalar rn, KnownNat n, ADReady ranked)
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
      (productToVectorOf $ dmapAccumL Proxy
         snat
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped eShs)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
              g acc e =
               blet
                (f (rfromD $ acc V.! 0) e)
                (\res -> ttuple (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ])
                             (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ]))
          in g)
         (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked acc0)
         (HVectorPseudoTensor $ dmkHVector es))
      (\res -> rappend (rfromList [acc0]) (rfromD $ res V.! 1))

sscanZip :: forall rn sh k ranked shaped.
            ( GoodScalar rn, KnownShS sh, KnownNat k
            , ADReady ranked
            , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
       => (forall f. ADReadyS f
           => f rn sh -> HVector (RankedOf f) -> f rn sh)
       -> VoidHVector
       -> shaped rn sh
       -> HVector ranked
       -> shaped rn (1 + k ': sh)
sscanZip f eShs acc0 es =
  sletHVectorIn
    (productToVectorOf $ dmapAccumL Proxy
       (SNat @k)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped eShs)
       (let g :: forall f. ADReady f
              => HVector f -> HVector f -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
            g acc e =
             blet
                (f (sfromD $ acc V.! 0) e)
                (\res -> ttuple (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ])
                             (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ]))
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                  -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                  -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
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
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ xh V.! 0
                             in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 1
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[2]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[4, 3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                    x1 = sfromD @Double @'[3] $ xh V.! 1
                                in ttuple (HVectorPseudoTensor $ dmkHVector
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
                                              / sin x / srepl 3) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sbuild1 @_ @_ @4 $ \i ->
                                             sfromD (a V.! 1)
                                             - sin x1 / sreplicate @_ @3
                                                          (srepl 1 + sfromIndex0 i) ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[2]
                                                       (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 2) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                       [ DynamicShaped
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
                                           + sin x / srepl 3 ])
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
                      $ productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ ingestData [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1) ])
                                            (HVectorPseudoTensor $ dmkHVector
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
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ])
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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[6] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    x2 = sfromD @Double @'[6] $ xh V.! 1
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList
                                             [srepl 0.01, ssum @_ @_ @6 x2, srepl 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - sfromD (a V.! 1))) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sreplicate @_ @3
                                             (ssum @_ @_ @1 (sfromD (a V.! 0)))
                                           - sin x / srepl 3
                                           - sreplicate @_ @3
                                             (sindex0 @_ @_ @'[3]
                                                       (sfromD (a V.! 1)) [1]
                                             - smaxIndex
                                                 @_ @Double @Double @'[] @3
                                                 (sin x / srepl 3)) ])
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
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h28 -> ttuple ([sproject (tproject1 h28) 0], [0.0])) (\\h35 -> ttuple ([sproject (tproject1 (tproject1 h35)) 0], [0.0])) (\\h41 -> ttuple ([sproject (tproject1 (tproject1 h41)) 0], ttuple ([], ttuple ([0.0], [0.0])))) [4.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @0) (\\h47 -> ttuple ([sproject (tproject1 h47) 0], ttuple (tproject1 h47, []))) (\\h54 -> ttuple ([sproject (tproject1 (tproject1 h54)) 0], ttuple (tproject1 (tproject1 h54), []))) (\\h63 -> ttuple ([0.0 + sproject (tproject1 (tproject2 (tproject1 h63))) 0 + sproject (tproject1 (tproject1 h63)) 0], [0.0])) [1.1] [rconst (rfromListLinear [0] [])])), [rconst (rfromListLinear [0] [])]))))) 0)]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
    @?= "[sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (sfromListLinear [1] [0.0])])), [sconst @[1] (sfromListLinear [1] [0.0])]))))) 0]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
    @?= "(\\h1 -> [sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (sproject (tproject1 h1) 0))] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 h1) 0] [sconst @[1] (sfromListLinear [1] [0.0])])), [sconst @[1] (sfromListLinear [1] [0.0])]))))) 0]) (ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]))"

testSin0rmapAccumRD01SN531bRPP :: Assertion
testSin0rmapAccumRD01SN531bRPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rproject (tproject1 (dmapAccumLDer (SNat @1) (\\h27 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h27) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h34 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h34)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h40 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h40)) 0)]), ttuple (dmkHVector (fromList []), ttuple (dmkHVector (fromList [DynamicRanked 0.0]), dmkHVector (fromList [DynamicRanked 0.0]))))) (dmkHVector (fromList [DynamicRanked 4.0])) (ttuple (dmkHVector (fromList []), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) (\\h46 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h46) 0)]), ttuple (tproject1 h46, dmkHVector (fromList [])))) (\\h53 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h53)) 0)]), ttuple (tproject1 (tproject1 h53), dmkHVector (fromList [])))) (\\h62 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h62)) 0 + rproject (tproject1 (tproject2 (tproject1 h62))) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (dmkHVector (fromList [DynamicRanked 1.1])) (dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))), dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))))) 0)])"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i55, i56] -> [i55, i56])) (\\[i54] -> [i54])) (\\[i53] -> [i53])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))]))))) 0)))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVector (RankedOf f) -> f Double '[2, 2]
      f x0 = sletHVectorIn
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
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
    @?= "[ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i44, i45] -> [i44, i45])) (\\[i46] -> [i46])) (\\[i47] -> [i47])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))])), [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]))))) 0))]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVector f -> f Double 2
      f x0 = rletHVectorIn
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                               h xh _a = ttuple (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)

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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (rgather [4] (rproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))]))))) 0) (\\[i38] -> [remF (quotF i38 2) 2, remF i38 2]))]"

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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                         (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                            in g)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sconstant (sfromR j))) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIntegral (sconstant (sfromR i))]) ])))
      in f . sfromR) (rscalar 1.1 :: ORArray Double 0))

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
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList [ DynamicShaped x ])
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                 let x = sfromD @Double @'[3] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sin x - sfromD (a V.! 2) ])
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    a = xh
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
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
                                           + sin x / srepl 3 ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g _xh a =
                                let x = sreplicate @g @3 (sscalar 2)
                                in ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [])
                                         (HVectorPseudoTensor $ dmkHVector
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
                                                 (sin x / sreplicate0N (sscalar 3))) ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x])
                                           (HVectorPseudoTensor $ dmkHVector
                                        [ DynamicShaped x ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1)])
                                           (HVectorPseudoTensor $ dmkHVector
                                      [ DynamicShaped x ])
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
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in ttuple (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                       (HVectorPseudoTensor $ dmkHVector
                                        [ DynamicShaped x ])
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
               f x0 = dunHVector $ productToVectorOf
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
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           `atan2F` smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sindex0 @_ @_ @'[2]
                                                      (sfromD (a V.! 2)) [1]
                                              / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 3) ])
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
               f x0 = productToVectorOf
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
                                 -> InterpretationTarget (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  ttuple (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           ** smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sreplicate @_ @3
                                             (sin x / srepl 6
                                              + sindex0 @_ @_ @'[2]
                                                        (sfromD (a V.! 2)) [1]
                                                / sin x / srepl 3)
                                       , DynamicShaped
                                         $ sreplicate @_ @3
                                             (ssum @_ @_ @2 (sfromD (a V.! 1))
                                              + sin x / srepl 6) ])
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
                             (rrepl @Double @1 [1] 42)))
          (FlipR $ OR.constant [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             (rrepl @Double @1 [5] 42)))
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
                              (rrepl @Double @6
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
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                   (let g :: forall g. ADReady g
                          => HVector g -> HVector g -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @5 $ xh V.! 0
                         in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked x)
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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v24 = rconst (rfromListLinear [2] [42.0,42.0]) ; v19 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v19], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v24])), [v24]))))) 0 + v19 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v23 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v23])), [v23]))))) 0)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev2 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v30 = rconst (rfromListLinear [2] [5.0,7.0]) ; v27 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v27], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v30])), [v30]))))) 0 + v27 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v23 = rconst (rfromListLinear [2] [5.0,7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v23])), [v23]))))) 0)"

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
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZSR])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInlineAst a1))
    @?= 5072

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v26 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0])], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v26])), [v26]))))) 0)"

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
                           (rrepl @Double @1 [1] 42)
                         , DynamicRanked
                           (rrepl @Double @3 [1, 3, 4] 32) ]))
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
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                   (let g :: forall g. ADReady g
                          => HVector g -> HVector g -> InterpretationTarget g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @2 $ xh V.! 0
                         in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked x)
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
    @?= "let h14 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1])), [sreplicate 1.1]))) in [ssum (sproject (tproject2 h14) 0) + sproject (tproject1 h14) 0]"

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
    (g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h20 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1])), [rreplicate 11 1.1]))) in [rsum (rproject (tproject2 h20) 0) + rproject (tproject1 h20) 0]"

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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h20 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1])), [rreplicate 11 1.1]))) in [rsum (rproject (tproject2 h20) 0) + rproject (tproject1 h20) 0]"

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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h20 = dmapAccumRDer (SNat @11) (\\h23 -> let h51 = dmapAccumRDer (SNat @22) (\\h54 -> let x70 = cos (rproject (tproject2 (tproject2 (tproject2 h54))) 0) in ttuple ([0.0 + rproject (tproject1 h54) 0], [0.0 + recip (x70 * x70) * rproject (tproject1 h54) 0])) (\\h73 -> let x99 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h73)))) 0) ; x100 = x99 * x99 ; x103 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h73)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h73)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h73)) 0], [((x103 * x99 + x103 * x99) * negate (recip (x100 * x100))) * rproject (tproject1 (tproject2 h73)) 0 + rproject (tproject1 (tproject1 h73)) 0 * recip x100])) (\\h107 -> let x130 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h107)))) 0) ; x131 = x130 * x130 ; x134 = negate (recip (x131 * x131)) * (rproject (tproject1 (tproject2 h107)) 0 * rproject (tproject2 (tproject1 h107)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h107)) 0 + recip x131 * rproject (tproject2 (tproject1 h107)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h107)))) 0)) * (x130 * x134 + x130 * x134)])))) [rproject (tproject1 h23) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\h138 -> ttuple ([rproject (tproject1 h138) 0 + tan (rproject (tproject2 h138) 0)], ttuple (tproject1 h138, []))) (\\h152 -> let x174 = cos (rproject (tproject2 (tproject2 h152)) 0) in ttuple ([rproject (tproject1 (tproject1 h152)) 0 + rproject (tproject2 (tproject1 h152)) 0 * recip (x174 * x174)], ttuple (tproject1 (tproject1 h152), []))) (\\h177 -> let x197 = cos (rproject (tproject2 (tproject2 h177)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h177))) 0 + rproject (tproject1 (tproject1 h177)) 0], [0.0 + recip (x197 * x197) * rproject (tproject1 (tproject1 h177)) 0])) [rproject (tproject2 (tproject2 (tproject2 h23))) 0] [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 h23))) 0)])), [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 h23))) 0)]))) in ttuple ([0.0 + rsum (rproject (tproject2 h51) 0)], [0.0 + rproject (tproject1 h51) 0])) (\\h201 -> let h236 = dmapAccumLDer (SNat @22) (\\h251 -> ttuple ([rproject (tproject1 h251) 0 + tan (rproject (tproject2 h251) 0)], ttuple (tproject1 h251, ttuple (tproject1 h251, [])))) (\\h265 -> let x282 = cos (rproject (tproject2 (tproject2 h265)) 0) in ttuple ([rproject (tproject1 (tproject1 h265)) 0 + rproject (tproject2 (tproject1 h265)) 0 * recip (x282 * x282)], ttuple (tproject1 (tproject1 h265), ttuple (tproject1 (tproject1 h265), [])))) (\\h285 -> let x306 = cos (rproject (tproject2 (tproject2 h285)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h285))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h285)))) 0 + rproject (tproject1 (tproject1 h285)) 0], [0.0 + recip (x306 * x306) * rproject (tproject1 (tproject1 h285)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h201)))) 0] [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h201)))) 0)] ; h248 = dmapAccumRDer (SNat @22) (\\h311 -> let x333 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h311))))) 0) ; x334 = x333 * x333 ; x337 = rproject (tproject2 (tproject2 (tproject1 (tproject2 h311)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h311))))) 0)) in ttuple ([rproject (tproject1 h311) 0], [((x337 * x333 + x337 * x333) * negate (recip (x334 * x334))) * rproject (tproject1 (tproject2 (tproject2 h311))) 0 + rproject (tproject1 h311) 0 * recip x334])) (\\h341 -> let x380 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h341)))))) 0) ; x381 = x380 * x380 ; x383 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h341)))))) 0)) ; x385 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h341))))) 0 * x383 ; x386 = x381 * x381 ; x387 = x385 * x380 + x385 * x380 ; x388 = negate (recip x386) ; x393 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 h341))))) 0 * x383 + ((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h341)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h341)))))) 0)) * -1.0) * rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h341))))) 0 ; x396 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h341)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h341)))))) 0)) ; x397 = x396 * x380 + x396 * x380 in ttuple ([rproject (tproject1 (tproject1 h341)) 0], [((x393 * x380 + x396 * x385 + x393 * x380 + x396 * x385) * x388 + (((x397 * x381 + x397 * x381) * negate (recip (x386 * x386))) * -1.0) * x387) * rproject (tproject1 (tproject2 (tproject2 (tproject2 h341)))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h341)))) 0 * (x387 * x388) + rproject (tproject1 (tproject1 h341)) 0 * recip x381 + (x397 * negate (recip (x381 * x381))) * rproject (tproject1 (tproject2 h341)) 0])) (\\h403 -> let x431 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h403)))))) 0) ; x432 = x431 * x431 ; x434 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h403)))))) 0)) ; x436 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h403))))) 0 * x434 ; x437 = x432 * x432 ; x438 = x436 * x431 + x436 * x431 ; x439 = negate (recip x437) ; x442 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h403)))) 0 * rproject (tproject2 (tproject1 h403)) 0 ; x443 = negate (recip (x437 * x437)) * (-1.0 * (x438 * x442)) ; x444 = x439 * x442 ; x445 = x431 * x444 + x431 * x444 ; x448 = x432 * x443 + x432 * x443 + negate (recip (x432 * x432)) * (rproject (tproject1 (tproject2 h403)) 0 * rproject (tproject2 (tproject1 h403)) 0) in ttuple ([0.0 + recip x432 * rproject (tproject2 (tproject1 h403)) 0 + rproject (tproject1 (tproject1 h403)) 0], ttuple (ttuple ([], ttuple ([0.0], [0.0 + x434 * x445])), ttuple ([0.0 + (x438 * x439) * rproject (tproject2 (tproject1 h403)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h403)))))) 0)) * (x431 * x448 + x431 * x448 + x436 * x444 + x436 * x444) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h403)))))) 0) * (-1.0 * (rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h403))))) 0 * x445))])))))) [rproject (tproject1 (tproject1 h201)) 0] (ttuple (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\h455 -> let x462 = cos (rproject (tproject2 (tproject2 (tproject2 h455))) 0) in ttuple ([rproject (tproject1 h455) 0 + rproject (tproject1 (tproject2 h455)) 0 * recip (x462 * x462)], ttuple ([rproject (tproject1 h455) 0], []))) (\\h466 -> let x483 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h466)))) 0) ; x484 = x483 * x483 ; x487 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h466)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h466)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h466)) 0 + rproject (tproject1 (tproject2 (tproject1 h466))) 0 * recip x484 + ((x487 * x483 + x487 * x483) * negate (recip (x484 * x484))) * rproject (tproject1 (tproject2 (tproject2 h466))) 0], ttuple ([rproject (tproject1 (tproject1 h466)) 0], []))) (\\h492 -> let x505 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h492)))) 0) ; x506 = x505 * x505 ; x509 = negate (recip (x506 * x506)) * (rproject (tproject1 (tproject2 (tproject2 h492))) 0 * rproject (tproject1 (tproject1 h492)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h492)) 0 + rproject (tproject1 (tproject2 (tproject1 h492))) 0], ttuple ([0.0 + recip x506 * rproject (tproject1 (tproject1 h492)) 0], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h492)))) 0)) * (x505 * x509 + x505 * x509)])))) [rproject (tproject2 (tproject2 (tproject2 (tproject1 h201)))) 0] (ttuple ([rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h201)))) 0)], ttuple (tproject1 (tproject2 h236), [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h201)))) 0)])))))) 0], [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h201)))) 0)])), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\h514 -> let x531 = cos (rproject (tproject2 (tproject2 (tproject2 h514))) 0) in ttuple ([0.0 + rproject (tproject1 h514) 0], ttuple (tproject1 h514, [0.0 + recip (x531 * x531) * rproject (tproject1 h514) 0]))) (\\h534 -> let h555 = let x547 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h534)))) 0) ; x548 = x547 * x547 ; x551 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h534)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h534)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h534)) 0], [((x551 * x547 + x551 * x547) * negate (recip (x548 * x548))) * rproject (tproject1 (tproject2 h534)) 0 + rproject (tproject1 (tproject1 h534)) 0 * recip x548]) in ttuple (tproject1 h555, ttuple (tproject1 (tproject1 h534), tproject2 h555))) (\\h556 -> let h589 = let x581 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h556)))) 0) ; x582 = x581 * x581 ; x585 = negate (recip (x582 * x582)) * (rproject (tproject1 (tproject2 h556)) 0 * rproject (tproject2 (tproject2 (tproject1 h556))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h556)) 0 + recip x582 * rproject (tproject2 (tproject2 (tproject1 h556))) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h556)))) 0)) * (x581 * x585 + x581 * x585)]))) in ttuple ([rproject (tproject1 h589) 0 + rproject (tproject1 (tproject2 (tproject1 h556))) 0], tproject2 h589)) [rproject (tproject1 (tproject2 h201)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h236))) 0], [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h201)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h236))) 0], [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h201)))) 0)]))))) in ttuple ([rsum (rproject (tproject2 h248) 0)], [rproject (tproject1 h248) 0])) (\\h592 -> let h629 = dmapAccumLDer (SNat @22) (\\h645 -> ttuple ([rproject (tproject1 h645) 0 + tan (rproject (tproject2 h645) 0)], ttuple (tproject1 h645, ttuple (tproject1 h645, [])))) (\\h659 -> let x676 = cos (rproject (tproject2 (tproject2 h659)) 0) in ttuple ([rproject (tproject1 (tproject1 h659)) 0 + rproject (tproject2 (tproject1 h659)) 0 * recip (x676 * x676)], ttuple (tproject1 (tproject1 h659), ttuple (tproject1 (tproject1 h659), [])))) (\\h679 -> let x700 = cos (rproject (tproject2 (tproject2 h679)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h679))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h679)))) 0 + rproject (tproject1 (tproject1 h679)) 0], [0.0 + recip (x700 * x700) * rproject (tproject1 (tproject1 h679)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h592)))) 0] [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h592)))) 0)] ; h637 = dmapAccumLDer (SNat @22) (\\h705 -> let x727 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h705))))) 0) ; x728 = x727 * x727 ; x731 = negate (recip (x728 * x728)) * (rproject (tproject1 (tproject2 (tproject2 h705))) 0 * rproject (tproject1 (tproject2 h705)) 0) in ttuple ([0.0 + rproject (tproject1 h705) 0 + recip x728 * rproject (tproject1 (tproject2 h705)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h705))))) 0)) * (x727 * x731 + x727 * x731)])))) (\\h735 -> let x774 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h735)))))) 0) ; x775 = x774 * x774 ; x776 = x775 * x775 ; x777 = negate (recip x776) ; x780 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h735)))) 0 * rproject (tproject1 (tproject2 (tproject2 h735))) 0 ; x781 = x777 * x780 ; x784 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h735)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h735)))))) 0)) ; x785 = x784 * x774 + x784 * x774 ; x790 = (((x785 * x775 + x785 * x775) * negate (recip (x776 * x776))) * -1.0) * x780 + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h735)))) 0 * rproject (tproject1 (tproject2 (tproject2 h735))) 0 + rproject (tproject1 (tproject2 (tproject1 h735))) 0 * rproject (tproject1 (tproject2 (tproject2 (tproject2 h735)))) 0) * x777 in ttuple ([rproject (tproject1 (tproject1 h735)) 0 + (x785 * negate (recip (x775 * x775))) * rproject (tproject1 (tproject2 (tproject2 h735))) 0 + rproject (tproject1 (tproject2 (tproject1 h735))) 0 * recip x775], ttuple ([], ttuple ([0.0], [((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h735)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h735)))))) 0)) * -1.0) * (x774 * x781 + x774 * x781) + (x784 * x781 + x790 * x774 + x784 * x781 + x790 * x774) * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h735)))))) 0))])))) (\\h797 -> let x825 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h797)))))) 0) ; x826 = x825 * x825 ; x827 = x826 * x826 ; x828 = negate (recip x827) ; x831 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h797)))) 0 * rproject (tproject1 (tproject2 (tproject2 h797))) 0 ; x832 = x828 * x831 ; x835 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h797)))))) 0)) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h797)))) 0 ; x836 = x825 * x835 + x825 * x835 ; x837 = x828 * x836 ; x838 = negate (recip (x827 * x827)) * (-1.0 * (x831 * x836)) ; x841 = x826 * x838 + x826 * x838 + negate (recip (x826 * x826)) * (rproject (tproject1 (tproject2 (tproject2 h797))) 0 * rproject (tproject1 (tproject1 h797)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h797)) 0], ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject2 (tproject2 h797)))) 0 * x837 + recip x826 * rproject (tproject1 (tproject1 h797)) 0], ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject2 h797))) 0 * x837], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h797)))))) 0)) * (x825 * x841 + x825 * x841 + x832 * x835 + x832 * x835) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h797)))))) 0) * (-1.0 * ((x825 * x832 + x825 * x832) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h797)))) 0))])))))) [0.0 + rproject (tproject2 (tproject1 h592)) 0] (ttuple ([rconst (rfromListLinear [22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + rreplicate 22 (rproject (tproject1 (tproject1 h592)) 0)], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\h849 -> let x866 = cos (rproject (tproject2 (tproject2 (tproject2 h849))) 0) in ttuple ([0.0 + rproject (tproject1 h849) 0], ttuple (tproject1 h849, [0.0 + recip (x866 * x866) * rproject (tproject1 h849) 0]))) (\\h869 -> let h900 = let x892 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h869)))) 0) ; x893 = x892 * x892 ; x896 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h869)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h869)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h869)) 0], [((x896 * x892 + x896 * x892) * negate (recip (x893 * x893))) * rproject (tproject1 (tproject2 h869)) 0 + rproject (tproject1 (tproject1 h869)) 0 * recip x893]) in ttuple (tproject1 h900, ttuple (tproject1 (tproject1 h869), tproject2 h900))) (\\h901 -> let h924 = let x916 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h901)))) 0) ; x917 = x916 * x916 ; x920 = negate (recip (x917 * x917)) * (rproject (tproject1 (tproject2 h901)) 0 * rproject (tproject2 (tproject2 (tproject1 h901))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h901)) 0 + recip x917 * rproject (tproject2 (tproject2 (tproject1 h901))) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h901)))) 0)) * (x916 * x920 + x916 * x920)]))) in ttuple ([rproject (tproject1 h924) 0 + rproject (tproject1 (tproject2 (tproject1 h901))) 0], tproject2 h924)) [rproject (tproject1 (tproject2 h592)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h629))) 0], [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h592)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h629))) 0], [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h592)))) 0)]))))) ; h640 = dmapAccumRDer (SNat @22) (\\h927 -> let x935 = cos (rproject (tproject2 (tproject2 (tproject2 h927))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 (tproject2 h927))) 0 + rproject (tproject1 h927) 0], [0.0 + recip (x935 * x935) * rproject (tproject1 h927) 0])) (\\h939 -> let x957 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h939)))) 0) ; x958 = x957 * x957 ; x961 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h939)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h939)))) 0)) in ttuple ([rproject (tproject1 (tproject1 (tproject2 (tproject1 h939)))) 0 + rproject (tproject1 (tproject1 h939)) 0], [((x961 * x957 + x961 * x957) * negate (recip (x958 * x958))) * rproject (tproject1 (tproject2 h939)) 0 + rproject (tproject1 (tproject1 h939)) 0 * recip x958])) (\\h966 -> let x980 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h966)))) 0) ; x981 = x980 * x980 ; x984 = negate (recip (x981 * x981)) * (rproject (tproject1 (tproject2 h966)) 0 * rproject (tproject2 (tproject1 h966)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h966)) 0 + recip x981 * rproject (tproject2 (tproject1 h966)) 0], ttuple (ttuple ([0.0 + rproject (tproject1 (tproject1 h966)) 0], []), ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h966)))) 0)) * (x980 * x984 + x980 * x984)])))) [0.0] (ttuple (ttuple ([rproject (tproject1 (tproject2 (tproject2 h637))) 0], []), ttuple (tproject1 (tproject2 h629), [rreplicate 22 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h592)))) 0)]))) in ttuple ([0.0 + rproject (tproject1 h637) 0], ttuple ([], ttuple ([0.0 + rsum (rproject (tproject2 h640) 0) + rsum (rproject (tproject2 (tproject2 (tproject2 h637))) 0)], [0.0 + rproject (tproject1 h640) 0])))) [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) (\\h989 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @22) (\\h1007 -> ttuple ([rproject (tproject1 h1007) 0 + tan (rproject (tproject2 h1007) 0)], [])) (\\h1014 -> let x1027 = cos (rproject (tproject2 (tproject2 h1014)) 0) in ttuple ([rproject (tproject1 (tproject1 h1014)) 0 + rproject (tproject2 (tproject1 h1014)) 0 * recip (x1027 * x1027)], [])) (\\h1030 -> let x1041 = cos (rproject (tproject2 (tproject2 h1030)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1030)) 0], [0.0 + recip (x1041 * x1041) * rproject (tproject1 (tproject1 h1030)) 0])) [rproject (tproject2 h989) 0] [rreplicate 22 (rproject (tproject1 h989) 0)])) 0], ttuple (tproject1 h989, []))) (\\h1044 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @22) (\\h1077 -> let x1095 = cos (rproject (tproject2 (tproject2 (tproject2 h1077))) 0) in ttuple ([rproject (tproject1 h1077) 0 + rproject (tproject1 (tproject2 h1077)) 0 * recip (x1095 * x1095)], [])) (\\h1098 -> let x1125 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1098)))) 0) ; x1126 = x1125 * x1125 ; x1129 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h1098)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1098)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h1098)) 0 + rproject (tproject1 (tproject2 (tproject1 h1098))) 0 * recip x1126 + ((x1129 * x1125 + x1129 * x1125) * negate (recip (x1126 * x1126))) * rproject (tproject1 (tproject2 (tproject2 h1098))) 0], [])) (\\h1133 -> let x1156 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1133)))) 0) ; x1157 = x1156 * x1156 ; x1160 = negate (recip (x1157 * x1157)) * (rproject (tproject1 (tproject2 (tproject2 h1133))) 0 * rproject (tproject1 (tproject1 h1133)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1133)) 0], ttuple ([0.0 + recip x1157 * rproject (tproject1 (tproject1 h1133)) 0], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1133)))) 0)) * (x1156 * x1160 + x1156 * x1160)])))) [rproject (tproject2 (tproject1 h1044)) 0] (ttuple ([rreplicate 22 (rproject (tproject1 (tproject1 h1044)) 0)], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\h1164 -> ttuple ([rproject (tproject1 h1164) 0 + tan (rproject (tproject2 h1164) 0)], ttuple (tproject1 h1164, []))) (\\h1178 -> let x1194 = cos (rproject (tproject2 (tproject2 h1178)) 0) in ttuple ([rproject (tproject1 (tproject1 h1178)) 0 + rproject (tproject2 (tproject1 h1178)) 0 * recip (x1194 * x1194)], ttuple (tproject1 (tproject1 h1178), []))) (\\h1197 -> let x1221 = cos (rproject (tproject2 (tproject2 h1197)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1197))) 0 + rproject (tproject1 (tproject1 h1197)) 0], [0.0 + recip (x1221 * x1221) * rproject (tproject1 (tproject1 h1197)) 0])) [rproject (tproject2 (tproject2 h1044)) 0] [rreplicate 22 (rproject (tproject1 (tproject2 h1044)) 0)])), [rreplicate 22 (rproject (tproject1 (tproject2 h1044)) 0)]))))) 0], ttuple (tproject1 (tproject1 h1044), []))) (\\h1225 -> let h1245 = dmapAccumRDer (SNat @22) (\\h1251 -> let x1258 = cos (rproject (tproject2 (tproject2 (tproject2 h1251))) 0) in ttuple ([0.0 + rproject (tproject1 h1251) 0], [0.0 + recip (x1258 * x1258) * rproject (tproject1 h1251) 0])) (\\h1261 -> let x1273 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1261)))) 0) ; x1274 = x1273 * x1273 ; x1277 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h1261)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1261)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h1261)) 0], [((x1277 * x1273 + x1277 * x1273) * negate (recip (x1274 * x1274))) * rproject (tproject1 (tproject2 h1261)) 0 + rproject (tproject1 (tproject1 h1261)) 0 * recip x1274])) (\\h1281 -> let x1293 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1281)))) 0) ; x1294 = x1293 * x1293 ; x1297 = negate (recip (x1294 * x1294)) * (rproject (tproject1 (tproject2 h1281)) 0 * rproject (tproject2 (tproject1 h1281)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1281)) 0 + recip x1294 * rproject (tproject2 (tproject1 h1281)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1281)))) 0)) * (x1293 * x1297 + x1293 * x1297)])))) [rproject (tproject1 (tproject1 h1225)) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\h1301 -> ttuple ([rproject (tproject1 h1301) 0 + tan (rproject (tproject2 h1301) 0)], ttuple (tproject1 h1301, []))) (\\h1307 -> let x1314 = cos (rproject (tproject2 (tproject2 h1307)) 0) in ttuple ([rproject (tproject1 (tproject1 h1307)) 0 + rproject (tproject2 (tproject1 h1307)) 0 * recip (x1314 * x1314)], ttuple (tproject1 (tproject1 h1307), []))) (\\h1317 -> let x1325 = cos (rproject (tproject2 (tproject2 h1317)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1317))) 0 + rproject (tproject1 (tproject1 h1317)) 0], [0.0 + recip (x1325 * x1325) * rproject (tproject1 (tproject1 h1317)) 0])) [rproject (tproject2 (tproject2 h1225)) 0] [rreplicate 22 (rproject (tproject1 (tproject2 h1225)) 0)])), [rreplicate 22 (rproject (tproject1 (tproject2 h1225)) 0)]))) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1225))) 0 + rsum (rproject (tproject2 h1245) 0)], [0.0 + rproject (tproject1 h1245) 0])) [1.1] [rreplicate 11 1.1])), [rreplicate 11 1.1]))) in [rsum (rproject (tproject2 h20) 0) + rproject (tproject1 h20) 0]"

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
       $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 2680

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
       $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 31568

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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 407752

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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 6106313

-- Takes 100s, probably due to some of the pipelines forcing all derivs.
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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

testSin0FoldNestedR2LengthPPsDummy7 :: Assertion
testSin0FoldNestedR2LengthPPsDummy7 = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\_x3 _a3 -> 7)
                   -- the 7 causes Dummy InterpretationTargetM values
                   -- with the more precise typing of folds
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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 157643

testSin0FoldNestedR2Dummy7 :: Assertion
testSin0FoldNestedR2Dummy7 = do
 resetVarCounter
 assertEqualUpToEpsilon' 1e-10
  (0 :: OR.Array 0 Double)
  (rev'
   (let f :: forall f. ADReady f => f Double 0 -> f Double 0
        f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\_x3 _a3 -> 7)
                   -- the 7 causes Dummy InterpretationTargetM values
                   -- with the more precise typing of folds
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
    in f) 0.0001)

testSin0FoldNestedR2Tan :: Assertion
testSin0FoldNestedR2Tan = do
 assertEqualUpToEpsilon' 1e-10
  (25.000016360009603 :: OR.Array 0 Double)
  (rev'
   (let f :: forall f. ADReady f => f Double 0 -> f Double 0
        f z = rfold (\x a ->
                 rfold (\x2 a2 ->
                   rfold (\x3 a3 -> x3 + tan a3)
                         a2 (rreplicate 2 x2))
                       a (rreplicate 2 x))
                    z (rreplicate 2 z)
    in f) 0.0001)

testSin0MapAccumNestedR1PP :: Assertion
testSin0MapAccumNestedR1PP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 -> let y = rfromD @Double @0 $ x2 V.! 0
                                    w = rfromD @Double @0 $ a2 V.! 0
                                in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h16 = dmapAccumRDer (SNat @2) (\\h19 -> let h42 = dmapAccumRDer (SNat @2) (\\h45 -> let x61 = cos (rproject (tproject2 (tproject2 (tproject2 h45))) 0) in ttuple ([0.0 + rproject (tproject1 h45) 0], [0.0 + recip (x61 * x61) * rproject (tproject1 h45) 0])) (\\h64 -> let x90 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h64)))) 0) ; x91 = x90 * x90 ; x94 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h64)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h64)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h64)) 0], [((x94 * x90 + x94 * x90) * negate (recip (x91 * x91))) * rproject (tproject1 (tproject2 h64)) 0 + rproject (tproject1 (tproject1 h64)) 0 * recip x91])) (\\h98 -> let x121 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h98)))) 0) ; x122 = x121 * x121 ; x125 = negate (recip (x122 * x122)) * (rproject (tproject1 (tproject2 h98)) 0 * rproject (tproject2 (tproject1 h98)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h98)) 0 + recip x122 * rproject (tproject2 (tproject1 h98)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h98)))) 0)) * (x121 * x125 + x121 * x125)])))) [rproject (tproject1 h19) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h129 -> ttuple ([rproject (tproject1 h129) 0 + tan (rproject (tproject2 h129) 0)], ttuple (tproject1 h129, []))) (\\h143 -> let x165 = cos (rproject (tproject2 (tproject2 h143)) 0) in ttuple ([rproject (tproject1 (tproject1 h143)) 0 + rproject (tproject2 (tproject1 h143)) 0 * recip (x165 * x165)], ttuple (tproject1 (tproject1 h143), []))) (\\h168 -> let x188 = cos (rproject (tproject2 (tproject2 h168)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h168))) 0 + rproject (tproject1 (tproject1 h168)) 0], [0.0 + recip (x188 * x188) * rproject (tproject1 (tproject1 h168)) 0])) [rproject (tproject2 (tproject2 (tproject2 h19))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h19))) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h19))) 0)]))) in ttuple ([0.0 + rsum (rproject (tproject2 h42) 0)], [0.0 + rproject (tproject1 h42) 0])) (\\h192 -> let h227 = dmapAccumLDer (SNat @2) (\\h242 -> ttuple ([rproject (tproject1 h242) 0 + tan (rproject (tproject2 h242) 0)], ttuple (tproject1 h242, ttuple (tproject1 h242, [])))) (\\h256 -> let x273 = cos (rproject (tproject2 (tproject2 h256)) 0) in ttuple ([rproject (tproject1 (tproject1 h256)) 0 + rproject (tproject2 (tproject1 h256)) 0 * recip (x273 * x273)], ttuple (tproject1 (tproject1 h256), ttuple (tproject1 (tproject1 h256), [])))) (\\h276 -> let x297 = cos (rproject (tproject2 (tproject2 h276)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h276))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h276)))) 0 + rproject (tproject1 (tproject1 h276)) 0], [0.0 + recip (x297 * x297) * rproject (tproject1 (tproject1 h276)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h192)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h192)))) 0)] ; h239 = dmapAccumRDer (SNat @2) (\\h302 -> let x324 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h302))))) 0) ; x325 = x324 * x324 ; x328 = rproject (tproject2 (tproject2 (tproject1 (tproject2 h302)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h302))))) 0)) in ttuple ([rproject (tproject1 h302) 0], [((x328 * x324 + x328 * x324) * negate (recip (x325 * x325))) * rproject (tproject1 (tproject2 (tproject2 h302))) 0 + rproject (tproject1 h302) 0 * recip x325])) (\\h332 -> let x371 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h332)))))) 0) ; x372 = x371 * x371 ; x374 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h332)))))) 0)) ; x376 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h332))))) 0 * x374 ; x377 = x372 * x372 ; x378 = x376 * x371 + x376 * x371 ; x379 = negate (recip x377) ; x384 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 h332))))) 0 * x374 + ((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h332)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h332)))))) 0)) * -1.0) * rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h332))))) 0 ; x387 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h332)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h332)))))) 0)) ; x388 = x387 * x371 + x387 * x371 in ttuple ([rproject (tproject1 (tproject1 h332)) 0], [((x384 * x371 + x387 * x376 + x384 * x371 + x387 * x376) * x379 + (((x388 * x372 + x388 * x372) * negate (recip (x377 * x377))) * -1.0) * x378) * rproject (tproject1 (tproject2 (tproject2 (tproject2 h332)))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h332)))) 0 * (x378 * x379) + rproject (tproject1 (tproject1 h332)) 0 * recip x372 + (x388 * negate (recip (x372 * x372))) * rproject (tproject1 (tproject2 h332)) 0])) (\\h394 -> let x422 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h394)))))) 0) ; x423 = x422 * x422 ; x425 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h394)))))) 0)) ; x427 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h394))))) 0 * x425 ; x428 = x423 * x423 ; x429 = x427 * x422 + x427 * x422 ; x430 = negate (recip x428) ; x433 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h394)))) 0 * rproject (tproject2 (tproject1 h394)) 0 ; x434 = negate (recip (x428 * x428)) * (-1.0 * (x429 * x433)) ; x435 = x430 * x433 ; x436 = x422 * x435 + x422 * x435 ; x439 = x423 * x434 + x423 * x434 + negate (recip (x423 * x423)) * (rproject (tproject1 (tproject2 h394)) 0 * rproject (tproject2 (tproject1 h394)) 0) in ttuple ([0.0 + recip x423 * rproject (tproject2 (tproject1 h394)) 0 + rproject (tproject1 (tproject1 h394)) 0], ttuple (ttuple ([], ttuple ([0.0], [0.0 + x425 * x436])), ttuple ([0.0 + (x429 * x430) * rproject (tproject2 (tproject1 h394)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h394)))))) 0)) * (x422 * x439 + x422 * x439 + x427 * x435 + x427 * x435) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h394)))))) 0) * (-1.0 * (rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h394))))) 0 * x436))])))))) [rproject (tproject1 (tproject1 h192)) 0] (ttuple (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h446 -> let x453 = cos (rproject (tproject2 (tproject2 (tproject2 h446))) 0) in ttuple ([rproject (tproject1 h446) 0 + rproject (tproject1 (tproject2 h446)) 0 * recip (x453 * x453)], ttuple ([rproject (tproject1 h446) 0], []))) (\\h457 -> let x474 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h457)))) 0) ; x475 = x474 * x474 ; x478 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h457)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h457)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h457)) 0 + rproject (tproject1 (tproject2 (tproject1 h457))) 0 * recip x475 + ((x478 * x474 + x478 * x474) * negate (recip (x475 * x475))) * rproject (tproject1 (tproject2 (tproject2 h457))) 0], ttuple ([rproject (tproject1 (tproject1 h457)) 0], []))) (\\h483 -> let x496 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h483)))) 0) ; x497 = x496 * x496 ; x500 = negate (recip (x497 * x497)) * (rproject (tproject1 (tproject2 (tproject2 h483))) 0 * rproject (tproject1 (tproject1 h483)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h483)) 0 + rproject (tproject1 (tproject2 (tproject1 h483))) 0], ttuple ([0.0 + recip x497 * rproject (tproject1 (tproject1 h483)) 0], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h483)))) 0)) * (x496 * x500 + x496 * x500)])))) [rproject (tproject2 (tproject2 (tproject2 (tproject1 h192)))) 0] (ttuple ([rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h192)))) 0)], ttuple (tproject1 (tproject2 h227), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h192)))) 0)])))))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h192)))) 0)])), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h505 -> let x522 = cos (rproject (tproject2 (tproject2 (tproject2 h505))) 0) in ttuple ([0.0 + rproject (tproject1 h505) 0], ttuple (tproject1 h505, [0.0 + recip (x522 * x522) * rproject (tproject1 h505) 0]))) (\\h525 -> let h546 = let x538 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h525)))) 0) ; x539 = x538 * x538 ; x542 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h525)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h525)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h525)) 0], [((x542 * x538 + x542 * x538) * negate (recip (x539 * x539))) * rproject (tproject1 (tproject2 h525)) 0 + rproject (tproject1 (tproject1 h525)) 0 * recip x539]) in ttuple (tproject1 h546, ttuple (tproject1 (tproject1 h525), tproject2 h546))) (\\h547 -> let h580 = let x572 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h547)))) 0) ; x573 = x572 * x572 ; x576 = negate (recip (x573 * x573)) * (rproject (tproject1 (tproject2 h547)) 0 * rproject (tproject2 (tproject2 (tproject1 h547))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h547)) 0 + recip x573 * rproject (tproject2 (tproject2 (tproject1 h547))) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h547)))) 0)) * (x572 * x576 + x572 * x576)]))) in ttuple ([rproject (tproject1 h580) 0 + rproject (tproject1 (tproject2 (tproject1 h547))) 0], tproject2 h580)) [rproject (tproject1 (tproject2 h192)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h227))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h192)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h227))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h192)))) 0)]))))) in ttuple ([rsum (rproject (tproject2 h239) 0)], [rproject (tproject1 h239) 0])) (\\h583 -> let h620 = dmapAccumLDer (SNat @2) (\\h636 -> ttuple ([rproject (tproject1 h636) 0 + tan (rproject (tproject2 h636) 0)], ttuple (tproject1 h636, ttuple (tproject1 h636, [])))) (\\h650 -> let x667 = cos (rproject (tproject2 (tproject2 h650)) 0) in ttuple ([rproject (tproject1 (tproject1 h650)) 0 + rproject (tproject2 (tproject1 h650)) 0 * recip (x667 * x667)], ttuple (tproject1 (tproject1 h650), ttuple (tproject1 (tproject1 h650), [])))) (\\h670 -> let x691 = cos (rproject (tproject2 (tproject2 h670)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h670))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h670)))) 0 + rproject (tproject1 (tproject1 h670)) 0], [0.0 + recip (x691 * x691) * rproject (tproject1 (tproject1 h670)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h583)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h583)))) 0)] ; h628 = dmapAccumLDer (SNat @2) (\\h696 -> let x718 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h696))))) 0) ; x719 = x718 * x718 ; x722 = negate (recip (x719 * x719)) * (rproject (tproject1 (tproject2 (tproject2 h696))) 0 * rproject (tproject1 (tproject2 h696)) 0) in ttuple ([0.0 + rproject (tproject1 h696) 0 + recip x719 * rproject (tproject1 (tproject2 h696)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h696))))) 0)) * (x718 * x722 + x718 * x722)])))) (\\h726 -> let x765 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h726)))))) 0) ; x766 = x765 * x765 ; x767 = x766 * x766 ; x768 = negate (recip x767) ; x771 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h726)))) 0 * rproject (tproject1 (tproject2 (tproject2 h726))) 0 ; x772 = x768 * x771 ; x775 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h726)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h726)))))) 0)) ; x776 = x775 * x765 + x775 * x765 ; x781 = (((x776 * x766 + x776 * x766) * negate (recip (x767 * x767))) * -1.0) * x771 + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h726)))) 0 * rproject (tproject1 (tproject2 (tproject2 h726))) 0 + rproject (tproject1 (tproject2 (tproject1 h726))) 0 * rproject (tproject1 (tproject2 (tproject2 (tproject2 h726)))) 0) * x768 in ttuple ([rproject (tproject1 (tproject1 h726)) 0 + (x776 * negate (recip (x766 * x766))) * rproject (tproject1 (tproject2 (tproject2 h726))) 0 + rproject (tproject1 (tproject2 (tproject1 h726))) 0 * recip x766], ttuple ([], ttuple ([0.0], [((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h726)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h726)))))) 0)) * -1.0) * (x765 * x772 + x765 * x772) + (x775 * x772 + x781 * x765 + x775 * x772 + x781 * x765) * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h726)))))) 0))])))) (\\h788 -> let x816 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h788)))))) 0) ; x817 = x816 * x816 ; x818 = x817 * x817 ; x819 = negate (recip x818) ; x822 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h788)))) 0 * rproject (tproject1 (tproject2 (tproject2 h788))) 0 ; x823 = x819 * x822 ; x826 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h788)))))) 0)) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h788)))) 0 ; x827 = x816 * x826 + x816 * x826 ; x828 = x819 * x827 ; x829 = negate (recip (x818 * x818)) * (-1.0 * (x822 * x827)) ; x832 = x817 * x829 + x817 * x829 + negate (recip (x817 * x817)) * (rproject (tproject1 (tproject2 (tproject2 h788))) 0 * rproject (tproject1 (tproject1 h788)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h788)) 0], ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject2 (tproject2 h788)))) 0 * x828 + recip x817 * rproject (tproject1 (tproject1 h788)) 0], ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject2 h788))) 0 * x828], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h788)))))) 0)) * (x816 * x832 + x816 * x832 + x823 * x826 + x823 * x826) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h788)))))) 0) * (-1.0 * ((x816 * x823 + x816 * x823) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h788)))) 0))])))))) [0.0 + rproject (tproject2 (tproject1 h583)) 0] (ttuple ([rconst (rfromListLinear [2] [0.0,0.0]) + rreplicate 2 (rproject (tproject1 (tproject1 h583)) 0)], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h840 -> let x857 = cos (rproject (tproject2 (tproject2 (tproject2 h840))) 0) in ttuple ([0.0 + rproject (tproject1 h840) 0], ttuple (tproject1 h840, [0.0 + recip (x857 * x857) * rproject (tproject1 h840) 0]))) (\\h860 -> let h891 = let x883 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h860)))) 0) ; x884 = x883 * x883 ; x887 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h860)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h860)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h860)) 0], [((x887 * x883 + x887 * x883) * negate (recip (x884 * x884))) * rproject (tproject1 (tproject2 h860)) 0 + rproject (tproject1 (tproject1 h860)) 0 * recip x884]) in ttuple (tproject1 h891, ttuple (tproject1 (tproject1 h860), tproject2 h891))) (\\h892 -> let h915 = let x907 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h892)))) 0) ; x908 = x907 * x907 ; x911 = negate (recip (x908 * x908)) * (rproject (tproject1 (tproject2 h892)) 0 * rproject (tproject2 (tproject2 (tproject1 h892))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h892)) 0 + recip x908 * rproject (tproject2 (tproject2 (tproject1 h892))) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h892)))) 0)) * (x907 * x911 + x907 * x911)]))) in ttuple ([rproject (tproject1 h915) 0 + rproject (tproject1 (tproject2 (tproject1 h892))) 0], tproject2 h915)) [rproject (tproject1 (tproject2 h583)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h620))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h583)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h620))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h583)))) 0)]))))) ; h631 = dmapAccumRDer (SNat @2) (\\h918 -> let x926 = cos (rproject (tproject2 (tproject2 (tproject2 h918))) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 (tproject2 h918))) 0 + rproject (tproject1 h918) 0], [0.0 + recip (x926 * x926) * rproject (tproject1 h918) 0])) (\\h930 -> let x948 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h930)))) 0) ; x949 = x948 * x948 ; x952 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h930)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h930)))) 0)) in ttuple ([rproject (tproject1 (tproject1 (tproject2 (tproject1 h930)))) 0 + rproject (tproject1 (tproject1 h930)) 0], [((x952 * x948 + x952 * x948) * negate (recip (x949 * x949))) * rproject (tproject1 (tproject2 h930)) 0 + rproject (tproject1 (tproject1 h930)) 0 * recip x949])) (\\h957 -> let x971 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h957)))) 0) ; x972 = x971 * x971 ; x975 = negate (recip (x972 * x972)) * (rproject (tproject1 (tproject2 h957)) 0 * rproject (tproject2 (tproject1 h957)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h957)) 0 + recip x972 * rproject (tproject2 (tproject1 h957)) 0], ttuple (ttuple ([0.0 + rproject (tproject1 (tproject1 h957)) 0], []), ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h957)))) 0)) * (x971 * x975 + x971 * x975)])))) [0.0] (ttuple (ttuple ([rproject (tproject1 (tproject2 (tproject2 h628))) 0], []), ttuple (tproject1 (tproject2 h620), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h583)))) 0)]))) in ttuple ([0.0 + rproject (tproject1 h628) 0], ttuple ([], ttuple ([0.0 + rsum (rproject (tproject2 h631) 0) + rsum (rproject (tproject2 (tproject2 (tproject2 h628))) 0)], [0.0 + rproject (tproject1 h631) 0])))) [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h980 -> let h988 = dmapAccumLDer (SNat @2) (\\h989 -> ttuple ([rproject (tproject1 h989) 0 + tan (rproject (tproject2 h989) 0)], [])) (\\h996 -> let x1009 = cos (rproject (tproject2 (tproject2 h996)) 0) in ttuple ([rproject (tproject1 (tproject1 h996)) 0 + rproject (tproject2 (tproject1 h996)) 0 * recip (x1009 * x1009)], [])) (\\h1012 -> let x1023 = cos (rproject (tproject2 (tproject2 h1012)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1012)) 0], [0.0 + recip (x1023 * x1023) * rproject (tproject1 (tproject1 h1012)) 0])) [rproject (tproject2 h980) 0] [rreplicate 2 (rproject (tproject1 h980) 0)] in ttuple (tproject1 h988, ttuple (tproject1 h980, tproject2 h988))) (\\h1026 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @2) (\\h1054 -> let x1072 = cos (rproject (tproject2 (tproject2 (tproject2 h1054))) 0) in ttuple ([rproject (tproject1 h1054) 0 + rproject (tproject1 (tproject2 h1054)) 0 * recip (x1072 * x1072)], [])) (\\h1075 -> let x1102 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1075)))) 0) ; x1103 = x1102 * x1102 ; x1106 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h1075)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1075)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h1075)) 0 + rproject (tproject1 (tproject2 (tproject1 h1075))) 0 * recip x1103 + ((x1106 * x1102 + x1106 * x1102) * negate (recip (x1103 * x1103))) * rproject (tproject1 (tproject2 (tproject2 h1075))) 0], [])) (\\h1110 -> let x1133 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1110)))) 0) ; x1134 = x1133 * x1133 ; x1137 = negate (recip (x1134 * x1134)) * (rproject (tproject1 (tproject2 (tproject2 h1110))) 0 * rproject (tproject1 (tproject1 h1110)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1110)) 0], ttuple ([0.0 + recip x1134 * rproject (tproject1 (tproject1 h1110)) 0], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1110)))) 0)) * (x1133 * x1137 + x1133 * x1137)])))) [rproject (tproject2 (tproject1 h1026)) 0] (ttuple ([rreplicate 2 (rproject (tproject1 (tproject1 h1026)) 0)], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h1141 -> ttuple ([rproject (tproject1 h1141) 0 + tan (rproject (tproject2 h1141) 0)], ttuple (tproject1 h1141, []))) (\\h1155 -> let x1171 = cos (rproject (tproject2 (tproject2 h1155)) 0) in ttuple ([rproject (tproject1 (tproject1 h1155)) 0 + rproject (tproject2 (tproject1 h1155)) 0 * recip (x1171 * x1171)], ttuple (tproject1 (tproject1 h1155), []))) (\\h1174 -> let x1198 = cos (rproject (tproject2 (tproject2 h1174)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1174))) 0 + rproject (tproject1 (tproject1 h1174)) 0], [0.0 + recip (x1198 * x1198) * rproject (tproject1 (tproject1 h1174)) 0])) [rproject (tproject2 (tproject2 h1026)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h1026)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h1026)) 0)]))))) 0], ttuple (tproject1 (tproject1 h1026), []))) (\\h1202 -> let h1222 = dmapAccumRDer (SNat @2) (\\h1228 -> let x1235 = cos (rproject (tproject2 (tproject2 (tproject2 h1228))) 0) in ttuple ([0.0 + rproject (tproject1 h1228) 0], [0.0 + recip (x1235 * x1235) * rproject (tproject1 h1228) 0])) (\\h1238 -> let x1250 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1238)))) 0) ; x1251 = x1250 * x1250 ; x1254 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h1238)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1238)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h1238)) 0], [((x1254 * x1250 + x1254 * x1250) * negate (recip (x1251 * x1251))) * rproject (tproject1 (tproject2 h1238)) 0 + rproject (tproject1 (tproject1 h1238)) 0 * recip x1251])) (\\h1258 -> let x1270 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1258)))) 0) ; x1271 = x1270 * x1270 ; x1274 = negate (recip (x1271 * x1271)) * (rproject (tproject1 (tproject2 h1258)) 0 * rproject (tproject2 (tproject1 h1258)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1258)) 0 + recip x1271 * rproject (tproject2 (tproject1 h1258)) 0], ttuple ([], ttuple ([0.0], [0.0 + negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h1258)))) 0)) * (x1270 * x1274 + x1270 * x1274)])))) [rproject (tproject1 (tproject1 h1202)) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h1278 -> ttuple ([rproject (tproject1 h1278) 0 + tan (rproject (tproject2 h1278) 0)], ttuple (tproject1 h1278, []))) (\\h1284 -> let x1291 = cos (rproject (tproject2 (tproject2 h1284)) 0) in ttuple ([rproject (tproject1 (tproject1 h1284)) 0 + rproject (tproject2 (tproject1 h1284)) 0 * recip (x1291 * x1291)], ttuple (tproject1 (tproject1 h1284), []))) (\\h1294 -> let x1302 = cos (rproject (tproject2 (tproject2 h1294)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1294))) 0 + rproject (tproject1 (tproject1 h1294)) 0], [0.0 + recip (x1302 * x1302) * rproject (tproject1 (tproject1 h1294)) 0])) [rproject (tproject2 (tproject2 h1202)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h1202)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h1202)) 0)]))) in ttuple ([0.0 + rproject (tproject1 (tproject2 (tproject1 h1202))) 0 + rsum (rproject (tproject2 h1222) 0)], [0.0 + rproject (tproject1 h1222) 0])) [1.1] [rreplicate 2 1.1])), [rreplicate 2 1.1]))) in [rsum (rproject (tproject2 h16) 0) + rproject (tproject1 h16) 0]"

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 -> let y = rfromD @Double @0 $ x4 V.! 0
                                        w = rfromD @Double @0 $ a4 V.! 0
                                    in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 6103933

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
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 ->
                       dmapAccumL Proxy (SNat @2) shs1 she shs1
                           (\x5 a5 -> let y = rfromD @Double @0 $ x5 V.! 0
                                          w = rfromD @Double @0 $ a5 V.! 0
                                      in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                           (HVectorPseudoTensor $ dmkHVector a4) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x4))
                         (HVectorPseudoTensor $ dmkHVector a3) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x3))
                       (HVectorPseudoTensor $ dmkHVector a2) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x2))
                     (HVectorPseudoTensor $ dmkHVector a) (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) 0.0001)

testSin0MapAccumNestedR5 :: Assertion
testSin0MapAccumNestedR5 = do
 assertEqualUpToEpsilon' 1e-10
  (6.308416949436515e-16 :: OR.Array 0 Double)
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f Double 0 -> f Double 0
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * (y + tan w))
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ x6 V.! 0
                                            w = rfromD @Double @0 $ a6 V.! 0
                                        in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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
                                          let y = rfromD @Double @0 $ x11 V.! 0
                                              w = rfromD @Double @0 $ a11 V.! 0
                                          in ttuple (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
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

productToVectorOf
  :: ADReady f
  => InterpretationTarget f (TKProduct TKUntyped TKUntyped)
  -> HVectorOf f
productToVectorOf p = unHVectorPseudoTensor
                      $ tlet @_ @_ @_ @TKUntyped (tproject1 p) $ \p1 ->
                          tlet (tproject2 p) $ \p2 ->
                            HVectorPseudoTensor $ dmkHVector $ p1 V.++ p2

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

testSin0FoldNestedS5 :: Assertion
testSin0FoldNestedS5 = do
  assertEqualUpToEpsilon' 1e-10
    (0.22000000000000003 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
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

testSin0FoldNestedR41 :: Assertion
testSin0FoldNestedR41 = do
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
        rrev1 @(AstRanked PrimalSpan) @Double @0 @0
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
    @?= 73617

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
  printAstHVectorSimple IM.empty (f @(AstRanked PrimalSpan)
                                    (V.singleton
                                     $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (cos 1.1 * 1.0)])"

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
