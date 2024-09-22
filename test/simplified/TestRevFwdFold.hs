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
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstPretty IM.empty a1
    @?= "let x61 = sin 2.2 ; x65 = 1.1 * x61 ; x66 = recip (3.3 * 3.3 + x65 * x65) ; x103 = sin 2.2 ; x108 = 3.3 * 1.0 ; x109 = (negate 3.3 * x66) * 1.0 in x61 * x109 + x103 * x108"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rlet (sin (rconstant 2.2)) (\\x191 -> rlet (rconstant 1.1 * x191) (\\x195 -> rlet (recip (rconstant 3.3 * rconstant 3.3 + x195 * x195)) (\\x196 -> rlet (sin (rconstant 2.2)) (\\x233 -> rlet (rconstant 3.3 * rconstant 1.0) (\\x238 -> rlet ((negate (rconstant 3.3) * x196) * rconstant 1.0) (\\x239 -> x191 * x239 + x233 * x238))))))"

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

testSin0RfwdPP4Dual :: Assertion
testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "rproject ((\\h23 -> [rproject (tproject1 h23) 0 * cos (rproject (tproject2 h23) 0)]) (ttuple ([rdualPart 1.0], [rproject ((\\h18 -> [rproject (tproject1 h18) 0 * cos (rproject (tproject2 h18) 0)]) (ttuple ([rdualPart 1.0], [rdualPart 1.1]))) 0]))) 0"

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
                        x0 (rrepl @Double @1 [1] 42)) 1.1)

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
    @?= "let h16 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])] [sproject (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sreplicate 1.1] [sreplicate 1.1])) 0, sreplicate 1.1] in rfromS (sreshape (sproject (tproject2 h16) 0)) + rfromS (ssum (sproject (tproject1 h16) 0))"

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
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let v22 = rconst (rfromListLinear [2] [42.0,42.0]) ; v16 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) (\\h24 -> ttuple ([cos (rproject (tproject2 h24) 1) * (rproject (tproject2 h24) 0 + rproject (tproject1 h24) 0)], [0.0])) (\\h41 -> ttuple ([(rproject (tproject2 (tproject1 h41)) 1 * negate (sin (rproject (tproject2 (tproject2 h41)) 1))) * (rproject (tproject2 (tproject2 h41)) 0 + rproject (tproject1 (tproject2 h41)) 0) + (rproject (tproject2 (tproject1 h41)) 0 + rproject (tproject1 (tproject1 h41)) 0) * cos (rproject (tproject2 (tproject2 h41)) 1)], [0.0])) (\\h79 -> let x102 = cos (rproject (tproject2 (tproject2 h79)) 1) * rproject (tproject1 (tproject1 h79)) 0 in ttuple ([0.0 + x102], [0.0 + x102, 0.0 + negate (sin (rproject (tproject2 (tproject2 h79)) 1)) * ((rproject (tproject2 (tproject2 h79)) 0 + rproject (tproject1 (tproject2 h79)) 0) * rproject (tproject1 (tproject1 h79)) 0), 0.0])) [0.0] [rslice 1 2 v16, rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h111 -> let x119 = sin (rproject (tproject1 h111) 0) in ttuple ([x119], [rproject (tproject1 h111) 0, x119])) (\\h121 -> let x135 = rproject (tproject1 (tproject1 h121)) 0 * cos (rproject (tproject1 (tproject2 h121)) 0) in ttuple ([x135], [rproject (tproject1 (tproject1 h121)) 0, x135])) (\\h137 -> ttuple ([cos (rproject (tproject1 (tproject2 h137)) 0) * (rproject (tproject2 (tproject1 h137)) 1 + rproject (tproject1 (tproject1 h137)) 0) + rproject (tproject2 (tproject1 h137)) 0], [0.0])) [1.1] [v22])) 0, v22])) 0 + v16 ! [0]"

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
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "let v14 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h15 -> let x24 = rproject (tproject1 h15) 0 * cos (rproject (tproject2 h15) 1) in ttuple ([x24], [x24])) (\\h25 -> let x36 = rproject (tproject1 (tproject1 h25)) 0 * cos (rproject (tproject2 (tproject2 h25)) 1) + (rproject (tproject2 (tproject1 h25)) 1 * negate (sin (rproject (tproject2 (tproject2 h25)) 1))) * rproject (tproject1 (tproject2 h25)) 0 in ttuple ([x36], [x36])) (\\h40 -> let x50 = rproject (tproject2 (tproject1 h40)) 0 + rproject (tproject1 (tproject1 h40)) 0 in ttuple ([0.0 + cos (rproject (tproject2 (tproject2 h40)) 1) * x50], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h40)) 1)) * (rproject (tproject1 (tproject2 h40)) 0 * x50), 0.0])) [1.0] [rreplicate 2 0.0, rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h54 -> let x58 = sin (rproject (tproject1 h54) 0) in ttuple ([x58], [rproject (tproject1 h54) 0, x58])) (\\h60 -> let x63 = rproject (tproject1 (tproject1 h60)) 0 * cos (rproject (tproject1 (tproject2 h60)) 0) in ttuple ([x63], [rproject (tproject1 (tproject1 h60)) 0, x63])) (\\h65 -> ttuple ([cos (rproject (tproject1 (tproject2 h65)) 0) * (rproject (tproject2 (tproject1 h65)) 1 + rproject (tproject1 (tproject1 h65)) 0) + rproject (tproject2 (tproject1 h65)) 0], [0.0])) [1.1] [v14])) 0, v14])) 0)"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "rproject ((\\h1 -> let v14 = rconst (rfromListLinear [2] [42.0,42.0]) in [rappend (rreplicate 1 (rproject (tproject1 h1) 0)) (rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h15 -> let x24 = rproject (tproject1 h15) 0 * cos (rproject (tproject2 h15) 1) in ttuple ([x24], [x24])) (\\h25 -> let x36 = rproject (tproject1 (tproject1 h25)) 0 * cos (rproject (tproject2 (tproject2 h25)) 1) + (rproject (tproject2 (tproject1 h25)) 1 * negate (sin (rproject (tproject2 (tproject2 h25)) 1))) * rproject (tproject1 (tproject2 h25)) 0 in ttuple ([x36], [x36])) (\\h40 -> let x50 = rproject (tproject2 (tproject1 h40)) 0 + rproject (tproject1 (tproject1 h40)) 0 in ttuple ([0.0 + cos (rproject (tproject2 (tproject2 h40)) 1) * x50], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h40)) 1)) * (rproject (tproject1 (tproject2 h40)) 0 * x50), 0.0])) [rproject (tproject1 h1) 0] [rreplicate 2 0.0, rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h54 -> let x58 = sin (rproject (tproject1 h54) 0) in ttuple ([x58], [rproject (tproject1 h54) 0, x58])) (\\h60 -> let x63 = rproject (tproject1 (tproject1 h60)) 0 * cos (rproject (tproject1 (tproject2 h60)) 0) in ttuple ([x63], [rproject (tproject1 (tproject1 h60)) 0, x63])) (\\h65 -> ttuple ([cos (rproject (tproject1 (tproject2 h65)) 0) * (rproject (tproject2 (tproject1 h65)) 1 + rproject (tproject1 (tproject1 h65)) 0) + rproject (tproject2 (tproject1 h65)) 0], [0.0])) [rproject (tproject2 h1) 0] [v14])) 0, v14])) 0)]) (ttuple ([1.0], [1.1]))) 0"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v22 = rconst (rfromListLinear [2] [5.0,7.0]) ; v16 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v16, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v22])) 0, v22])) 0 + v16 ! [0]"

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
    @?= "\\v10 x14 -> let v12 = rconst (rfromListLinear [2] [5.0,7.0]) in [rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v10, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [x14] [v12])) 0, v12])) 0 + v10 ! [0]]"

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
    @?= "let v26 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) ; v19 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; h23 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v19, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v26])) 0, v26] in 5.0 * rproject (tproject2 h23) 0 ! [0] + 7.0 * rproject (tproject2 h23) 0 ! [1] + rproject (tproject1 h23) 0 + v19 ! [0]"

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
    @?= "let v17 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v17])) 0, v17])) 0)"

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
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h23 -> ttuple ([sproject (tproject1 h23) 0], [0.0])) (\\h32 -> ttuple ([sproject (tproject1 (tproject1 h32)) 0], [0.0])) (\\h40 -> ttuple ([sproject (tproject1 (tproject1 h40)) 0], [0.0, 0.0])) [4.0] [sproject (tproject2 (dmapAccumRDer (SNat @0) (\\h48 -> ttuple ([sproject (tproject1 h48) 0], [sproject (tproject1 h48) 0])) (\\h56 -> ttuple ([sproject (tproject1 (tproject1 h56)) 0], [sproject (tproject1 (tproject1 h56)) 0])) (\\h66 -> ttuple ([0.0 + sproject (tproject2 (tproject1 h66)) 0 + sproject (tproject1 (tproject1 h66)) 0], [0.0])) [1.1] [rconst (rfromListLinear [0] [])])) 0, rconst (rfromListLinear [0] [])])) 0)]"

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
    @?= "[sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] [sproject (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (sfromListLinear [1] [0.0])])) 0, sconst @[1] (sfromListLinear [1] [0.0])])) 0]"

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
    @?= "(\\h1 -> [sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (sproject (tproject1 h1) 0))] [sproject (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 h1) 0] [sconst @[1] (sfromListLinear [1] [0.0])])) 0, sconst @[1] (sfromListLinear [1] [0.0])])) 0]) (ttuple ([sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])], [1.1]))"

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
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rproject (tproject1 (dmapAccumLDer (SNat @1) (\\h22 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h22) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h31 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h31)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h39 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h39)) 0)]), dmkHVector (fromList [DynamicRanked 0.0, DynamicRanked 0.0]))) (dmkHVector (fromList [DynamicRanked (rconstant 4.0)])) (dmkHVector (fromList [DynamicRanked (rproject (tproject2 (dmapAccumRDer (SNat @1) (\\h47 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h47) 0)]), dmkHVector (fromList [DynamicRanked (rproject (tproject1 h47) 0)]))) (\\h55 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h55)) 0)]), dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h55)) 0)]))) (\\h65 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h65)) 0 + rproject (tproject2 (tproject1 h65)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (dmkHVector (fromList [DynamicRanked (rconstant 1.1)])) (dmkHVector (fromList [DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])))) 0), DynamicRanked (rconstant (rconst (rfromListLinear [1] [0.0])))])))) 0)])"

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
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i47, i48] -> [i47, i48])) (\\[i46] -> [i46])) (\\[i45] -> [i45])] [sproject (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0])] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))])) 0, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))])) 0)))]"

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
    @?= "[ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i38, i39] -> [i38, i39])) (\\[i40] -> [i40])) (\\[i41] -> [i41])] [sproject (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))])) 0, stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))])) 0))]"

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
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (rgather [4] (rproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] [rproject (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))])) 0, rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))])) 0) (\\[i34] -> [remF (quotF i34 2) 2, remF i34 2]))]"

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
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v27 = rconst (rfromListLinear [2] [42.0,42.0]) ; v21 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v21, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v27])) 0, v27])) 0 + v21 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v19 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v19])) 0, v19])) 0)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v27 = rconst (rfromListLinear [2] [5.0,7.0]) ; v21 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] [rslice 1 2 v21, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v27])) 0, v27])) 0 + v21 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v19 = rconst (rfromListLinear [2] [5.0,7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rreplicate 2 0.0, rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v19])) 0, v19])) 0)"

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
    @?= 4770

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v22 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] [rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v22])) 0, v22])) 0)"

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
    @?= "let h11 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [sproject (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [sreplicate 1.1])) 0, sreplicate 1.1] in [ssum (sproject (tproject2 h11) 0) + sproject (tproject1 h11) 0]"

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
    @?= "let h16 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [rproject (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1])) 0, rreplicate 11 1.1] in [rsum (rproject (tproject2 h16) 0) + rproject (tproject1 h16) 0]"

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
    @?= "let h16 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> [1.0] [rproject (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> [1.1] [rreplicate 11 1.1])) 0, rreplicate 11 1.1] in [rsum (rproject (tproject2 h16) 0) + rproject (tproject1 h16) 0]"

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
    @?= "let h16 = dmapAccumRDer (SNat @11) (\\h19 -> let h49 = dmapAccumRDer (SNat @22) (\\h52 -> let x72 = cos (rproject (tproject2 h52) 1) in ttuple ([0.0 + rproject (tproject1 h52) 0], [0.0 + recip (x72 * x72) * rproject (tproject1 h52) 0])) (\\h75 -> let x111 = cos (rproject (tproject2 (tproject2 h75)) 1) ; x112 = x111 * x111 ; x117 = rproject (tproject2 (tproject1 h75)) 1 * negate (sin (rproject (tproject2 (tproject2 h75)) 1)) in ttuple ([rproject (tproject1 (tproject1 h75)) 0], [((x117 * x111 + x117 * x111) * negate (recip (x112 * x112))) * rproject (tproject1 (tproject2 h75)) 0 + rproject (tproject1 (tproject1 h75)) 0 * recip x112])) (\\h121 -> let x153 = cos (rproject (tproject2 (tproject2 h121)) 1) ; x154 = x153 * x153 ; x157 = negate (recip (x154 * x154)) * (rproject (tproject1 (tproject2 h121)) 0 * rproject (tproject2 (tproject1 h121)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h121)) 0 + recip x154 * rproject (tproject2 (tproject1 h121)) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h121)) 1)) * (x153 * x157 + x153 * x157)])) [rproject (tproject1 h19) 0] [rproject (tproject2 (dmapAccumLDer (SNat @22) (\\h162 -> ttuple ([rproject (tproject1 h162) 0 + tan (rproject (tproject2 h162) 0)], [rproject (tproject1 h162) 0])) (\\h178 -> let x201 = cos (rproject (tproject2 (tproject2 h178)) 0) in ttuple ([rproject (tproject1 (tproject1 h178)) 0 + rproject (tproject2 (tproject1 h178)) 0 * recip (x201 * x201)], [rproject (tproject1 (tproject1 h178)) 0])) (\\h205 -> let x225 = cos (rproject (tproject2 (tproject2 h205)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h205)) 0 + rproject (tproject1 (tproject1 h205)) 0], [0.0 + recip (x225 * x225) * rproject (tproject1 (tproject1 h205)) 0])) [rproject (tproject2 h19) 1] [rreplicate 22 (rproject (tproject2 h19) 0)])) 0, rreplicate 22 (rproject (tproject2 h19) 0)] in ttuple ([0.0 + rsum (rproject (tproject2 h49) 0)], [0.0 + rproject (tproject1 h49) 0])) (\\h229 -> let h271 = dmapAccumLDer (SNat @22) (\\h298 -> ttuple ([rproject (tproject1 h298) 0 + tan (rproject (tproject2 h298) 0)], [rproject (tproject1 h298) 0, rproject (tproject1 h298) 0])) (\\h314 -> let x331 = cos (rproject (tproject2 (tproject2 h314)) 0) in ttuple ([rproject (tproject1 (tproject1 h314)) 0 + rproject (tproject2 (tproject1 h314)) 0 * recip (x331 * x331)], [rproject (tproject1 (tproject1 h314)) 0, rproject (tproject1 (tproject1 h314)) 0])) (\\h336 -> let x355 = cos (rproject (tproject2 (tproject2 h336)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h336)) 0 + rproject (tproject2 (tproject1 h336)) 1 + rproject (tproject1 (tproject1 h336)) 0], [0.0 + recip (x355 * x355) * rproject (tproject1 (tproject1 h336)) 0])) [rproject (tproject2 (tproject2 h229)) 1] [rreplicate 22 (rproject (tproject2 (tproject2 h229)) 0)] ; h295 = dmapAccumRDer (SNat @22) (\\h362 -> let x394 = cos (rproject (tproject2 h362) 4) ; x395 = x394 * x394 ; x406 = rproject (tproject2 h362) 1 * negate (sin (rproject (tproject2 h362) 4)) in ttuple ([rproject (tproject1 h362) 0], [((x406 * x394 + x406 * x394) * negate (recip (x395 * x395))) * rproject (tproject2 h362) 2 + rproject (tproject1 h362) 0 * recip x395])) (\\h414 -> let x488 = cos (rproject (tproject2 (tproject2 h414)) 4) ; x489 = x488 * x488 ; x495 = negate (sin (rproject (tproject2 (tproject2 h414)) 4)) ; x501 = rproject (tproject2 (tproject2 h414)) 1 * x495 ; x502 = x489 * x489 ; x503 = x501 * x488 + x501 * x488 ; x504 = negate (recip x502) ; x525 = rproject (tproject2 (tproject1 h414)) 1 * x495 + ((rproject (tproject2 (tproject1 h414)) 4 * cos (rproject (tproject2 (tproject2 h414)) 4)) * -1.0) * rproject (tproject2 (tproject2 h414)) 1 ; x536 = rproject (tproject2 (tproject1 h414)) 4 * negate (sin (rproject (tproject2 (tproject2 h414)) 4)) ; x537 = x536 * x488 + x536 * x488 in ttuple ([rproject (tproject1 (tproject1 h414)) 0], [((x525 * x488 + x536 * x501 + x525 * x488 + x536 * x501) * x504 + (((x537 * x489 + x537 * x489) * negate (recip (x502 * x502))) * -1.0) * x503) * rproject (tproject2 (tproject2 h414)) 2 + rproject (tproject2 (tproject1 h414)) 2 * (x503 * x504) + rproject (tproject1 (tproject1 h414)) 0 * recip x489 + (x537 * negate (recip (x489 * x489))) * rproject (tproject1 (tproject2 h414)) 0])) (\\h551 -> let x614 = cos (rproject (tproject2 (tproject2 h551)) 4) ; x615 = x614 * x614 ; x621 = negate (sin (rproject (tproject2 (tproject2 h551)) 4)) ; x627 = rproject (tproject2 (tproject2 h551)) 1 * x621 ; x628 = x615 * x615 ; x629 = x627 * x614 + x627 * x614 ; x630 = negate (recip x628) ; x637 = rproject (tproject2 (tproject2 h551)) 2 * rproject (tproject2 (tproject1 h551)) 0 ; x638 = negate (recip (x628 * x628)) * (-1.0 * (x629 * x637)) ; x639 = x630 * x637 ; x640 = x614 * x639 + x614 * x639 ; x643 = x615 * x638 + x615 * x638 + negate (recip (x615 * x615)) * (rproject (tproject1 (tproject2 h551)) 0 * rproject (tproject2 (tproject1 h551)) 0) in ttuple ([0.0 + recip x615 * rproject (tproject2 (tproject1 h551)) 0 + rproject (tproject1 (tproject1 h551)) 0], [0.0, 0.0 + x621 * x640, 0.0 + (x629 * x630) * rproject (tproject2 (tproject1 h551)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h551)) 4)) * (x614 * x643 + x614 * x643 + x627 * x639 + x627 * x639) + cos (rproject (tproject2 (tproject2 h551)) 4) * (-1.0 * (rproject (tproject2 (tproject2 h551)) 1 * x640))])) [rproject (tproject1 (tproject1 h229)) 0] [rproject (tproject2 (dmapAccumLDer (SNat @22) (\\h662 -> let x672 = cos (rproject (tproject2 h662) 2) in ttuple ([rproject (tproject1 h662) 0 + rproject (tproject2 h662) 0 * recip (x672 * x672)], [rproject (tproject1 h662) 0])) (\\h678 -> let x708 = cos (rproject (tproject2 (tproject2 h678)) 2) ; x709 = x708 * x708 ; x716 = rproject (tproject2 (tproject1 h678)) 2 * negate (sin (rproject (tproject2 (tproject2 h678)) 2)) in ttuple ([rproject (tproject1 (tproject1 h678)) 0 + rproject (tproject2 (tproject1 h678)) 0 * recip x709 + ((x716 * x708 + x716 * x708) * negate (recip (x709 * x709))) * rproject (tproject2 (tproject2 h678)) 0], [rproject (tproject1 (tproject1 h678)) 0])) (\\h725 -> let x751 = cos (rproject (tproject2 (tproject2 h725)) 2) ; x752 = x751 * x751 ; x757 = negate (recip (x752 * x752)) * (rproject (tproject2 (tproject2 h725)) 0 * rproject (tproject1 (tproject1 h725)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h725)) 0 + rproject (tproject2 (tproject1 h725)) 0], [0.0 + recip x752 * rproject (tproject1 (tproject1 h725)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h725)) 2)) * (x751 * x757 + x751 * x757)])) [rproject (tproject2 (tproject1 h229)) 1] [rreplicate 22 (rproject (tproject2 (tproject1 h229)) 0), rproject (tproject2 h271) 0, rreplicate 22 (rproject (tproject2 (tproject2 h229)) 0)])) 0, rreplicate 22 (rproject (tproject2 (tproject1 h229)) 0), rproject (tproject2 (dmapAccumRDer (SNat @22) (\\h764 -> let x784 = cos (rproject (tproject2 h764) 1) in ttuple ([0.0 + rproject (tproject1 h764) 0], [rproject (tproject1 h764) 0, 0.0 + recip (x784 * x784) * rproject (tproject1 h764) 0])) (\\h788 -> let h815 = let x805 = cos (rproject (tproject2 (tproject2 h788)) 1) ; x806 = x805 * x805 ; x811 = rproject (tproject2 (tproject1 h788)) 1 * negate (sin (rproject (tproject2 (tproject2 h788)) 1)) in ttuple ([rproject (tproject1 (tproject1 h788)) 0], [((x811 * x805 + x811 * x805) * negate (recip (x806 * x806))) * rproject (tproject1 (tproject2 h788)) 0 + rproject (tproject1 (tproject1 h788)) 0 * recip x806]) in ttuple (tproject1 h815, [rproject (tproject1 (tproject1 h788)) 0, rproject (tproject2 h815) 0])) (\\h818 -> let h857 = let x846 = cos (rproject (tproject2 (tproject2 h818)) 1) ; x847 = x846 * x846 ; x851 = negate (recip (x847 * x847)) * (rproject (tproject1 (tproject2 h818)) 0 * rproject (tproject2 (tproject1 h818)) 1) in ttuple ([0.0 + rproject (tproject1 (tproject1 h818)) 0 + recip x847 * rproject (tproject2 (tproject1 h818)) 1], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h818)) 1)) * (x846 * x851 + x846 * x851)]) in ttuple ([rproject (tproject1 h857) 0 + rproject (tproject2 (tproject1 h818)) 0], tproject2 h857)) [rproject (tproject1 (tproject2 h229)) 0] [rproject (tproject2 h271) 1, rreplicate 22 (rproject (tproject2 (tproject2 h229)) 0)])) 0, rproject (tproject2 h271) 1, rreplicate 22 (rproject (tproject2 (tproject2 h229)) 0)] in ttuple ([rsum (rproject (tproject2 h295) 0)], [rproject (tproject1 h295) 0])) (\\h861 -> let h901 = dmapAccumLDer (SNat @22) (\\h928 -> ttuple ([rproject (tproject1 h928) 0 + tan (rproject (tproject2 h928) 0)], [rproject (tproject1 h928) 0, rproject (tproject1 h928) 0])) (\\h944 -> let x961 = cos (rproject (tproject2 (tproject2 h944)) 0) in ttuple ([rproject (tproject1 (tproject1 h944)) 0 + rproject (tproject2 (tproject1 h944)) 0 * recip (x961 * x961)], [rproject (tproject1 (tproject1 h944)) 0, rproject (tproject1 (tproject1 h944)) 0])) (\\h966 -> let x985 = cos (rproject (tproject2 (tproject2 h966)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h966)) 0 + rproject (tproject2 (tproject1 h966)) 1 + rproject (tproject1 (tproject1 h966)) 0], [0.0 + recip (x985 * x985) * rproject (tproject1 (tproject1 h966)) 0])) [rproject (tproject2 (tproject2 h861)) 1] [rreplicate 22 (rproject (tproject2 (tproject2 h861)) 0)] ; h915 = dmapAccumLDer (SNat @22) (\\h992 -> let x1021 = cos (rproject (tproject2 h992) 3) ; x1022 = x1021 * x1021 ; x1031 = negate (recip (x1022 * x1022)) * (rproject (tproject2 h992) 1 * rproject (tproject2 h992) 0) in ttuple ([0.0 + rproject (tproject1 h992) 0 + recip x1022 * rproject (tproject2 h992) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 h992) 3)) * (x1021 * x1031 + x1021 * x1031)])) (\\h1041 -> let x1115 = cos (rproject (tproject2 (tproject2 h1041)) 3) ; x1116 = x1115 * x1115 ; x1117 = x1116 * x1116 ; x1118 = negate (recip x1117) ; x1127 = rproject (tproject2 (tproject2 h1041)) 1 * rproject (tproject2 (tproject2 h1041)) 0 ; x1128 = x1118 * x1127 ; x1137 = rproject (tproject2 (tproject1 h1041)) 3 * negate (sin (rproject (tproject2 (tproject2 h1041)) 3)) ; x1138 = x1137 * x1115 + x1137 * x1115 ; x1155 = (((x1138 * x1116 + x1138 * x1116) * negate (recip (x1117 * x1117))) * -1.0) * x1127 + (rproject (tproject2 (tproject1 h1041)) 1 * rproject (tproject2 (tproject2 h1041)) 0 + rproject (tproject2 (tproject1 h1041)) 0 * rproject (tproject2 (tproject2 h1041)) 1) * x1118 in ttuple ([rproject (tproject1 (tproject1 h1041)) 0 + (x1138 * negate (recip (x1116 * x1116))) * rproject (tproject2 (tproject2 h1041)) 0 + rproject (tproject2 (tproject1 h1041)) 0 * recip x1116], [0.0, ((rproject (tproject2 (tproject1 h1041)) 3 * cos (rproject (tproject2 (tproject2 h1041)) 3)) * -1.0) * (x1115 * x1128 + x1115 * x1128) + (x1137 * x1128 + x1155 * x1115 + x1137 * x1128 + x1155 * x1115) * negate (sin (rproject (tproject2 (tproject2 h1041)) 3))])) (\\h1177 -> let x1240 = cos (rproject (tproject2 (tproject2 h1177)) 3) ; x1241 = x1240 * x1240 ; x1242 = x1241 * x1241 ; x1243 = negate (recip x1242) ; x1252 = rproject (tproject2 (tproject2 h1177)) 1 * rproject (tproject2 (tproject2 h1177)) 0 ; x1253 = x1243 * x1252 ; x1260 = negate (sin (rproject (tproject2 (tproject2 h1177)) 3)) * rproject (tproject2 (tproject1 h1177)) 1 ; x1261 = x1240 * x1260 + x1240 * x1260 ; x1262 = x1243 * x1261 ; x1263 = negate (recip (x1242 * x1242)) * (-1.0 * (x1252 * x1261)) ; x1269 = x1241 * x1263 + x1241 * x1263 + negate (recip (x1241 * x1241)) * (rproject (tproject2 (tproject2 h1177)) 0 * rproject (tproject1 (tproject1 h1177)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1177)) 0], [0.0 + rproject (tproject2 (tproject2 h1177)) 1 * x1262 + recip x1241 * rproject (tproject1 (tproject1 h1177)) 0, 0.0 + rproject (tproject2 (tproject2 h1177)) 0 * x1262, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1177)) 3)) * (x1240 * x1269 + x1240 * x1269 + x1253 * x1260 + x1253 * x1260) + cos (rproject (tproject2 (tproject2 h1177)) 3) * (-1.0 * ((x1240 * x1253 + x1240 * x1253) * rproject (tproject2 (tproject1 h1177)) 1))])) [0.0 + rproject (tproject2 (tproject1 h861)) 0] [rconst (rfromListLinear [22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + rreplicate 22 (rproject (tproject1 (tproject1 h861)) 0), rproject (tproject2 (dmapAccumRDer (SNat @22) (\\h1290 -> let x1310 = cos (rproject (tproject2 h1290) 1) in ttuple ([0.0 + rproject (tproject1 h1290) 0], [rproject (tproject1 h1290) 0, 0.0 + recip (x1310 * x1310) * rproject (tproject1 h1290) 0])) (\\h1314 -> let h1354 = let x1344 = cos (rproject (tproject2 (tproject2 h1314)) 1) ; x1345 = x1344 * x1344 ; x1350 = rproject (tproject2 (tproject1 h1314)) 1 * negate (sin (rproject (tproject2 (tproject2 h1314)) 1)) in ttuple ([rproject (tproject1 (tproject1 h1314)) 0], [((x1350 * x1344 + x1350 * x1344) * negate (recip (x1345 * x1345))) * rproject (tproject1 (tproject2 h1314)) 0 + rproject (tproject1 (tproject1 h1314)) 0 * recip x1345]) in ttuple (tproject1 h1354, [rproject (tproject1 (tproject1 h1314)) 0, rproject (tproject2 h1354) 0])) (\\h1357 -> let h1384 = let x1373 = cos (rproject (tproject2 (tproject2 h1357)) 1) ; x1374 = x1373 * x1373 ; x1378 = negate (recip (x1374 * x1374)) * (rproject (tproject1 (tproject2 h1357)) 0 * rproject (tproject2 (tproject1 h1357)) 1) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1357)) 0 + recip x1374 * rproject (tproject2 (tproject1 h1357)) 1], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1357)) 1)) * (x1373 * x1378 + x1373 * x1378)]) in ttuple ([rproject (tproject1 h1384) 0 + rproject (tproject2 (tproject1 h1357)) 0], tproject2 h1384)) [rproject (tproject1 (tproject2 h861)) 0] [rproject (tproject2 h901) 1, rreplicate 22 (rproject (tproject2 (tproject2 h861)) 0)])) 0, rproject (tproject2 h901) 1, rreplicate 22 (rproject (tproject2 (tproject2 h861)) 0)] ; h922 = dmapAccumRDer (SNat @22) (\\h1388 -> let x1398 = cos (rproject (tproject2 h1388) 2) in ttuple ([0.0 + rproject (tproject2 h1388) 0 + rproject (tproject1 h1388) 0], [0.0 + recip (x1398 * x1398) * rproject (tproject1 h1388) 0])) (\\h1404 -> let x1430 = cos (rproject (tproject2 (tproject2 h1404)) 2) ; x1431 = x1430 * x1430 ; x1438 = rproject (tproject2 (tproject1 h1404)) 2 * negate (sin (rproject (tproject2 (tproject2 h1404)) 2)) in ttuple ([rproject (tproject2 (tproject1 h1404)) 0 + rproject (tproject1 (tproject1 h1404)) 0], [((x1438 * x1430 + x1438 * x1430) * negate (recip (x1431 * x1431))) * rproject (tproject1 (tproject2 h1404)) 0 + rproject (tproject1 (tproject1 h1404)) 0 * recip x1431])) (\\h1445 -> let x1467 = cos (rproject (tproject2 (tproject2 h1445)) 2) ; x1468 = x1467 * x1467 ; x1471 = negate (recip (x1468 * x1468)) * (rproject (tproject1 (tproject2 h1445)) 0 * rproject (tproject2 (tproject1 h1445)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1445)) 0 + recip x1468 * rproject (tproject2 (tproject1 h1445)) 0], [0.0 + rproject (tproject1 (tproject1 h1445)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1445)) 2)) * (x1467 * x1471 + x1467 * x1471)])) [0.0] [rproject (tproject2 h915) 0, rproject (tproject2 h901) 0, rreplicate 22 (rproject (tproject2 (tproject2 h861)) 0)] in ttuple ([0.0 + rproject (tproject1 h915) 0], [0.0 + rsum (rproject (tproject2 h922) 0) + rsum (rproject (tproject2 h915) 1), 0.0 + rproject (tproject1 h922) 0])) [1.0] [rproject (tproject2 (dmapAccumLDer (SNat @11) (\\h1478 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @22) (\\h1497 -> ttuple ([rproject (tproject1 h1497) 0 + tan (rproject (tproject2 h1497) 0)], [])) (\\h1504 -> let x1517 = cos (rproject (tproject2 (tproject2 h1504)) 0) in ttuple ([rproject (tproject1 (tproject1 h1504)) 0 + rproject (tproject2 (tproject1 h1504)) 0 * recip (x1517 * x1517)], [])) (\\h1520 -> let x1531 = cos (rproject (tproject2 (tproject2 h1520)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1520)) 0], [0.0 + recip (x1531 * x1531) * rproject (tproject1 (tproject1 h1520)) 0])) [rproject (tproject2 h1478) 0] [rreplicate 22 (rproject (tproject1 h1478) 0)])) 0], [rproject (tproject1 h1478) 0])) (\\h1534 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @22) (\\h1566 -> let x1590 = cos (rproject (tproject2 h1566) 2) in ttuple ([rproject (tproject1 h1566) 0 + rproject (tproject2 h1566) 0 * recip (x1590 * x1590)], [])) (\\h1595 -> let x1644 = cos (rproject (tproject2 (tproject2 h1595)) 2) ; x1645 = x1644 * x1644 ; x1652 = rproject (tproject2 (tproject1 h1595)) 2 * negate (sin (rproject (tproject2 (tproject2 h1595)) 2)) in ttuple ([rproject (tproject1 (tproject1 h1595)) 0 + rproject (tproject2 (tproject1 h1595)) 0 * recip x1645 + ((x1652 * x1644 + x1652 * x1644) * negate (recip (x1645 * x1645))) * rproject (tproject2 (tproject2 h1595)) 0], [])) (\\h1660 -> let x1701 = cos (rproject (tproject2 (tproject2 h1660)) 2) ; x1702 = x1701 * x1701 ; x1707 = negate (recip (x1702 * x1702)) * (rproject (tproject2 (tproject2 h1660)) 0 * rproject (tproject1 (tproject1 h1660)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1660)) 0], [0.0 + recip x1702 * rproject (tproject1 (tproject1 h1660)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1660)) 2)) * (x1701 * x1707 + x1701 * x1707)])) [rproject (tproject2 (tproject1 h1534)) 0] [rreplicate 22 (rproject (tproject1 (tproject1 h1534)) 0), rproject (tproject2 (dmapAccumLDer (SNat @22) (\\h1713 -> ttuple ([rproject (tproject1 h1713) 0 + tan (rproject (tproject2 h1713) 0)], [rproject (tproject1 h1713) 0])) (\\h1729 -> let x1746 = cos (rproject (tproject2 (tproject2 h1729)) 0) in ttuple ([rproject (tproject1 (tproject1 h1729)) 0 + rproject (tproject2 (tproject1 h1729)) 0 * recip (x1746 * x1746)], [rproject (tproject1 (tproject1 h1729)) 0])) (\\h1750 -> let x1774 = cos (rproject (tproject2 (tproject2 h1750)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h1750)) 0 + rproject (tproject1 (tproject1 h1750)) 0], [0.0 + recip (x1774 * x1774) * rproject (tproject1 (tproject1 h1750)) 0])) [rproject (tproject2 (tproject2 h1534)) 0] [rreplicate 22 (rproject (tproject1 (tproject2 h1534)) 0)])) 0, rreplicate 22 (rproject (tproject1 (tproject2 h1534)) 0)])) 0], [rproject (tproject1 (tproject1 h1534)) 0])) (\\h1778 -> let h1800 = dmapAccumRDer (SNat @22) (\\h1806 -> let x1815 = cos (rproject (tproject2 h1806) 1) in ttuple ([0.0 + rproject (tproject1 h1806) 0], [0.0 + recip (x1815 * x1815) * rproject (tproject1 h1806) 0])) (\\h1818 -> let x1834 = cos (rproject (tproject2 (tproject2 h1818)) 1) ; x1835 = x1834 * x1834 ; x1840 = rproject (tproject2 (tproject1 h1818)) 1 * negate (sin (rproject (tproject2 (tproject2 h1818)) 1)) in ttuple ([rproject (tproject1 (tproject1 h1818)) 0], [((x1840 * x1834 + x1840 * x1834) * negate (recip (x1835 * x1835))) * rproject (tproject1 (tproject2 h1818)) 0 + rproject (tproject1 (tproject1 h1818)) 0 * recip x1835])) (\\h1844 -> let x1859 = cos (rproject (tproject2 (tproject2 h1844)) 1) ; x1860 = x1859 * x1859 ; x1863 = negate (recip (x1860 * x1860)) * (rproject (tproject1 (tproject2 h1844)) 0 * rproject (tproject2 (tproject1 h1844)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1844)) 0 + recip x1860 * rproject (tproject2 (tproject1 h1844)) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1844)) 1)) * (x1859 * x1863 + x1859 * x1863)])) [rproject (tproject1 (tproject1 h1778)) 0] [rproject (tproject2 (dmapAccumLDer (SNat @22) (\\h1868 -> ttuple ([rproject (tproject1 h1868) 0 + tan (rproject (tproject2 h1868) 0)], [rproject (tproject1 h1868) 0])) (\\h1876 -> let x1884 = cos (rproject (tproject2 (tproject2 h1876)) 0) in ttuple ([rproject (tproject1 (tproject1 h1876)) 0 + rproject (tproject2 (tproject1 h1876)) 0 * recip (x1884 * x1884)], [rproject (tproject1 (tproject1 h1876)) 0])) (\\h1888 -> let x1896 = cos (rproject (tproject2 (tproject2 h1888)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h1888)) 0 + rproject (tproject1 (tproject1 h1888)) 0], [0.0 + recip (x1896 * x1896) * rproject (tproject1 (tproject1 h1888)) 0])) [rproject (tproject2 (tproject2 h1778)) 0] [rreplicate 22 (rproject (tproject1 (tproject2 h1778)) 0)])) 0, rreplicate 22 (rproject (tproject1 (tproject2 h1778)) 0)] in ttuple ([0.0 + rproject (tproject2 (tproject1 h1778)) 0 + rsum (rproject (tproject2 h1800) 0)], [0.0 + rproject (tproject1 h1800) 0])) [1.1] [rreplicate 11 1.1])) 0, rreplicate 11 1.1] in [rsum (rproject (tproject2 h16) 0) + rproject (tproject1 h16) 0]"

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
    @?= 2518

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
    @?= 26977

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
    @?= 327852

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
    @?= 4707187

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
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
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
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
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
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 123822

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
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h13 = dmapAccumRDer (SNat @2) (\\h16 -> let h41 = dmapAccumRDer (SNat @2) (\\h44 -> let x64 = cos (rproject (tproject2 h44) 1) in ttuple ([0.0 + rproject (tproject1 h44) 0], [0.0 + recip (x64 * x64) * rproject (tproject1 h44) 0])) (\\h67 -> let x103 = cos (rproject (tproject2 (tproject2 h67)) 1) ; x104 = x103 * x103 ; x109 = rproject (tproject2 (tproject1 h67)) 1 * negate (sin (rproject (tproject2 (tproject2 h67)) 1)) in ttuple ([rproject (tproject1 (tproject1 h67)) 0], [((x109 * x103 + x109 * x103) * negate (recip (x104 * x104))) * rproject (tproject1 (tproject2 h67)) 0 + rproject (tproject1 (tproject1 h67)) 0 * recip x104])) (\\h113 -> let x145 = cos (rproject (tproject2 (tproject2 h113)) 1) ; x146 = x145 * x145 ; x149 = negate (recip (x146 * x146)) * (rproject (tproject1 (tproject2 h113)) 0 * rproject (tproject2 (tproject1 h113)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h113)) 0 + recip x146 * rproject (tproject2 (tproject1 h113)) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h113)) 1)) * (x145 * x149 + x145 * x149)])) [rproject (tproject1 h16) 0] [rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h154 -> ttuple ([rproject (tproject1 h154) 0 + tan (rproject (tproject2 h154) 0)], [rproject (tproject1 h154) 0])) (\\h170 -> let x193 = cos (rproject (tproject2 (tproject2 h170)) 0) in ttuple ([rproject (tproject1 (tproject1 h170)) 0 + rproject (tproject2 (tproject1 h170)) 0 * recip (x193 * x193)], [rproject (tproject1 (tproject1 h170)) 0])) (\\h197 -> let x217 = cos (rproject (tproject2 (tproject2 h197)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h197)) 0 + rproject (tproject1 (tproject1 h197)) 0], [0.0 + recip (x217 * x217) * rproject (tproject1 (tproject1 h197)) 0])) [rproject (tproject2 h16) 1] [rreplicate 2 (rproject (tproject2 h16) 0)])) 0, rreplicate 2 (rproject (tproject2 h16) 0)] in ttuple ([0.0 + rsum (rproject (tproject2 h41) 0)], [0.0 + rproject (tproject1 h41) 0])) (\\h221 -> let h263 = dmapAccumLDer (SNat @2) (\\h290 -> ttuple ([rproject (tproject1 h290) 0 + tan (rproject (tproject2 h290) 0)], [rproject (tproject1 h290) 0, rproject (tproject1 h290) 0])) (\\h306 -> let x323 = cos (rproject (tproject2 (tproject2 h306)) 0) in ttuple ([rproject (tproject1 (tproject1 h306)) 0 + rproject (tproject2 (tproject1 h306)) 0 * recip (x323 * x323)], [rproject (tproject1 (tproject1 h306)) 0, rproject (tproject1 (tproject1 h306)) 0])) (\\h328 -> let x347 = cos (rproject (tproject2 (tproject2 h328)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h328)) 0 + rproject (tproject2 (tproject1 h328)) 1 + rproject (tproject1 (tproject1 h328)) 0], [0.0 + recip (x347 * x347) * rproject (tproject1 (tproject1 h328)) 0])) [rproject (tproject2 (tproject2 h221)) 1] [rreplicate 2 (rproject (tproject2 (tproject2 h221)) 0)] ; h287 = dmapAccumRDer (SNat @2) (\\h354 -> let x386 = cos (rproject (tproject2 h354) 4) ; x387 = x386 * x386 ; x398 = rproject (tproject2 h354) 1 * negate (sin (rproject (tproject2 h354) 4)) in ttuple ([rproject (tproject1 h354) 0], [((x398 * x386 + x398 * x386) * negate (recip (x387 * x387))) * rproject (tproject2 h354) 2 + rproject (tproject1 h354) 0 * recip x387])) (\\h406 -> let x480 = cos (rproject (tproject2 (tproject2 h406)) 4) ; x481 = x480 * x480 ; x487 = negate (sin (rproject (tproject2 (tproject2 h406)) 4)) ; x493 = rproject (tproject2 (tproject2 h406)) 1 * x487 ; x494 = x481 * x481 ; x495 = x493 * x480 + x493 * x480 ; x496 = negate (recip x494) ; x517 = rproject (tproject2 (tproject1 h406)) 1 * x487 + ((rproject (tproject2 (tproject1 h406)) 4 * cos (rproject (tproject2 (tproject2 h406)) 4)) * -1.0) * rproject (tproject2 (tproject2 h406)) 1 ; x528 = rproject (tproject2 (tproject1 h406)) 4 * negate (sin (rproject (tproject2 (tproject2 h406)) 4)) ; x529 = x528 * x480 + x528 * x480 in ttuple ([rproject (tproject1 (tproject1 h406)) 0], [((x517 * x480 + x528 * x493 + x517 * x480 + x528 * x493) * x496 + (((x529 * x481 + x529 * x481) * negate (recip (x494 * x494))) * -1.0) * x495) * rproject (tproject2 (tproject2 h406)) 2 + rproject (tproject2 (tproject1 h406)) 2 * (x495 * x496) + rproject (tproject1 (tproject1 h406)) 0 * recip x481 + (x529 * negate (recip (x481 * x481))) * rproject (tproject1 (tproject2 h406)) 0])) (\\h543 -> let x606 = cos (rproject (tproject2 (tproject2 h543)) 4) ; x607 = x606 * x606 ; x613 = negate (sin (rproject (tproject2 (tproject2 h543)) 4)) ; x619 = rproject (tproject2 (tproject2 h543)) 1 * x613 ; x620 = x607 * x607 ; x621 = x619 * x606 + x619 * x606 ; x622 = negate (recip x620) ; x629 = rproject (tproject2 (tproject2 h543)) 2 * rproject (tproject2 (tproject1 h543)) 0 ; x630 = negate (recip (x620 * x620)) * (-1.0 * (x621 * x629)) ; x631 = x622 * x629 ; x632 = x606 * x631 + x606 * x631 ; x635 = x607 * x630 + x607 * x630 + negate (recip (x607 * x607)) * (rproject (tproject1 (tproject2 h543)) 0 * rproject (tproject2 (tproject1 h543)) 0) in ttuple ([0.0 + recip x607 * rproject (tproject2 (tproject1 h543)) 0 + rproject (tproject1 (tproject1 h543)) 0], [0.0, 0.0 + x613 * x632, 0.0 + (x621 * x622) * rproject (tproject2 (tproject1 h543)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h543)) 4)) * (x606 * x635 + x606 * x635 + x619 * x631 + x619 * x631) + cos (rproject (tproject2 (tproject2 h543)) 4) * (-1.0 * (rproject (tproject2 (tproject2 h543)) 1 * x632))])) [rproject (tproject1 (tproject1 h221)) 0] [rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h654 -> let x664 = cos (rproject (tproject2 h654) 2) in ttuple ([rproject (tproject1 h654) 0 + rproject (tproject2 h654) 0 * recip (x664 * x664)], [rproject (tproject1 h654) 0])) (\\h670 -> let x700 = cos (rproject (tproject2 (tproject2 h670)) 2) ; x701 = x700 * x700 ; x708 = rproject (tproject2 (tproject1 h670)) 2 * negate (sin (rproject (tproject2 (tproject2 h670)) 2)) in ttuple ([rproject (tproject1 (tproject1 h670)) 0 + rproject (tproject2 (tproject1 h670)) 0 * recip x701 + ((x708 * x700 + x708 * x700) * negate (recip (x701 * x701))) * rproject (tproject2 (tproject2 h670)) 0], [rproject (tproject1 (tproject1 h670)) 0])) (\\h717 -> let x743 = cos (rproject (tproject2 (tproject2 h717)) 2) ; x744 = x743 * x743 ; x749 = negate (recip (x744 * x744)) * (rproject (tproject2 (tproject2 h717)) 0 * rproject (tproject1 (tproject1 h717)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h717)) 0 + rproject (tproject2 (tproject1 h717)) 0], [0.0 + recip x744 * rproject (tproject1 (tproject1 h717)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h717)) 2)) * (x743 * x749 + x743 * x749)])) [rproject (tproject2 (tproject1 h221)) 1] [rreplicate 2 (rproject (tproject2 (tproject1 h221)) 0), rproject (tproject2 h263) 0, rreplicate 2 (rproject (tproject2 (tproject2 h221)) 0)])) 0, rreplicate 2 (rproject (tproject2 (tproject1 h221)) 0), rproject (tproject2 (dmapAccumRDer (SNat @2) (\\h756 -> let x776 = cos (rproject (tproject2 h756) 1) in ttuple ([0.0 + rproject (tproject1 h756) 0], [rproject (tproject1 h756) 0, 0.0 + recip (x776 * x776) * rproject (tproject1 h756) 0])) (\\h780 -> let h807 = let x797 = cos (rproject (tproject2 (tproject2 h780)) 1) ; x798 = x797 * x797 ; x803 = rproject (tproject2 (tproject1 h780)) 1 * negate (sin (rproject (tproject2 (tproject2 h780)) 1)) in ttuple ([rproject (tproject1 (tproject1 h780)) 0], [((x803 * x797 + x803 * x797) * negate (recip (x798 * x798))) * rproject (tproject1 (tproject2 h780)) 0 + rproject (tproject1 (tproject1 h780)) 0 * recip x798]) in ttuple (tproject1 h807, [rproject (tproject1 (tproject1 h780)) 0, rproject (tproject2 h807) 0])) (\\h810 -> let h849 = let x838 = cos (rproject (tproject2 (tproject2 h810)) 1) ; x839 = x838 * x838 ; x843 = negate (recip (x839 * x839)) * (rproject (tproject1 (tproject2 h810)) 0 * rproject (tproject2 (tproject1 h810)) 1) in ttuple ([0.0 + rproject (tproject1 (tproject1 h810)) 0 + recip x839 * rproject (tproject2 (tproject1 h810)) 1], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h810)) 1)) * (x838 * x843 + x838 * x843)]) in ttuple ([rproject (tproject1 h849) 0 + rproject (tproject2 (tproject1 h810)) 0], tproject2 h849)) [rproject (tproject1 (tproject2 h221)) 0] [rproject (tproject2 h263) 1, rreplicate 2 (rproject (tproject2 (tproject2 h221)) 0)])) 0, rproject (tproject2 h263) 1, rreplicate 2 (rproject (tproject2 (tproject2 h221)) 0)] in ttuple ([rsum (rproject (tproject2 h287) 0)], [rproject (tproject1 h287) 0])) (\\h853 -> let h893 = dmapAccumLDer (SNat @2) (\\h920 -> ttuple ([rproject (tproject1 h920) 0 + tan (rproject (tproject2 h920) 0)], [rproject (tproject1 h920) 0, rproject (tproject1 h920) 0])) (\\h936 -> let x953 = cos (rproject (tproject2 (tproject2 h936)) 0) in ttuple ([rproject (tproject1 (tproject1 h936)) 0 + rproject (tproject2 (tproject1 h936)) 0 * recip (x953 * x953)], [rproject (tproject1 (tproject1 h936)) 0, rproject (tproject1 (tproject1 h936)) 0])) (\\h958 -> let x977 = cos (rproject (tproject2 (tproject2 h958)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h958)) 0 + rproject (tproject2 (tproject1 h958)) 1 + rproject (tproject1 (tproject1 h958)) 0], [0.0 + recip (x977 * x977) * rproject (tproject1 (tproject1 h958)) 0])) [rproject (tproject2 (tproject2 h853)) 1] [rreplicate 2 (rproject (tproject2 (tproject2 h853)) 0)] ; h907 = dmapAccumLDer (SNat @2) (\\h984 -> let x1013 = cos (rproject (tproject2 h984) 3) ; x1014 = x1013 * x1013 ; x1023 = negate (recip (x1014 * x1014)) * (rproject (tproject2 h984) 1 * rproject (tproject2 h984) 0) in ttuple ([0.0 + rproject (tproject1 h984) 0 + recip x1014 * rproject (tproject2 h984) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 h984) 3)) * (x1013 * x1023 + x1013 * x1023)])) (\\h1033 -> let x1107 = cos (rproject (tproject2 (tproject2 h1033)) 3) ; x1108 = x1107 * x1107 ; x1109 = x1108 * x1108 ; x1110 = negate (recip x1109) ; x1119 = rproject (tproject2 (tproject2 h1033)) 1 * rproject (tproject2 (tproject2 h1033)) 0 ; x1120 = x1110 * x1119 ; x1129 = rproject (tproject2 (tproject1 h1033)) 3 * negate (sin (rproject (tproject2 (tproject2 h1033)) 3)) ; x1130 = x1129 * x1107 + x1129 * x1107 ; x1147 = (((x1130 * x1108 + x1130 * x1108) * negate (recip (x1109 * x1109))) * -1.0) * x1119 + (rproject (tproject2 (tproject1 h1033)) 1 * rproject (tproject2 (tproject2 h1033)) 0 + rproject (tproject2 (tproject1 h1033)) 0 * rproject (tproject2 (tproject2 h1033)) 1) * x1110 in ttuple ([rproject (tproject1 (tproject1 h1033)) 0 + (x1130 * negate (recip (x1108 * x1108))) * rproject (tproject2 (tproject2 h1033)) 0 + rproject (tproject2 (tproject1 h1033)) 0 * recip x1108], [0.0, ((rproject (tproject2 (tproject1 h1033)) 3 * cos (rproject (tproject2 (tproject2 h1033)) 3)) * -1.0) * (x1107 * x1120 + x1107 * x1120) + (x1129 * x1120 + x1147 * x1107 + x1129 * x1120 + x1147 * x1107) * negate (sin (rproject (tproject2 (tproject2 h1033)) 3))])) (\\h1169 -> let x1232 = cos (rproject (tproject2 (tproject2 h1169)) 3) ; x1233 = x1232 * x1232 ; x1234 = x1233 * x1233 ; x1235 = negate (recip x1234) ; x1244 = rproject (tproject2 (tproject2 h1169)) 1 * rproject (tproject2 (tproject2 h1169)) 0 ; x1245 = x1235 * x1244 ; x1252 = negate (sin (rproject (tproject2 (tproject2 h1169)) 3)) * rproject (tproject2 (tproject1 h1169)) 1 ; x1253 = x1232 * x1252 + x1232 * x1252 ; x1254 = x1235 * x1253 ; x1255 = negate (recip (x1234 * x1234)) * (-1.0 * (x1244 * x1253)) ; x1261 = x1233 * x1255 + x1233 * x1255 + negate (recip (x1233 * x1233)) * (rproject (tproject2 (tproject2 h1169)) 0 * rproject (tproject1 (tproject1 h1169)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1169)) 0], [0.0 + rproject (tproject2 (tproject2 h1169)) 1 * x1254 + recip x1233 * rproject (tproject1 (tproject1 h1169)) 0, 0.0 + rproject (tproject2 (tproject2 h1169)) 0 * x1254, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1169)) 3)) * (x1232 * x1261 + x1232 * x1261 + x1245 * x1252 + x1245 * x1252) + cos (rproject (tproject2 (tproject2 h1169)) 3) * (-1.0 * ((x1232 * x1245 + x1232 * x1245) * rproject (tproject2 (tproject1 h1169)) 1))])) [0.0 + rproject (tproject2 (tproject1 h853)) 0] [rconst (rfromListLinear [2] [0.0,0.0]) + rreplicate 2 (rproject (tproject1 (tproject1 h853)) 0), rproject (tproject2 (dmapAccumRDer (SNat @2) (\\h1282 -> let x1302 = cos (rproject (tproject2 h1282) 1) in ttuple ([0.0 + rproject (tproject1 h1282) 0], [rproject (tproject1 h1282) 0, 0.0 + recip (x1302 * x1302) * rproject (tproject1 h1282) 0])) (\\h1306 -> let h1346 = let x1336 = cos (rproject (tproject2 (tproject2 h1306)) 1) ; x1337 = x1336 * x1336 ; x1342 = rproject (tproject2 (tproject1 h1306)) 1 * negate (sin (rproject (tproject2 (tproject2 h1306)) 1)) in ttuple ([rproject (tproject1 (tproject1 h1306)) 0], [((x1342 * x1336 + x1342 * x1336) * negate (recip (x1337 * x1337))) * rproject (tproject1 (tproject2 h1306)) 0 + rproject (tproject1 (tproject1 h1306)) 0 * recip x1337]) in ttuple (tproject1 h1346, [rproject (tproject1 (tproject1 h1306)) 0, rproject (tproject2 h1346) 0])) (\\h1349 -> let h1376 = let x1365 = cos (rproject (tproject2 (tproject2 h1349)) 1) ; x1366 = x1365 * x1365 ; x1370 = negate (recip (x1366 * x1366)) * (rproject (tproject1 (tproject2 h1349)) 0 * rproject (tproject2 (tproject1 h1349)) 1) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1349)) 0 + recip x1366 * rproject (tproject2 (tproject1 h1349)) 1], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1349)) 1)) * (x1365 * x1370 + x1365 * x1370)]) in ttuple ([rproject (tproject1 h1376) 0 + rproject (tproject2 (tproject1 h1349)) 0], tproject2 h1376)) [rproject (tproject1 (tproject2 h853)) 0] [rproject (tproject2 h893) 1, rreplicate 2 (rproject (tproject2 (tproject2 h853)) 0)])) 0, rproject (tproject2 h893) 1, rreplicate 2 (rproject (tproject2 (tproject2 h853)) 0)] ; h914 = dmapAccumRDer (SNat @2) (\\h1380 -> let x1390 = cos (rproject (tproject2 h1380) 2) in ttuple ([0.0 + rproject (tproject2 h1380) 0 + rproject (tproject1 h1380) 0], [0.0 + recip (x1390 * x1390) * rproject (tproject1 h1380) 0])) (\\h1396 -> let x1422 = cos (rproject (tproject2 (tproject2 h1396)) 2) ; x1423 = x1422 * x1422 ; x1430 = rproject (tproject2 (tproject1 h1396)) 2 * negate (sin (rproject (tproject2 (tproject2 h1396)) 2)) in ttuple ([rproject (tproject2 (tproject1 h1396)) 0 + rproject (tproject1 (tproject1 h1396)) 0], [((x1430 * x1422 + x1430 * x1422) * negate (recip (x1423 * x1423))) * rproject (tproject1 (tproject2 h1396)) 0 + rproject (tproject1 (tproject1 h1396)) 0 * recip x1423])) (\\h1437 -> let x1459 = cos (rproject (tproject2 (tproject2 h1437)) 2) ; x1460 = x1459 * x1459 ; x1463 = negate (recip (x1460 * x1460)) * (rproject (tproject1 (tproject2 h1437)) 0 * rproject (tproject2 (tproject1 h1437)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1437)) 0 + recip x1460 * rproject (tproject2 (tproject1 h1437)) 0], [0.0 + rproject (tproject1 (tproject1 h1437)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1437)) 2)) * (x1459 * x1463 + x1459 * x1463)])) [0.0] [rproject (tproject2 h907) 0, rproject (tproject2 h893) 0, rreplicate 2 (rproject (tproject2 (tproject2 h853)) 0)] in ttuple ([0.0 + rproject (tproject1 h907) 0], [0.0 + rsum (rproject (tproject2 h914) 0) + rsum (rproject (tproject2 h907) 1), 0.0 + rproject (tproject1 h914) 0])) [1.0] [rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h1470 -> ttuple (tproject1 (dmapAccumLDer (SNat @2) (\\h1480 -> ttuple ([rproject (tproject1 h1480) 0 + tan (rproject (tproject2 h1480) 0)], [])) (\\h1487 -> let x1500 = cos (rproject (tproject2 (tproject2 h1487)) 0) in ttuple ([rproject (tproject1 (tproject1 h1487)) 0 + rproject (tproject2 (tproject1 h1487)) 0 * recip (x1500 * x1500)], [])) (\\h1503 -> let x1514 = cos (rproject (tproject2 (tproject2 h1503)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1503)) 0], [0.0 + recip (x1514 * x1514) * rproject (tproject1 (tproject1 h1503)) 0])) [rproject (tproject2 h1470) 0] [rreplicate 2 (rproject (tproject1 h1470) 0)]), [rproject (tproject1 h1470) 0])) (\\h1517 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @2) (\\h1544 -> let x1568 = cos (rproject (tproject2 h1544) 2) in ttuple ([rproject (tproject1 h1544) 0 + rproject (tproject2 h1544) 0 * recip (x1568 * x1568)], [])) (\\h1573 -> let x1622 = cos (rproject (tproject2 (tproject2 h1573)) 2) ; x1623 = x1622 * x1622 ; x1630 = rproject (tproject2 (tproject1 h1573)) 2 * negate (sin (rproject (tproject2 (tproject2 h1573)) 2)) in ttuple ([rproject (tproject1 (tproject1 h1573)) 0 + rproject (tproject2 (tproject1 h1573)) 0 * recip x1623 + ((x1630 * x1622 + x1630 * x1622) * negate (recip (x1623 * x1623))) * rproject (tproject2 (tproject2 h1573)) 0], [])) (\\h1638 -> let x1679 = cos (rproject (tproject2 (tproject2 h1638)) 2) ; x1680 = x1679 * x1679 ; x1685 = negate (recip (x1680 * x1680)) * (rproject (tproject2 (tproject2 h1638)) 0 * rproject (tproject1 (tproject1 h1638)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1638)) 0], [0.0 + recip x1680 * rproject (tproject1 (tproject1 h1638)) 0, 0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1638)) 2)) * (x1679 * x1685 + x1679 * x1685)])) [rproject (tproject2 (tproject1 h1517)) 0] [rreplicate 2 (rproject (tproject1 (tproject1 h1517)) 0), rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h1691 -> ttuple ([rproject (tproject1 h1691) 0 + tan (rproject (tproject2 h1691) 0)], [rproject (tproject1 h1691) 0])) (\\h1707 -> let x1724 = cos (rproject (tproject2 (tproject2 h1707)) 0) in ttuple ([rproject (tproject1 (tproject1 h1707)) 0 + rproject (tproject2 (tproject1 h1707)) 0 * recip (x1724 * x1724)], [rproject (tproject1 (tproject1 h1707)) 0])) (\\h1728 -> let x1752 = cos (rproject (tproject2 (tproject2 h1728)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h1728)) 0 + rproject (tproject1 (tproject1 h1728)) 0], [0.0 + recip (x1752 * x1752) * rproject (tproject1 (tproject1 h1728)) 0])) [rproject (tproject2 (tproject2 h1517)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h1517)) 0)])) 0, rreplicate 2 (rproject (tproject1 (tproject2 h1517)) 0)])) 0], [rproject (tproject1 (tproject1 h1517)) 0])) (\\h1756 -> let h1778 = dmapAccumRDer (SNat @2) (\\h1784 -> let x1793 = cos (rproject (tproject2 h1784) 1) in ttuple ([0.0 + rproject (tproject1 h1784) 0], [0.0 + recip (x1793 * x1793) * rproject (tproject1 h1784) 0])) (\\h1796 -> let x1812 = cos (rproject (tproject2 (tproject2 h1796)) 1) ; x1813 = x1812 * x1812 ; x1818 = rproject (tproject2 (tproject1 h1796)) 1 * negate (sin (rproject (tproject2 (tproject2 h1796)) 1)) in ttuple ([rproject (tproject1 (tproject1 h1796)) 0], [((x1818 * x1812 + x1818 * x1812) * negate (recip (x1813 * x1813))) * rproject (tproject1 (tproject2 h1796)) 0 + rproject (tproject1 (tproject1 h1796)) 0 * recip x1813])) (\\h1822 -> let x1837 = cos (rproject (tproject2 (tproject2 h1822)) 1) ; x1838 = x1837 * x1837 ; x1841 = negate (recip (x1838 * x1838)) * (rproject (tproject1 (tproject2 h1822)) 0 * rproject (tproject2 (tproject1 h1822)) 0) in ttuple ([0.0 + rproject (tproject1 (tproject1 h1822)) 0 + recip x1838 * rproject (tproject2 (tproject1 h1822)) 0], [0.0, 0.0 + negate (sin (rproject (tproject2 (tproject2 h1822)) 1)) * (x1837 * x1841 + x1837 * x1841)])) [rproject (tproject1 (tproject1 h1756)) 0] [rproject (tproject2 (dmapAccumLDer (SNat @2) (\\h1846 -> ttuple ([rproject (tproject1 h1846) 0 + tan (rproject (tproject2 h1846) 0)], [rproject (tproject1 h1846) 0])) (\\h1854 -> let x1862 = cos (rproject (tproject2 (tproject2 h1854)) 0) in ttuple ([rproject (tproject1 (tproject1 h1854)) 0 + rproject (tproject2 (tproject1 h1854)) 0 * recip (x1862 * x1862)], [rproject (tproject1 (tproject1 h1854)) 0])) (\\h1866 -> let x1874 = cos (rproject (tproject2 (tproject2 h1866)) 0) in ttuple ([0.0 + rproject (tproject2 (tproject1 h1866)) 0 + rproject (tproject1 (tproject1 h1866)) 0], [0.0 + recip (x1874 * x1874) * rproject (tproject1 (tproject1 h1866)) 0])) [rproject (tproject2 (tproject2 h1756)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h1756)) 0)])) 0, rreplicate 2 (rproject (tproject1 (tproject2 h1756)) 0)] in ttuple ([0.0 + rproject (tproject2 (tproject1 h1756)) 0 + rsum (rproject (tproject2 h1778) 0)], [0.0 + rproject (tproject1 h1778) 0])) [1.1] [rreplicate 2 1.1])) 0, rreplicate 2 1.1] in [rsum (rproject (tproject2 h13) 0) + rproject (tproject1 h13) 0]"

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
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4704011

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
    @?= 61743

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
