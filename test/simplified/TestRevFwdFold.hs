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
-- TODO:   , testCase "4Sin0revhFoldZip4R" testSin0revhFoldZip4R
  , testCase "4Sin0revhFoldS" testSin0revhFoldS
  , testCase "4Sin0revhFold2S" testSin0revhFold2S
  , testCase "4Sin0revhFold3S" testSin0revhFold3S
-- TODO: , testCase "4Sin0revhFold4S" testSin0revhFold4S
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
    @?= "let h129 = let x65 = sin 2.2 ; x66 = 1.1 * x65 ; x67 = recip (3.3 * 3.3 + x66 * x66) ; x107 = sin 2.2 ; x109 = 3.3 * 1.0 ; x110 = (negate 3.3 * x67) * 1.0 in [x65 * x110 + x107 * x109, cos 2.2 * (1.1 * x110) + cos 2.2 * (1.1 * x109), (x66 * x67) * 1.0 + (1.1 * x107) * 1.0] in rproject h129 0"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty (simplifyInlineAst a1)
    @?= "rlet (sin 2.2) (\\x194 -> rlet (1.1 * x194) (\\x195 -> x194 * ((negate 3.3 * recip (3.3 * 3.3 + x195 * x195)) * 1.0) + sin 2.2 * (3.3 * 1.0)))"

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
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (ttuple (1.0, 1.1))"

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
    @?= "rsum (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> 1.0 (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> 5.0 (rreplicate 1 1.1))), rreplicate 1 1.1)))))"

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
    @?= "let v5 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])) (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate 1.1) (sreplicate 1.1))), sreplicate 1.1))) in rfromS (ssum (tproject1 v5)) + rfromS (sreshape (tproject2 v5))"

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
    @?= "let v3 = rconst (rfromListLinear [2] [42.0,42.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) (\\x9 -> ttuple (cos (tproject1 (tproject2 (tproject2 x9))) * (tproject1 (tproject2 x9) + tproject1 x9), 0.0)) (\\x15 -> ttuple ((tproject1 (tproject2 (tproject2 (tproject1 x15))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x15)))))) * (tproject1 (tproject2 (tproject2 x15)) + tproject1 (tproject2 x15)) + (tproject1 (tproject2 (tproject1 x15)) + tproject1 (tproject1 x15)) * cos (tproject1 (tproject2 (tproject2 (tproject2 x15)))), 0.0)) (\\x23 -> let x28 = cos (tproject1 (tproject2 (tproject2 (tproject2 x23)))) * tproject1 (tproject1 x23) in ttuple (x28, ttuple (x28, ttuple (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x23))))) * ((tproject1 (tproject2 (tproject2 x23)) + tproject1 (tproject2 x23)) * tproject1 (tproject1 x23)), 0.0)))) 0.0 (ttuple (rslice 1 2 v6, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x29 -> let x32 = sin (tproject1 x29) in ttuple (x32, ttuple (tproject1 x29, x32))) (\\x34 -> let x41 = tproject1 (tproject1 x34) * cos (tproject1 (tproject2 x34)) in ttuple (x41, ttuple (tproject1 (tproject1 x34), x41))) (\\x43 -> ttuple (cos (tproject1 (tproject2 x43)) * (tproject2 (tproject2 (tproject1 x43)) + tproject1 (tproject1 x43)) + tproject1 (tproject2 (tproject1 x43)), 0.0)) 1.1 v3)), v3))))"

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
    @?= "let v4 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in ttuple (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in ttuple (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in ttuple (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, ttuple (0.0, ttuple (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) 1.0 (ttuple (rreplicate 2 0.0, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in ttuple (x35, ttuple (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in ttuple (x38, ttuple (tproject1 (tproject1 x37), x38))) (\\x40 -> ttuple (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) 1.1 v4)), v4)))))"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInlineAst a1)
    @?= "(\\x1 -> let v4 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 (tproject1 x1)) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in ttuple (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in ttuple (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in ttuple (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, ttuple (0.0, ttuple (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) (tproject1 x1) (ttuple (rreplicate 2 0.0, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in ttuple (x35, ttuple (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in ttuple (x38, ttuple (tproject1 (tproject1 x37), x38))) (\\x40 -> ttuple (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) (tproject2 x1) v4)), v4)))))) (ttuple (1.0, 1.1))"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v3 = rconst (rfromListLinear [2] [5.0,7.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (ttuple (rslice 1 2 v6, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))))"

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
    @?= "\\v5 x1 -> let v2 = rconst (rfromListLinear [2] [5.0,7.0]) in v5 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (ttuple (rslice 1 2 v5, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> x1 v2)), v2))))"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0])
                 (rscalar 1.1)
  printArtifactPretty @_ @(TKR Double 1) IM.empty (simplifyArtifact art)
    @?= "\\v3 x1 -> cos x1 * (cos (sin x1 - 5.0) * v3 ! [0]) + cos x1 * v3 ! [1] + v3 ! [2]"

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
    @?= "let v3 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; v7 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (ttuple (rslice 1 2 v6, ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))) in v6 ! [0] + 5.0 * tproject2 v7 ! [0] + 7.0 * tproject2 v7 ! [1] + tproject1 v7"

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
    @?= "let v4 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.0 (ttuple (rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v4)), v4)))))"

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
                => HVector f -> HVector f -> Rep f (TKProduct TKUntyped TKUntyped)
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
              => HVector f -> HVector f -> Rep f (TKProduct TKUntyped TKUntyped)
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
                                  -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                  -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h26 -> ttuple ([sproject (tproject1 h26) 0], [0])) (\\h31 -> ttuple ([sproject (tproject1 (tproject1 h31)) 0], [0.0])) (\\h35 -> ttuple ([sproject (tproject1 (tproject1 h35)) 0], ttuple ([], ttuple ([0], [0])))) [4.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @0) (\\h39 -> ttuple ([sproject (tproject1 h39) 0], ttuple (tproject1 h39, []))) (\\h44 -> ttuple ([sproject (tproject1 (tproject1 h44)) 0], ttuple (tproject1 (tproject1 h44), []))) (\\h51 -> ttuple ([0.0 + sproject (tproject1 (tproject2 (tproject1 h51))) 0 + sproject (tproject1 (tproject1 h51)) 0], [0])) [1.1] [rconst (rfromListLinear [0] [])])), [rconst (rfromListLinear [0] [])]))))) 0)]"

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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "dmkHVector (fromList [DynamicRanked (rproject (tproject1 (dmapAccumLDer (SNat @1) (\\h26 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h26) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (\\h31 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h31)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h35 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h35)) 0)]), ttuple (dmkHVector (fromList []), ttuple (dmkHVector (fromList [DynamicRankedDummy]), dmkHVector (fromList [DynamicRankedDummy]))))) (dmkHVector (fromList [DynamicRanked 4.0])) (ttuple (dmkHVector (fromList []), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) (\\h39 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h39) 0)]), ttuple (tproject1 h39, dmkHVector (fromList [])))) (\\h44 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h44)) 0)]), ttuple (tproject1 (tproject1 h44), dmkHVector (fromList [])))) (\\h51 -> ttuple (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h51)) 0 + rproject (tproject1 (tproject2 (tproject1 h51))) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (dmkHVector (fromList [DynamicRanked 1.1])) (dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))), dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))))) 0)])"

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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "[rfromS (ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i58, i59] -> [i58, i59])) (\\[i57] -> [i57])) (\\[i56] -> [i56])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1])))) + sreplicate (sreplicate 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))]))))) 0)))]"

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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
    @?= "[ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i49, i50] -> [i49, i50])) (\\[i51] -> [i51])) (\\[i52] -> [i52])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))])), [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]))))) 0))]"

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
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "[rsum (rgather [4] (rproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))]))))) 0) (\\[i47] -> [remF (quotF i47 2) 2, remF i47 2]))]"

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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
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
                          => HVector g -> HVector g -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "let v25 = rconst (rfromListLinear [2] [42.0,42.0]) ; v20 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v20], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v25])), [v25]))))) 0 + v20 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v24 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v24])), [v24]))))) 0)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev2 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v28 = rconst (rfromListLinear [2] [5.0,7.0]) ; v26 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (ttuple ([rslice 1 2 v26], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v28])), [v28]))))) 0 + v26 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.Internal.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v24 = rconst (rfromListLinear [2] [5.0,7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rreplicate 2 0.0], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v24])), [v24]))))) 0)"

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
    @?= 3728

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInlineAst a1)
    @?= "let v27 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (ttuple ([rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0])], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v27])), [v27]))))) 0)"

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
                          => HVector g -> HVector g -> Rep g (TKProduct TKUntyped TKUntyped)
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
    @?= "let v6 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (sreplicate 1.1))), sreplicate 1.1))) in [ssum (tproject2 v6) + tproject1 v6]"

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
    @?= "let v7 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v7) + tproject1 v7]"

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
    @?= "let v7 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v7) + tproject1 v7]"

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
    @?= "let v7 = dmapAccumRDer (SNat @11) (\\x8 -> let v17 = dmapAccumRDer (SNat @22) (\\x18 -> let x27 = cos (tproject2 (tproject2 (tproject2 x18))) in ttuple (tproject1 x18, recip (x27 * x27) * tproject1 x18)) (\\x28 -> let x44 = cos (tproject2 (tproject2 (tproject2 (tproject2 x28)))) ; x45 = x44 * x44 ; x46 = tproject2 (tproject2 (tproject2 (tproject1 x28))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x28))))) in ttuple (tproject1 (tproject1 x28), ((x46 * x44 + x46 * x44) * negate (recip (x45 * x45))) * tproject1 (tproject2 x28) + tproject1 (tproject1 x28) * recip x45)) (\\x47 -> let x60 = cos (tproject2 (tproject2 (tproject2 (tproject2 x47)))) ; x61 = x60 * x60 ; x62 = negate (recip (x61 * x61)) * (tproject1 (tproject2 x47) * tproject2 (tproject1 x47)) in ttuple (recip x61 * tproject2 (tproject1 x47) + tproject1 (tproject1 x47), ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x47))))) * (x60 * x62 + x60 * x62))))) (tproject1 x8) (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x63 -> ttuple (tproject1 x63 + tan (tproject2 x63), ttuple (tproject1 x63, []))) (\\x70 -> let x84 = cos (tproject2 (tproject2 x70)) in ttuple (tproject1 (tproject1 x70) + tproject2 (tproject1 x70) * recip (x84 * x84), ttuple (tproject1 (tproject1 x70), []))) (\\x85 -> let x92 = cos (tproject2 (tproject2 x85)) in ttuple (tproject1 (tproject1 x85) + tproject1 (tproject2 (tproject1 x85)), recip (x92 * x92) * tproject1 (tproject1 x85))) (tproject2 (tproject2 (tproject2 x8))) (rreplicate 22 (tproject1 (tproject2 (tproject2 x8)))))), rreplicate 22 (tproject1 (tproject2 (tproject2 x8)))))) in ttuple (rsum (tproject2 v17), tproject1 v17)) (\\x93 -> let v111 = dmapAccumLDer (SNat @22) (\\x113 -> ttuple (tproject1 x113 + tan (tproject2 x113), ttuple (tproject1 x113, ttuple (tproject1 x113, [])))) (\\x120 -> let x129 = cos (tproject2 (tproject2 x120)) in ttuple (tproject1 (tproject1 x120) + tproject2 (tproject1 x120) * recip (x129 * x129), ttuple (tproject1 (tproject1 x120), ttuple (tproject1 (tproject1 x120), [])))) (\\x130 -> let x138 = cos (tproject2 (tproject2 x130)) in ttuple (tproject1 (tproject2 (tproject1 x130)) + tproject1 (tproject1 x130) + tproject1 (tproject2 (tproject2 (tproject1 x130))), recip (x138 * x138) * tproject1 (tproject1 x130))) (tproject2 (tproject2 (tproject2 (tproject2 x93)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x93))))) ; v112 = dmapAccumRDer (SNat @22) (\\x139 -> let x148 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x139))))) ; x149 = x148 * x148 ; x150 = tproject2 (tproject2 (tproject1 (tproject2 x139))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x139)))))) in ttuple (tproject1 x139, ((x150 * x148 + x150 * x148) * negate (recip (x149 * x149))) * tproject1 (tproject2 (tproject2 x139)) + tproject1 x139 * recip x149)) (\\x151 -> let x183 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x151)))))) ; x184 = x183 * x183 ; x185 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x151))))))) ; x186 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x151)))) * x185 ; x187 = x184 * x184 ; x188 = x186 * x183 + x186 * x183 ; x189 = negate (recip x187) ; x190 = tproject2 (tproject2 (tproject1 (tproject2 (tproject1 x151)))) * x185 + ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x151))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x151))))))) * -1.0) * tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x151)))) ; x191 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x151))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x151))))))) ; x192 = x191 * x183 + x191 * x183 in ttuple (tproject1 (tproject1 x151), ((x190 * x183 + x191 * x186 + x190 * x183 + x191 * x186) * x189 + (((x192 * x184 + x192 * x184) * negate (recip (x187 * x187))) * -1.0) * x188) * tproject1 (tproject2 (tproject2 (tproject2 x151))) + tproject1 (tproject2 (tproject2 (tproject1 x151))) * (x188 * x189) + tproject1 (tproject1 x151) * recip x184 + (x192 * negate (recip (x184 * x184))) * tproject1 (tproject2 x151))) (\\x193 -> let x214 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x193)))))) ; x215 = x214 * x214 ; x216 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x193))))))) ; x217 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x193)))) * x216 ; x218 = x215 * x215 ; x219 = x217 * x214 + x217 * x214 ; x220 = negate (recip x218) ; x221 = tproject1 (tproject2 (tproject2 (tproject2 x193))) * tproject2 (tproject1 x193) ; x222 = negate (recip (x218 * x218)) * (-1.0 * (x219 * x221)) ; x223 = x220 * x221 ; x224 = x214 * x223 + x214 * x223 ; x225 = x215 * x222 + x215 * x222 + negate (recip (x215 * x215)) * (tproject1 (tproject2 x193) * tproject2 (tproject1 x193)) in ttuple (recip x215 * tproject2 (tproject1 x193) + tproject1 (tproject1 x193), ttuple (ttuple ([], ttuple (0.0, x216 * x224)), ttuple ((x219 * x220) * tproject2 (tproject1 x193), ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x193))))))) * (x214 * x225 + x214 * x225 + x217 * x223 + x217 * x223) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x193)))))) * (-1.0 * (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x193)))) * x224)))))))) (tproject1 (tproject1 x93)) (ttuple (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x226 -> let x229 = cos (tproject2 (tproject2 (tproject2 x226))) in ttuple (tproject1 x226 + tproject1 (tproject2 x226) * recip (x229 * x229), ttuple (tproject1 x226, []))) (\\x230 -> let x243 = cos (tproject2 (tproject2 (tproject2 (tproject2 x230)))) ; x244 = x243 * x243 ; x245 = tproject2 (tproject2 (tproject2 (tproject1 x230))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x230))))) in ttuple (tproject1 (tproject1 x230) + tproject1 (tproject2 (tproject1 x230)) * recip x244 + ((x245 * x243 + x245 * x243) * negate (recip (x244 * x244))) * tproject1 (tproject2 (tproject2 x230)), ttuple (tproject1 (tproject1 x230), []))) (\\x246 -> let x255 = cos (tproject2 (tproject2 (tproject2 (tproject2 x246)))) ; x256 = x255 * x255 ; x257 = negate (recip (x256 * x256)) * (tproject1 (tproject2 (tproject2 x246)) * tproject1 (tproject1 x246)) in ttuple (tproject1 (tproject1 x246) + tproject1 (tproject2 (tproject1 x246)), ttuple (recip x256 * tproject1 (tproject1 x246), ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x246))))) * (x255 * x257 + x255 * x257))))) (tproject2 (tproject2 (tproject2 (tproject1 x93)))) (ttuple (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x93)))), ttuple (tproject1 (tproject2 v111), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x93))))))))), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x93)))))), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x258 -> let x265 = cos (tproject2 (tproject2 (tproject2 x258))) in ttuple (tproject1 x258, ttuple (tproject1 x258, recip (x265 * x265) * tproject1 x258))) (\\x266 -> let x275 = let x272 = cos (tproject2 (tproject2 (tproject2 (tproject2 x266)))) ; x273 = x272 * x272 ; x274 = tproject2 (tproject2 (tproject2 (tproject1 x266))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x266))))) in ttuple (tproject1 (tproject1 x266), ((x274 * x272 + x274 * x272) * negate (recip (x273 * x273))) * tproject1 (tproject2 x266) + tproject1 (tproject1 x266) * recip x273) in ttuple (tproject1 x275, ttuple (tproject1 (tproject1 x266), tproject2 x275))) (\\x276 -> let x289 = let x286 = cos (tproject2 (tproject2 (tproject2 (tproject2 x276)))) ; x287 = x286 * x286 ; x288 = negate (recip (x287 * x287)) * (tproject1 (tproject2 x276) * tproject2 (tproject2 (tproject1 x276))) in ttuple (recip x287 * tproject2 (tproject2 (tproject1 x276)) + tproject1 (tproject1 x276), ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x276))))) * (x286 * x288 + x286 * x288)))) in ttuple (tproject1 x289 + tproject1 (tproject2 (tproject1 x276)), tproject2 x289)) (tproject1 (tproject2 x93)) (ttuple ([], ttuple (tproject1 (tproject2 (tproject2 v111)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x93))))))))), ttuple ([], ttuple (tproject1 (tproject2 (tproject2 v111)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x93))))))))) in ttuple (rsum (tproject2 v112), tproject1 v112)) (\\x290 -> let v309 = dmapAccumLDer (SNat @22) (\\x312 -> ttuple (tproject1 x312 + tan (tproject2 x312), ttuple (tproject1 x312, ttuple (tproject1 x312, [])))) (\\x319 -> let x328 = cos (tproject2 (tproject2 x319)) in ttuple (tproject1 (tproject1 x319) + tproject2 (tproject1 x319) * recip (x328 * x328), ttuple (tproject1 (tproject1 x319), ttuple (tproject1 (tproject1 x319), [])))) (\\x329 -> let x337 = cos (tproject2 (tproject2 x329)) in ttuple (tproject1 (tproject2 (tproject1 x329)) + tproject1 (tproject1 x329) + tproject1 (tproject2 (tproject2 (tproject1 x329))), recip (x337 * x337) * tproject1 (tproject1 x329))) (tproject2 (tproject2 (tproject2 (tproject2 x290)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x290))))) ; v310 = dmapAccumLDer (SNat @22) (\\x338 -> let x347 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x338))))) ; x348 = x347 * x347 ; x349 = negate (recip (x348 * x348)) * (tproject1 (tproject2 (tproject2 x338)) * tproject1 (tproject2 x338)) in ttuple (recip x348 * tproject1 (tproject2 x338) + tproject1 x338, ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x338)))))) * (x347 * x349 + x347 * x349))))) (\\x350 -> let x382 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x350)))))) ; x383 = x382 * x382 ; x384 = x383 * x383 ; x385 = negate (recip x384) ; x386 = tproject1 (tproject2 (tproject2 (tproject2 x350))) * tproject1 (tproject2 (tproject2 x350)) ; x387 = x385 * x386 ; x388 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x350))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x350))))))) ; x389 = x388 * x382 + x388 * x382 ; x390 = (((x389 * x383 + x389 * x383) * negate (recip (x384 * x384))) * -1.0) * x386 + (tproject1 (tproject2 (tproject2 (tproject1 x350))) * tproject1 (tproject2 (tproject2 x350)) + tproject1 (tproject2 (tproject1 x350)) * tproject1 (tproject2 (tproject2 (tproject2 x350)))) * x385 in ttuple (tproject1 (tproject1 x350) + (x389 * negate (recip (x383 * x383))) * tproject1 (tproject2 (tproject2 x350)) + tproject1 (tproject2 (tproject1 x350)) * recip x383, ttuple ([], ttuple (0.0, ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x350))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x350))))))) * -1.0) * (x382 * x387 + x382 * x387) + (x388 * x387 + x390 * x382 + x388 * x387 + x390 * x382) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x350))))))))))) (\\x391 -> let x412 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x391)))))) ; x413 = x412 * x412 ; x414 = x413 * x413 ; x415 = negate (recip x414) ; x416 = tproject1 (tproject2 (tproject2 (tproject2 x391))) * tproject1 (tproject2 (tproject2 x391)) ; x417 = x415 * x416 ; x418 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x391))))))) * tproject2 (tproject2 (tproject2 (tproject1 x391))) ; x419 = x412 * x418 + x412 * x418 ; x420 = x415 * x419 ; x421 = negate (recip (x414 * x414)) * (-1.0 * (x416 * x419)) ; x422 = x413 * x421 + x413 * x421 + negate (recip (x413 * x413)) * (tproject1 (tproject2 (tproject2 x391)) * tproject1 (tproject1 x391)) in ttuple (tproject1 (tproject1 x391), ttuple (tproject1 (tproject2 (tproject2 (tproject2 x391))) * x420 + recip x413 * tproject1 (tproject1 x391), ttuple (tproject1 (tproject2 (tproject2 x391)) * x420, ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x391))))))) * (x412 * x422 + x412 * x422 + x417 * x418 + x417 * x418) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x391)))))) * (-1.0 * ((x412 * x417 + x412 * x417) * tproject2 (tproject2 (tproject2 (tproject1 x391))))))))))) (0.0 + tproject2 (tproject1 x290)) (ttuple (rconst (rfromListLinear [22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + rreplicate 22 (tproject1 (tproject1 x290)), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x423 -> let x430 = cos (tproject2 (tproject2 (tproject2 x423))) in ttuple (tproject1 x423, ttuple (tproject1 x423, recip (x430 * x430) * tproject1 x423))) (\\x431 -> let x444 = let x441 = cos (tproject2 (tproject2 (tproject2 (tproject2 x431)))) ; x442 = x441 * x441 ; x443 = tproject2 (tproject2 (tproject2 (tproject1 x431))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x431))))) in ttuple (tproject1 (tproject1 x431), ((x443 * x441 + x443 * x441) * negate (recip (x442 * x442))) * tproject1 (tproject2 x431) + tproject1 (tproject1 x431) * recip x442) in ttuple (tproject1 x444, ttuple (tproject1 (tproject1 x431), tproject2 x444))) (\\x445 -> let x454 = let x451 = cos (tproject2 (tproject2 (tproject2 (tproject2 x445)))) ; x452 = x451 * x451 ; x453 = negate (recip (x452 * x452)) * (tproject1 (tproject2 x445) * tproject2 (tproject2 (tproject1 x445))) in ttuple (recip x452 * tproject2 (tproject2 (tproject1 x445)) + tproject1 (tproject1 x445), ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x445))))) * (x451 * x453 + x451 * x453)))) in ttuple (tproject1 x454 + tproject1 (tproject2 (tproject1 x445)), tproject2 x454)) (tproject1 (tproject2 x290)) (ttuple ([], ttuple (tproject1 (tproject2 (tproject2 v309)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x290))))))))), ttuple ([], ttuple (tproject1 (tproject2 (tproject2 v309)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x290))))))))) ; v311 = dmapAccumRDer (SNat @22) (\\x455 -> let x458 = cos (tproject2 (tproject2 (tproject2 x455))) in ttuple (tproject1 x455 + tproject1 (tproject1 (tproject2 x455)), recip (x458 * x458) * tproject1 x455)) (\\x459 -> let x472 = cos (tproject2 (tproject2 (tproject2 (tproject2 x459)))) ; x473 = x472 * x472 ; x474 = tproject2 (tproject2 (tproject2 (tproject1 x459))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x459))))) in ttuple (tproject1 (tproject1 x459) + tproject1 (tproject1 (tproject2 (tproject1 x459))), ((x474 * x472 + x474 * x472) * negate (recip (x473 * x473))) * tproject1 (tproject2 x459) + tproject1 (tproject1 x459) * recip x473)) (\\x475 -> let x484 = cos (tproject2 (tproject2 (tproject2 (tproject2 x475)))) ; x485 = x484 * x484 ; x486 = negate (recip (x485 * x485)) * (tproject1 (tproject2 x475) * tproject2 (tproject1 x475)) in ttuple (tproject1 (tproject1 x475) + recip x485 * tproject2 (tproject1 x475), ttuple (ttuple (tproject1 (tproject1 x475), []), ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x475))))) * (x484 * x486 + x484 * x486))))) 0.0 (ttuple (ttuple (tproject1 (tproject2 (tproject2 v310)), []), ttuple (tproject1 (tproject2 v309), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x290))))))) in ttuple (tproject1 v310, ttuple ([], ttuple (rsum (tproject2 v311) + rsum (tproject2 (tproject2 (tproject2 v310))), tproject1 v311)))) 1.0 (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @11) (\\x487 -> ttuple (tproject1 (dmapAccumLDer (SNat @22) (\\x494 -> ttuple (tproject1 x494 + tan (tproject2 x494), [])) (\\x497 -> let x506 = cos (tproject2 (tproject2 x497)) in ttuple (tproject1 (tproject1 x497) + tproject2 (tproject1 x497) * recip (x506 * x506), [])) (\\x507 -> let x514 = cos (tproject2 (tproject2 x507)) in ttuple (tproject1 (tproject1 x507), recip (x514 * x514) * tproject1 (tproject1 x507))) (tproject2 x487) (rreplicate 22 (tproject1 x487))), ttuple (tproject1 x487, []))) (\\x515 -> ttuple (tproject1 (dmapAccumLDer (SNat @22) (\\x527 -> let x538 = cos (tproject2 (tproject2 (tproject2 x527))) in ttuple (tproject1 x527 + tproject1 (tproject2 x527) * recip (x538 * x538), [])) (\\x539 -> let x556 = cos (tproject2 (tproject2 (tproject2 (tproject2 x539)))) ; x557 = x556 * x556 ; x558 = tproject2 (tproject2 (tproject2 (tproject1 x539))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x539))))) in ttuple (tproject1 (tproject1 x539) + tproject1 (tproject2 (tproject1 x539)) * recip x557 + ((x558 * x556 + x558 * x556) * negate (recip (x557 * x557))) * tproject1 (tproject2 (tproject2 x539)), [])) (\\x559 -> let x572 = cos (tproject2 (tproject2 (tproject2 (tproject2 x559)))) ; x573 = x572 * x572 ; x574 = negate (recip (x573 * x573)) * (tproject1 (tproject2 (tproject2 x559)) * tproject1 (tproject1 x559)) in ttuple (tproject1 (tproject1 x559), ttuple (recip x573 * tproject1 (tproject1 x559), ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x559))))) * (x572 * x574 + x572 * x574))))) (tproject2 (tproject1 x515)) (ttuple (rreplicate 22 (tproject1 (tproject1 x515)), ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x575 -> ttuple (tproject1 x575 + tan (tproject2 x575), ttuple (tproject1 x575, []))) (\\x582 -> let x590 = cos (tproject2 (tproject2 x582)) in ttuple (tproject1 (tproject1 x582) + tproject2 (tproject1 x582) * recip (x590 * x590), ttuple (tproject1 (tproject1 x582), []))) (\\x591 -> let x602 = cos (tproject2 (tproject2 x591)) in ttuple (tproject1 (tproject1 x591) + tproject1 (tproject2 (tproject1 x591)), recip (x602 * x602) * tproject1 (tproject1 x591))) (tproject2 (tproject2 x515)) (rreplicate 22 (tproject1 (tproject2 x515))))), rreplicate 22 (tproject1 (tproject2 x515)))))), ttuple (tproject1 (tproject1 x515), []))) (\\x603 -> let v608 = dmapAccumRDer (SNat @22) (\\x610 -> let x613 = cos (tproject2 (tproject2 (tproject2 x610))) in ttuple (tproject1 x610, recip (x613 * x613) * tproject1 x610)) (\\x614 -> let x619 = cos (tproject2 (tproject2 (tproject2 (tproject2 x614)))) ; x620 = x619 * x619 ; x621 = tproject2 (tproject2 (tproject2 (tproject1 x614))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x614))))) in ttuple (tproject1 (tproject1 x614), ((x621 * x619 + x621 * x619) * negate (recip (x620 * x620))) * tproject1 (tproject2 x614) + tproject1 (tproject1 x614) * recip x620)) (\\x622 -> let x627 = cos (tproject2 (tproject2 (tproject2 (tproject2 x622)))) ; x628 = x627 * x627 ; x629 = negate (recip (x628 * x628)) * (tproject1 (tproject2 x622) * tproject2 (tproject1 x622)) in ttuple (recip x628 * tproject2 (tproject1 x622) + tproject1 (tproject1 x622), ttuple ([], ttuple (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x622))))) * (x627 * x629 + x627 * x629))))) (tproject1 (tproject1 x603)) (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x630 -> ttuple (tproject1 x630 + tan (tproject2 x630), ttuple (tproject1 x630, []))) (\\x632 -> let x635 = cos (tproject2 (tproject2 x632)) in ttuple (tproject1 (tproject1 x632) + tproject2 (tproject1 x632) * recip (x635 * x635), ttuple (tproject1 (tproject1 x632), []))) (\\x636 -> let x639 = cos (tproject2 (tproject2 x636)) in ttuple (tproject1 (tproject1 x636) + tproject1 (tproject2 (tproject1 x636)), recip (x639 * x639) * tproject1 (tproject1 x636))) (tproject2 (tproject2 x603)) (rreplicate 22 (tproject1 (tproject2 x603))))), rreplicate 22 (tproject1 (tproject2 x603))))) in ttuple (rsum (tproject2 v608) + tproject1 (tproject2 (tproject1 x603)), tproject1 v608)) 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v7) + tproject1 v7]"

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
    @?= 1690

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
    @?= 21152

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
    @?= 288976

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
    @?= 4513361

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
                   -- the 7 causes Dummy RepM values
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
    @?= 82738

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
                   -- the 7 causes Dummy RepM values
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
    @?= "let h19 = dmapAccumRDer (SNat @2) (\\h20 -> let h33 = dmapAccumRDer (SNat @2) (\\h34 -> let x43 = cos (rproject (tproject2 (tproject2 (tproject2 h34))) 0) in ttuple ([rproject (tproject1 h34) 0], [recip (x43 * x43) * rproject (tproject1 h34) 0])) (\\h44 -> let x60 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h44)))) 0) ; x61 = x60 * x60 ; x62 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h44)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h44)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h44)) 0], [((x62 * x60 + x62 * x60) * negate (recip (x61 * x61))) * rproject (tproject1 (tproject2 h44)) 0 + rproject (tproject1 (tproject1 h44)) 0 * recip x61])) (\\h63 -> let x76 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h63)))) 0) ; x77 = x76 * x76 ; x78 = negate (recip (x77 * x77)) * (rproject (tproject1 (tproject2 h63)) 0 * rproject (tproject2 (tproject1 h63)) 0) in ttuple ([recip x77 * rproject (tproject2 (tproject1 h63)) 0 + rproject (tproject1 (tproject1 h63)) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h63)))) 0)) * (x76 * x78 + x76 * x78)])))) [rproject (tproject1 h20) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h79 -> ttuple ([rproject (tproject1 h79) 0 + tan (rproject (tproject2 h79) 0)], ttuple (tproject1 h79, []))) (\\h87 -> let x102 = cos (rproject (tproject2 (tproject2 h87)) 0) in ttuple ([rproject (tproject1 (tproject1 h87)) 0 + rproject (tproject2 (tproject1 h87)) 0 * recip (x102 * x102)], ttuple (tproject1 (tproject1 h87), []))) (\\h103 -> let x111 = cos (rproject (tproject2 (tproject2 h103)) 0) in ttuple ([rproject (tproject1 (tproject1 h103)) 0 + rproject (tproject1 (tproject2 (tproject1 h103))) 0], [recip (x111 * x111) * rproject (tproject1 (tproject1 h103)) 0])) [rproject (tproject2 (tproject2 (tproject2 h20))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h20))) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h20))) 0)]))) in ttuple ([rsum (rproject (tproject2 h33) 0)], [rproject (tproject1 h33) 0])) (\\h112 -> let h138 = dmapAccumLDer (SNat @2) (\\h141 -> ttuple ([rproject (tproject1 h141) 0 + tan (rproject (tproject2 h141) 0)], ttuple (tproject1 h141, ttuple (tproject1 h141, [])))) (\\h149 -> let x159 = cos (rproject (tproject2 (tproject2 h149)) 0) in ttuple ([rproject (tproject1 (tproject1 h149)) 0 + rproject (tproject2 (tproject1 h149)) 0 * recip (x159 * x159)], ttuple (tproject1 (tproject1 h149), ttuple (tproject1 (tproject1 h149), [])))) (\\h160 -> let x170 = cos (rproject (tproject2 (tproject2 h160)) 0) in ttuple ([rproject (tproject1 (tproject2 (tproject1 h160))) 0 + rproject (tproject1 (tproject1 h160)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h160)))) 0], [recip (x170 * x170) * rproject (tproject1 (tproject1 h160)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h112)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h112)))) 0)] ; h140 = dmapAccumRDer (SNat @2) (\\h171 -> let x180 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h171))))) 0) ; x181 = x180 * x180 ; x182 = rproject (tproject2 (tproject2 (tproject1 (tproject2 h171)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h171))))) 0)) in ttuple ([rproject (tproject1 h171) 0], [((x182 * x180 + x182 * x180) * negate (recip (x181 * x181))) * rproject (tproject1 (tproject2 (tproject2 h171))) 0 + rproject (tproject1 h171) 0 * recip x181])) (\\h183 -> let x215 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0) ; x216 = x215 * x215 ; x217 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0)) ; x218 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h183))))) 0 * x217 ; x219 = x216 * x216 ; x220 = x218 * x215 + x218 * x215 ; x221 = negate (recip x219) ; x222 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 h183))))) 0 * x217 + ((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h183)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0)) * -1.0) * rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h183))))) 0 ; x223 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h183)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0)) ; x224 = x223 * x215 + x223 * x215 in ttuple ([rproject (tproject1 (tproject1 h183)) 0], [((x222 * x215 + x223 * x218 + x222 * x215 + x223 * x218) * x221 + (((x224 * x216 + x224 * x216) * negate (recip (x219 * x219))) * -1.0) * x220) * rproject (tproject1 (tproject2 (tproject2 (tproject2 h183)))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h183)))) 0 * (x220 * x221) + rproject (tproject1 (tproject1 h183)) 0 * recip x216 + (x224 * negate (recip (x216 * x216))) * rproject (tproject1 (tproject2 h183)) 0])) (\\h225 -> let x246 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h225)))))) 0) ; x247 = x246 * x246 ; x248 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h225)))))) 0)) ; x249 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h225))))) 0 * x248 ; x250 = x247 * x247 ; x251 = x249 * x246 + x249 * x246 ; x252 = negate (recip x250) ; x253 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h225)))) 0 * rproject (tproject2 (tproject1 h225)) 0 ; x254 = negate (recip (x250 * x250)) * (-1.0 * (x251 * x253)) ; x255 = x252 * x253 ; x256 = x246 * x255 + x246 * x255 ; x257 = x247 * x254 + x247 * x254 + negate (recip (x247 * x247)) * (rproject (tproject1 (tproject2 h225)) 0 * rproject (tproject2 (tproject1 h225)) 0) in ttuple ([recip x247 * rproject (tproject2 (tproject1 h225)) 0 + rproject (tproject1 (tproject1 h225)) 0], ttuple (ttuple ([], ttuple ([0], [x248 * x256])), ttuple ([(x251 * x252) * rproject (tproject2 (tproject1 h225)) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h225)))))) 0)) * (x246 * x257 + x246 * x257 + x249 * x255 + x249 * x255) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h225)))))) 0) * (-1.0 * (rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h225))))) 0 * x256))])))))) [rproject (tproject1 (tproject1 h112)) 0] (ttuple (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h258 -> let x261 = cos (rproject (tproject2 (tproject2 (tproject2 h258))) 0) in ttuple ([rproject (tproject1 h258) 0 + rproject (tproject1 (tproject2 h258)) 0 * recip (x261 * x261)], ttuple ([rproject (tproject1 h258) 0], []))) (\\h262 -> let x275 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h262)))) 0) ; x276 = x275 * x275 ; x277 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h262)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h262)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h262)) 0 + rproject (tproject1 (tproject2 (tproject1 h262))) 0 * recip x276 + ((x277 * x275 + x277 * x275) * negate (recip (x276 * x276))) * rproject (tproject1 (tproject2 (tproject2 h262))) 0], ttuple ([rproject (tproject1 (tproject1 h262)) 0], []))) (\\h278 -> let x287 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h278)))) 0) ; x288 = x287 * x287 ; x289 = negate (recip (x288 * x288)) * (rproject (tproject1 (tproject2 (tproject2 h278))) 0 * rproject (tproject1 (tproject1 h278)) 0) in ttuple ([rproject (tproject1 (tproject1 h278)) 0 + rproject (tproject1 (tproject2 (tproject1 h278))) 0], ttuple ([recip x288 * rproject (tproject1 (tproject1 h278)) 0], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h278)))) 0)) * (x287 * x289 + x287 * x289)])))) [rproject (tproject2 (tproject2 (tproject2 (tproject1 h112)))) 0] (ttuple ([rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h112)))) 0)], ttuple (tproject1 (tproject2 h138), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h112)))) 0)])))))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h112)))) 0)])), ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h290 -> let x298 = cos (rproject (tproject2 (tproject2 (tproject2 h290))) 0) in ttuple ([rproject (tproject1 h290) 0], ttuple (tproject1 h290, [recip (x298 * x298) * rproject (tproject1 h290) 0]))) (\\h299 -> let h308 = let x305 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h299)))) 0) ; x306 = x305 * x305 ; x307 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h299)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h299)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h299)) 0], [((x307 * x305 + x307 * x305) * negate (recip (x306 * x306))) * rproject (tproject1 (tproject2 h299)) 0 + rproject (tproject1 (tproject1 h299)) 0 * recip x306]) in ttuple (tproject1 h308, ttuple (tproject1 (tproject1 h299), tproject2 h308))) (\\h309 -> let h322 = let x319 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h309)))) 0) ; x320 = x319 * x319 ; x321 = negate (recip (x320 * x320)) * (rproject (tproject1 (tproject2 h309)) 0 * rproject (tproject2 (tproject2 (tproject1 h309))) 0) in ttuple ([recip x320 * rproject (tproject2 (tproject2 (tproject1 h309))) 0 + rproject (tproject1 (tproject1 h309)) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h309)))) 0)) * (x319 * x321 + x319 * x321)]))) in ttuple ([rproject (tproject1 h322) 0 + rproject (tproject1 (tproject2 (tproject1 h309))) 0], tproject2 h322)) [rproject (tproject1 (tproject2 h112)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h138))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h112)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h138))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h112)))) 0)]))))) in ttuple ([rsum (rproject (tproject2 h140) 0)], [rproject (tproject1 h140) 0])) (\\h323 -> let h352 = dmapAccumLDer (SNat @2) (\\h355 -> ttuple ([rproject (tproject1 h355) 0 + tan (rproject (tproject2 h355) 0)], ttuple (tproject1 h355, ttuple (tproject1 h355, [])))) (\\h363 -> let x373 = cos (rproject (tproject2 (tproject2 h363)) 0) in ttuple ([rproject (tproject1 (tproject1 h363)) 0 + rproject (tproject2 (tproject1 h363)) 0 * recip (x373 * x373)], ttuple (tproject1 (tproject1 h363), ttuple (tproject1 (tproject1 h363), [])))) (\\h374 -> let x384 = cos (rproject (tproject2 (tproject2 h374)) 0) in ttuple ([rproject (tproject1 (tproject2 (tproject1 h374))) 0 + rproject (tproject1 (tproject1 h374)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h374)))) 0], [recip (x384 * x384) * rproject (tproject1 (tproject1 h374)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h323)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h323)))) 0)] ; h353 = dmapAccumLDer (SNat @2) (\\h385 -> let x394 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h385))))) 0) ; x395 = x394 * x394 ; x396 = negate (recip (x395 * x395)) * (rproject (tproject1 (tproject2 (tproject2 h385))) 0 * rproject (tproject1 (tproject2 h385)) 0) in ttuple ([recip x395 * rproject (tproject1 (tproject2 h385)) 0 + rproject (tproject1 h385) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h385))))) 0)) * (x394 * x396 + x394 * x396)])))) (\\h397 -> let x429 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h397)))))) 0) ; x430 = x429 * x429 ; x431 = x430 * x430 ; x432 = negate (recip x431) ; x433 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h397)))) 0 * rproject (tproject1 (tproject2 (tproject2 h397))) 0 ; x434 = x432 * x433 ; x435 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h397)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h397)))))) 0)) ; x436 = x435 * x429 + x435 * x429 ; x437 = (((x436 * x430 + x436 * x430) * negate (recip (x431 * x431))) * -1.0) * x433 + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h397)))) 0 * rproject (tproject1 (tproject2 (tproject2 h397))) 0 + rproject (tproject1 (tproject2 (tproject1 h397))) 0 * rproject (tproject1 (tproject2 (tproject2 (tproject2 h397)))) 0) * x432 in ttuple ([rproject (tproject1 (tproject1 h397)) 0 + (x436 * negate (recip (x430 * x430))) * rproject (tproject1 (tproject2 (tproject2 h397))) 0 + rproject (tproject1 (tproject2 (tproject1 h397))) 0 * recip x430], ttuple ([], ttuple ([0.0], [((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h397)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h397)))))) 0)) * -1.0) * (x429 * x434 + x429 * x434) + (x435 * x434 + x437 * x429 + x435 * x434 + x437 * x429) * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h397)))))) 0))])))) (\\h438 -> let x459 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h438)))))) 0) ; x460 = x459 * x459 ; x461 = x460 * x460 ; x462 = negate (recip x461) ; x463 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h438)))) 0 * rproject (tproject1 (tproject2 (tproject2 h438))) 0 ; x464 = x462 * x463 ; x465 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h438)))))) 0)) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h438)))) 0 ; x466 = x459 * x465 + x459 * x465 ; x467 = x462 * x466 ; x468 = negate (recip (x461 * x461)) * (-1.0 * (x463 * x466)) ; x469 = x460 * x468 + x460 * x468 + negate (recip (x460 * x460)) * (rproject (tproject1 (tproject2 (tproject2 h438))) 0 * rproject (tproject1 (tproject1 h438)) 0) in ttuple ([rproject (tproject1 (tproject1 h438)) 0], ttuple ([rproject (tproject1 (tproject2 (tproject2 (tproject2 h438)))) 0 * x467 + recip x460 * rproject (tproject1 (tproject1 h438)) 0], ttuple ([rproject (tproject1 (tproject2 (tproject2 h438))) 0 * x467], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h438)))))) 0)) * (x459 * x469 + x459 * x469 + x464 * x465 + x464 * x465) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h438)))))) 0) * (-1.0 * ((x459 * x464 + x459 * x464) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h438)))) 0))])))))) [0.0 + rproject (tproject2 (tproject1 h323)) 0] (ttuple ([rconst (rfromListLinear [2] [0.0,0.0]) + rreplicate 2 (rproject (tproject1 (tproject1 h323)) 0)], ttuple (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h470 -> let x478 = cos (rproject (tproject2 (tproject2 (tproject2 h470))) 0) in ttuple ([rproject (tproject1 h470) 0], ttuple (tproject1 h470, [recip (x478 * x478) * rproject (tproject1 h470) 0]))) (\\h479 -> let h492 = let x489 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h479)))) 0) ; x490 = x489 * x489 ; x491 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h479)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h479)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h479)) 0], [((x491 * x489 + x491 * x489) * negate (recip (x490 * x490))) * rproject (tproject1 (tproject2 h479)) 0 + rproject (tproject1 (tproject1 h479)) 0 * recip x490]) in ttuple (tproject1 h492, ttuple (tproject1 (tproject1 h479), tproject2 h492))) (\\h493 -> let h502 = let x499 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h493)))) 0) ; x500 = x499 * x499 ; x501 = negate (recip (x500 * x500)) * (rproject (tproject1 (tproject2 h493)) 0 * rproject (tproject2 (tproject2 (tproject1 h493))) 0) in ttuple ([recip x500 * rproject (tproject2 (tproject2 (tproject1 h493))) 0 + rproject (tproject1 (tproject1 h493)) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h493)))) 0)) * (x499 * x501 + x499 * x501)]))) in ttuple ([rproject (tproject1 h502) 0 + rproject (tproject1 (tproject2 (tproject1 h493))) 0], tproject2 h502)) [rproject (tproject1 (tproject2 h323)) 0] (ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h352))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h323)))) 0)]))))), ttuple ([], ttuple ([rproject (tproject1 (tproject2 (tproject2 h352))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h323)))) 0)]))))) ; h354 = dmapAccumRDer (SNat @2) (\\h503 -> let x506 = cos (rproject (tproject2 (tproject2 (tproject2 h503))) 0) in ttuple ([rproject (tproject1 h503) 0 + rproject (tproject1 (tproject1 (tproject2 h503))) 0], [recip (x506 * x506) * rproject (tproject1 h503) 0])) (\\h507 -> let x520 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h507)))) 0) ; x521 = x520 * x520 ; x522 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h507)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h507)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h507)) 0 + rproject (tproject1 (tproject1 (tproject2 (tproject1 h507)))) 0], [((x522 * x520 + x522 * x520) * negate (recip (x521 * x521))) * rproject (tproject1 (tproject2 h507)) 0 + rproject (tproject1 (tproject1 h507)) 0 * recip x521])) (\\h523 -> let x532 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h523)))) 0) ; x533 = x532 * x532 ; x534 = negate (recip (x533 * x533)) * (rproject (tproject1 (tproject2 h523)) 0 * rproject (tproject2 (tproject1 h523)) 0) in ttuple ([rproject (tproject1 (tproject1 h523)) 0 + recip x533 * rproject (tproject2 (tproject1 h523)) 0], ttuple (ttuple ([rproject (tproject1 (tproject1 h523)) 0], []), ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h523)))) 0)) * (x532 * x534 + x532 * x534)])))) [0.0] (ttuple (ttuple ([rproject (tproject1 (tproject2 (tproject2 h353))) 0], []), ttuple (tproject1 (tproject2 h352), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h323)))) 0)]))) in ttuple ([rproject (tproject1 h353) 0], ttuple ([], ttuple ([rsum (rproject (tproject2 h354) 0) + rsum (rproject (tproject2 (tproject2 (tproject2 h353))) 0)], [rproject (tproject1 h354) 0])))) [1.0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h535 -> let h539 = dmapAccumLDer (SNat @2) (\\h540 -> ttuple ([rproject (tproject1 h540) 0 + tan (rproject (tproject2 h540) 0)], [])) (\\h543 -> let x552 = cos (rproject (tproject2 (tproject2 h543)) 0) in ttuple ([rproject (tproject1 (tproject1 h543)) 0 + rproject (tproject2 (tproject1 h543)) 0 * recip (x552 * x552)], [])) (\\h553 -> let x560 = cos (rproject (tproject2 (tproject2 h553)) 0) in ttuple ([rproject (tproject1 (tproject1 h553)) 0], [recip (x560 * x560) * rproject (tproject1 (tproject1 h553)) 0])) [rproject (tproject2 h535) 0] [rreplicate 2 (rproject (tproject1 h535) 0)] in ttuple (tproject1 h539, ttuple (tproject1 h535, tproject2 h539))) (\\h561 -> ttuple ([rproject (tproject1 (dmapAccumLDer (SNat @2) (\\h579 -> let x590 = cos (rproject (tproject2 (tproject2 (tproject2 h579))) 0) in ttuple ([rproject (tproject1 h579) 0 + rproject (tproject1 (tproject2 h579)) 0 * recip (x590 * x590)], [])) (\\h591 -> let x608 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h591)))) 0) ; x609 = x608 * x608 ; x610 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h591)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h591)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h591)) 0 + rproject (tproject1 (tproject2 (tproject1 h591))) 0 * recip x609 + ((x610 * x608 + x610 * x608) * negate (recip (x609 * x609))) * rproject (tproject1 (tproject2 (tproject2 h591))) 0], [])) (\\h611 -> let x624 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h611)))) 0) ; x625 = x624 * x624 ; x626 = negate (recip (x625 * x625)) * (rproject (tproject1 (tproject2 (tproject2 h611))) 0 * rproject (tproject1 (tproject1 h611)) 0) in ttuple ([rproject (tproject1 (tproject1 h611)) 0], ttuple ([recip x625 * rproject (tproject1 (tproject1 h611)) 0], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h611)))) 0)) * (x624 * x626 + x624 * x626)])))) [rproject (tproject2 (tproject1 h561)) 0] (ttuple ([rreplicate 2 (rproject (tproject1 (tproject1 h561)) 0)], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h627 -> ttuple ([rproject (tproject1 h627) 0 + tan (rproject (tproject2 h627) 0)], ttuple (tproject1 h627, []))) (\\h635 -> let x644 = cos (rproject (tproject2 (tproject2 h635)) 0) in ttuple ([rproject (tproject1 (tproject1 h635)) 0 + rproject (tproject2 (tproject1 h635)) 0 * recip (x644 * x644)], ttuple (tproject1 (tproject1 h635), []))) (\\h645 -> let x657 = cos (rproject (tproject2 (tproject2 h645)) 0) in ttuple ([rproject (tproject1 (tproject1 h645)) 0 + rproject (tproject1 (tproject2 (tproject1 h645))) 0], [recip (x657 * x657) * rproject (tproject1 (tproject1 h645)) 0])) [rproject (tproject2 (tproject2 h561)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h561)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h561)) 0)]))))) 0], ttuple (tproject1 (tproject1 h561), []))) (\\h658 -> let h664 = dmapAccumRDer (SNat @2) (\\h666 -> let x669 = cos (rproject (tproject2 (tproject2 (tproject2 h666))) 0) in ttuple ([rproject (tproject1 h666) 0], [recip (x669 * x669) * rproject (tproject1 h666) 0])) (\\h670 -> let x675 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h670)))) 0) ; x676 = x675 * x675 ; x677 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h670)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h670)))) 0)) in ttuple ([rproject (tproject1 (tproject1 h670)) 0], [((x677 * x675 + x677 * x675) * negate (recip (x676 * x676))) * rproject (tproject1 (tproject2 h670)) 0 + rproject (tproject1 (tproject1 h670)) 0 * recip x676])) (\\h678 -> let x683 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h678)))) 0) ; x684 = x683 * x683 ; x685 = negate (recip (x684 * x684)) * (rproject (tproject1 (tproject2 h678)) 0 * rproject (tproject2 (tproject1 h678)) 0) in ttuple ([recip x684 * rproject (tproject2 (tproject1 h678)) 0 + rproject (tproject1 (tproject1 h678)) 0], ttuple ([], ttuple ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h678)))) 0)) * (x683 * x685 + x683 * x685)])))) [rproject (tproject1 (tproject1 h658)) 0] (ttuple ([], ttuple (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h686 -> ttuple ([rproject (tproject1 h686) 0 + tan (rproject (tproject2 h686) 0)], ttuple (tproject1 h686, []))) (\\h688 -> let x691 = cos (rproject (tproject2 (tproject2 h688)) 0) in ttuple ([rproject (tproject1 (tproject1 h688)) 0 + rproject (tproject2 (tproject1 h688)) 0 * recip (x691 * x691)], ttuple (tproject1 (tproject1 h688), []))) (\\h692 -> let x695 = cos (rproject (tproject2 (tproject2 h692)) 0) in ttuple ([rproject (tproject1 (tproject1 h692)) 0 + rproject (tproject1 (tproject2 (tproject1 h692))) 0], [recip (x695 * x695) * rproject (tproject1 (tproject1 h692)) 0])) [rproject (tproject2 (tproject2 h658)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h658)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h658)) 0)]))) in ttuple ([rsum (rproject (tproject2 h664) 0) + rproject (tproject1 (tproject2 (tproject1 h658))) 0], [rproject (tproject1 h664) 0])) [1.1] [rreplicate 2 1.1])), [rreplicate 2 1.1]))) in [rsum (rproject (tproject2 h19) 0) + rproject (tproject1 h19) 0]"

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
    @?= 5967217

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
        -> Rep f (TKProduct (TKS Float '[1]) (TKR Double 0))
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
  => Rep f (TKProduct TKUntyped TKUntyped)
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
    @?= 43355

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

{-
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
-}

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
{-
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
