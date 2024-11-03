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

import Data.Array.Nested (Rank)
import Data.Array.Nested qualified as Nested

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
  let fHVector :: forall f. ADReady f => HVectorPseudoTensor f Float '() -> f a 0
      fHVector v = foo (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0, rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 1, rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 2)
      sh = []
      zero = voidFromSh @a @0 sh
      shapes = V.fromList [zero, zero, zero]
      domsOf = unHVectorPseudoTensor $ rrev @g fHVector (FTKUntyped shapes)
                    (HVectorPseudoTensor $ dmkHVector $ V.fromList
                       [ DynamicRanked $ rconst @g $ Nested.rscalar x
                       , DynamicRanked $ rconst @g $ Nested.rscalar y
                       , DynamicRanked $ rconst @g $ Nested.rscalar z ])
  in ( tlet @_ @TKUntyped (HVectorPseudoTensor domsOf) (\v -> rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0)
     , tlet @_ @TKUntyped (HVectorPseudoTensor domsOf) (\v -> rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 1)
     , tlet @_ @TKUntyped (HVectorPseudoTensor domsOf) (\v -> rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 2) )

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
  printAstPretty IM.empty (unAstRanked a1)
    @?= "let h44 = let x8 = sin 2.2 ; x10 = 1.1 * x8 ; x11 = recip (3.3 * 3.3 + x10 * x10) ; x17 = sin 2.2 ; x20 = 3.3 * 1.0 ; x21 = (negate 3.3 * x11) * 1.0 in [x8 * x21 + x17 * x20, cos 2.2 * (1.1 * x21) + cos 2.2 * (1.1 * x20), (x10 * x11) * 1.0 + (1.1 * x17) * 1.0] in rproject h44 0"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty (simplifyInline $ unAstRanked a1)
    @?= "tlet (sin 2.2) (\\x52 -> tlet (1.1 * x52) (\\x54 -> x52 * ((negate 3.3 * recip (3.3 * 3.3 + x54 * x54)) * 1.0) + sin 2.2 * (3.3 * 1.0)))"

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
  printAstPretty IM.empty (unAstRanked a1)
    @?= "cos 1.1 * 1.0"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstSimple IM.empty (unAstRanked a1)
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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
  printAstPretty IM.empty (unAstRanked a1)
    @?= "1.0 * cos 1.1"

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "1.0 * cos 1.1"  -- agrees with the rrev1 version above

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (unAstRanked a1)
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (tpair (1.0, 1.1))"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (tpair (1.0, 1.1))"

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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "1.0 * cos (1.0 * cos 1.1)"  -- agrees with the rrev1 version above

testSin0RfwdPP4Dual :: Assertion
testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "(\\x18 -> tproject1 x18 * cos (tproject2 x18)) (tpair (rdualPart 1.0, (\\x14 -> tproject1 x14 * cos (tproject2 x14)) (tpair (rdualPart 1.0, rdualPart 1.1))))"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))  -- agrees with the rrev1 version above
    (rfwd1 @ORArray @Double @0 @0 (rfwd1 sin) (rscalar 1.1))

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @0 (rfwd1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
  printAstPretty IM.empty (simplifyInline $ unAstShaped a1)
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
  printAstPretty IM.empty (unAstRanked a1)
    @?= "rsum (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> 5.0 (rreplicate 1 1.1))), rreplicate 1 1.1)))))"

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
               f x0 = sfold @(RankedOf f) @Double @Double @'[] @'[] @0
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
               f a0 = sfold @(RankedOf f) @Double @Double @'[2, 1] @'[] @2
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
               f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @2
                        (\x _a -> str $ sreplicate @_ @5 $ ssum (str x))
                        (sreplicate @_ @2 (sreplicate @_ @5 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) 1.1)

testSin0Fold8S :: Assertion
testSin0Fold8S = do
  assertEqualUpToEpsilon' 1e-10
    (-2.200311410593445 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
               f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @3
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
                f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @3
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
                     f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @3
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
                f a0 = sfold @(RankedOf f) @Double @Double @'[5] @'[] @1
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
                f a0 = sfold @(RankedOf f) @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1)
  printAstPretty IM.empty (unAstRanked a1)
    @?= "let v5 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sconst @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate 1.1) (sreplicate 1.1))), sreplicate 1.1))) in rfromS (ssum (tproject1 v5)) + rfromS (sreshape (tproject2 v5))"

testSin0Fold18Srev :: Assertion
testSin0Fold18Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.4026418024701366) :: ORArray Double 0)
    (rrev1 (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[2, 5]
                f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @2
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
                f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @3
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
                     f a0 = sfold @(RankedOf f) @Double @Double @'[2, 5] @'[] @3
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
  printAstPrettyButNested IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v3 = rconst (rfromListLinear [2] [42.0,42.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) (\\x9 -> tpair (cos (tproject1 (tproject2 (tproject2 x9))) * (tproject1 (tproject2 x9) + tproject1 x9), 0.0)) (\\x15 -> tpair ((tproject1 (tproject2 (tproject2 (tproject1 x15))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x15)))))) * (tproject1 (tproject2 (tproject2 x15)) + tproject1 (tproject2 x15)) + (tproject1 (tproject2 (tproject1 x15)) + tproject1 (tproject1 x15)) * cos (tproject1 (tproject2 (tproject2 (tproject2 x15)))), 0.0)) (\\x23 -> let x28 = cos (tproject1 (tproject2 (tproject2 (tproject2 x23)))) * tproject1 (tproject1 x23) in tpair (x28, tpair (x28, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x23))))) * ((tproject1 (tproject2 (tproject2 x23)) + tproject1 (tproject2 x23)) * tproject1 (tproject1 x23)), 0.0)))) 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x29 -> let x32 = sin (tproject1 x29) in tpair (x32, tpair (tproject1 x29, x32))) (\\x34 -> let x41 = tproject1 (tproject1 x34) * cos (tproject1 (tproject2 x34)) in tpair (x41, tpair (tproject1 (tproject1 x34), x41))) (\\x43 -> tpair (cos (tproject1 (tproject2 x43)) * (tproject2 (tproject2 (tproject1 x43)) + tproject1 (tproject1 x43)) + tproject1 (tproject2 (tproject1 x43)), 0.0)) 1.1 v3)), v3))))"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v4 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v4 ! [0]) + cos 1.1 * v4 ! [1] + v4 ! [2]"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v4 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in tpair (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in tpair (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in tpair (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, tpair (0.0, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) 1.0 (tpair (rreplicate 2 0.0, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in tpair (x35, tpair (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in tpair (x38, tpair (tproject1 (tproject1 x37), x38))) (\\x40 -> tpair (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) 1.1 v4)), v4)))))"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInline $ unAstRanked a1)
    @?= "(\\x1 -> let v4 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 (tproject1 x1)) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in tpair (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in tpair (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in tpair (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, tpair (0.0, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) (tproject1 x1) (tpair (rreplicate 2 0.0, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in tpair (x35, tpair (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in tpair (x38, tpair (tproject1 (tproject1 x37), x38))) (\\x40 -> tpair (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) (tproject2 x1) v4)), v4)))))) (tpair (1.0, 1.1))"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v3 = rconst (rfromListLinear [2] [5.0,7.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))))"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (Nested.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7])))
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v5 x1 -> let v2 = rconst (rfromListLinear [2] [5.0,7.0]) in v5 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v5, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> x1 v2)), v2))))"

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
                    (rconst (Nested.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) 1.1)

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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v3 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) ; v6 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; v7 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))) in v6 ! [0] + 5.0 * tproject2 v7 ! [0] + 7.0 * tproject2 v7 ! [1] + tproject1 v7"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v4 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) ; x5 = v4 ! [1] ; x6 = v4 ! [0] ; x7 = cos (sin 1.1 - 1.1 * 5.0) * x6 in cos 1.1 * x7 + 5.0 * (-1.0 * x7) + 7.0 * (-1.0 * x6) + cos 1.1 * x5 + 5.0 * (-1.0 * x5) + v4 ! [2]"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v4 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.0 (tpair (rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v4)), v4)))))"

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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
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
    tlet @_ @TKUntyped (HVectorPseudoTensor
      (productToVectorOf $ dmapAccumL Proxy
         snat
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped eShs)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> Rep f (TKProduct TKUntyped TKUntyped)
              g acc e =
               tlet
                (f (rfromD $ acc V.! 0) e)
                (\res -> tpair (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ])
                             (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ]))
          in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
         (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked acc0)
         (HVectorPseudoTensor $ dmkHVector es)))
      (\res -> rappend (rfromList [acc0]) (rfromD $ dunHVector (unHVectorPseudoTensor res) V.! 1))

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
  tlet @_ @TKUntyped (HVectorPseudoTensor
    (productToVectorOf $ dmapAccumL Proxy
       (SNat @k)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped eShs)
       (let g :: forall f. ADReady f
              => HVector f -> HVector f -> Rep f (TKProduct TKUntyped TKUntyped)
            g acc e =
             tlet
                (f (sfromD $ acc V.! 0) e)
                (\res -> tpair (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ])
                             (HVectorPseudoTensor $ dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ]))
        in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
       (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped acc0)
       (HVectorPseudoTensor $ dmkHVector es)))
    (\res -> sappend @_ @_ @1 (sfromList [acc0]) (sfromD $ dunHVector (unHVectorPseudoTensor res) V.! 1))

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
                                  in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (HVectorPseudoTensor $ dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList []))) $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
               f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[]
              f _x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                      (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList []))) $ \_ -> srepl 3
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
                             let x = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor xh) V.! 0
                             in tpair (HVectorPseudoTensor $ dmkHVector
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
                             let x = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor xh) V.! 0
                             in tpair (HVectorPseudoTensor $ dmkHVector
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                        (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                      $ dbuild1 @(RankedOf f) (SNat @6) $ \j ->
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                          in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                      $ dbuild1 @(RankedOf f) (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \j ->
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
               f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromR x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [0]) [] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
           in f) 1.1)

testSin0rmapAccumRD01SN531bS :: Assertion
testSin0rmapAccumRD01SN531bS = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2]
               f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN531bR :: Assertion
testSin0rmapAccumRD01SN531bR = do
  assertEqualUpToEpsilon' 1e-10
    4
    (rev' (let f :: forall f. ADReady f
                 => f Double 0 -> f Double 2
               f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked x0 ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [1]) [0] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
           in f) 1.1)

testSin0rmapAccumRD01SN531b0PP :: Assertion
testSin0rmapAccumRD01SN531b0PP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVectorPseudoTensor f Float '() -> f Double 2
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromD (dunHVector (unHVectorPseudoTensor x0) V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [0]) [] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor . rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . HVectorPseudoTensor . dmkHVector
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h25 -> tpair ([sproject (tproject1 h25) 0], [0])) (\\h29 -> tpair ([sproject (tproject1 (tproject1 h29)) 0], [0.0])) (\\h32 -> tpair ([sproject (tproject1 (tproject1 h32)) 0], tpair ([], tpair ([0], [0])))) [4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) (\\h35 -> tpair ([sproject (tproject1 h35) 0], tpair (tproject1 h35, []))) (\\h39 -> tpair ([sproject (tproject1 (tproject1 h39)) 0], tpair (tproject1 (tproject1 h39), []))) (\\h45 -> tpair ([sproject (tproject1 (tproject1 h45)) 0 + sproject (tproject1 (tproject2 (tproject1 h45))) 0], [0])) [1.1] [rconst (rfromListLinear [0] [])])), [rconst (rfromListLinear [0] [])]))))) 0)]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVectorPseudoTensor  (RankedOf f) Float '() -> f Double '[2, 2]
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          x0
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor
          . srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . HVectorPseudoTensor . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconst @[1] (sfromListLinear [1] [0.0])])), [sconst @[1] (sfromListLinear [1] [0.0])]))))) 0]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVectorPseudoTensor  (RankedOf f) Float '() -> f Double '[2, 2]
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          x0
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor
          . srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . HVectorPseudoTensor . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "(\\m1 -> [sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (tproject1 m1))] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 m1) 0] [sconst @[1] (sfromListLinear [1] [0.0])])), [sconst @[1] (sfromListLinear [1] [0.0])]))))) 0]) (tpair (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]), [1.1]))"

testSin0rmapAccumRD01SN531bRPP :: Assertion
testSin0rmapAccumRD01SN531bRPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVectorPseudoTensor f Float '() -> f Double 2
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          x0
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [1]) [0] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor . rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . HVectorPseudoTensor . dmkHVector
  printAstSimple
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rproject (tproject1 (dmapAccumLDer (SNat @1) (\\h25 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h25) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (\\h29 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h29)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h32 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h32)) 0)]), tpair (dmkHVector (fromList []), tpair (dmkHVector (fromList [DynamicRankedDummy]), dmkHVector (fromList [DynamicRankedDummy]))))) (dmkHVector (fromList [DynamicRanked 4.0])) (tpair (dmkHVector (fromList []), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) (\\h35 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h35) 0)]), tpair (tproject1 h35, dmkHVector (fromList [])))) (\\h39 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h39)) 0)]), tpair (tproject1 (tproject1 h39), dmkHVector (fromList [])))) (\\h45 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h45)) 0 + rproject (tproject1 (tproject2 (tproject1 h45))) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (dmkHVector (fromList [DynamicRanked 1.1])) (dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))), dmkHVector (fromList [DynamicRanked (rconst (rfromListLinear [1] [0.0]))])))))) 0)])"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVectorPseudoTensor f Float '() -> f Double 2
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (dunHVector (unHVectorPseudoTensor x0) V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [0]) [] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor . rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . HVectorPseudoTensor . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i48, i49] -> [i48, i49])) (\\[i50] -> [i50])) (\\[i51] -> [i51])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [0] []))))]))))) 0)))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReadyS f
        => HVectorPseudoTensor  (RankedOf f) Float '() -> f Double '[2, 2]
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @(RankedOf f) (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sconstant (sfromR (i + j)))
                                 + sfromD (dunHVector (unHVectorPseudoTensor x0) V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. ADReady g => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor
          . srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . HVectorPseudoTensor . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconst @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i49, i50] -> [i49, i50])) (\\[i51] -> [i51])) (\\[i52] -> [i52])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconst @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sfromR (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))))] [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))])), [stranspose (sreplicate (sreplicate (sconst @[1] (sfromListLinear [1] [0.0]))))]))))) 0))]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => HVectorPseudoTensor f Float '() -> f Double 2
      f x0 = tlet @_ @TKUntyped (HVectorPseudoTensor
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> Rep g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (HVectorPseudoTensor $ dmkHVector xh)
                                            (HVectorPseudoTensor $ dmkHVector V.empty)

                           in \x y -> h (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList
                             [ DynamicRanked @Double @0
                               $ rfromIntegral (rconstant (i + j))
                                 + rfromD (dunHVector (unHVectorPseudoTensor x0) V.! 0) ])
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconst $ Nested.rfromListPrimLinear (fromList [1]) [0] ])))))
                        $ \ !d -> rfromD $ dunHVector (unHVectorPseudoTensor d) V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g = unHVectorPseudoTensor . rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . HVectorPseudoTensor . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (rsum (rproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconst (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rtranspose [1,0] (rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rconst (rfromListLinear [2] [0,1]))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconst (rfromListLinear [1] [0.0]))))]))))) 0))]"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (-1.8866871148429984)
    (rev' (let f :: forall f. ADReadyS f
                 => f Double '[] -> f Double '[2, 2, 2]
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 1))
                      $ dunHVector
                      $ dbuild1 @(RankedOf f) (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                         (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                      $ dbuild1 @(RankedOf f) (SNat @2) $ \i ->
                       (dbuild1 @(RankedOf f) (SNat @0) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                            in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                      $ dbuild1 @(RankedOf f) (SNat @2) $ \_i ->
                       (dbuild1 @(RankedOf f) (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @(RankedOf f)) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReadyS g
                                 => HVector (RankedOf g) -> HVector (RankedOf g)
                                 -> Rep (RankedOf g) (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (HVectorPseudoTensor $ dmkHVector
                                   $ V.fromList [ DynamicShaped x ])
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sin x - sfromD (a V.! 2) ])
                                           (HVectorPseudoTensor $ dmkHVector V.empty)
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                in tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                            (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in rfromS . f . sfromR) 1.1)

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[2] knownShS [0.4989557335681351,1.1])
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x])
                                           (HVectorPseudoTensor $ dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1)])
                                           (HVectorPseudoTensor $ dmkHVector
                                      [ DynamicShaped x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
                          (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicShaped x0)
                          (HVectorPseudoTensor $ dmkHVector $ V.fromList [DynamicShaped @Double @'[5] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (sconst $ Nested.sfromListPrimLinear @_ @'[1] knownShS [1.1])
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
                                 in tpair (HVectorPseudoTensor $ dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                       (HVectorPseudoTensor $ dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                                  tpair (HVectorPseudoTensor $ dmkHVector
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
                           in \x y -> g (dunHVector (unHVectorPseudoTensor x)) (dunHVector (unHVectorPseudoTensor y)))
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
                          => HVectorPseudoTensor g Float '() -> HVectorPseudoTensor g Float '() -> Rep g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @5 $ dunHVector (unHVectorPseudoTensor xh) V.! 0
                         in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector (unHVectorPseudoTensor a)))))
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
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v25 = rconst (rfromListLinear [2] [42.0,42.0]) ; v20 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (tpair ([rslice 1 2 v20], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v25])), [v25]))))) 0 + v20 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v24 = rconst (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rreplicate 2 0.0], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v24])), [v24]))))) 0)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev2 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (Nested.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v25 = rconst (rfromListLinear [2] [5.0,7.0]) ; v20 = rconst (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (tpair ([rslice 1 2 v20], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v25])), [v25]))))) 0 + v20 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (Nested.rfromListPrimLinear @Double @1 (fromList [2]) [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v24 = rconst (rfromListLinear [2] [5.0,7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rreplicate 2 0.0], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v24])), [v24]))))) 0)"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [2.417297824578748] :: OR.Array 0 Double)
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconst (Nested.sfromListPrimLinear @Double @'[2, 2] knownShS [5, 7, 3, 4])
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
  length (printAstSimple IM.empty (simplifyInline $ unAstRanked a1))
    @?= 3718

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline $ unAstRanked a1)
    @?= "let v27 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0])], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v27])), [v27]))))) 0)"

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
                          => HVectorPseudoTensor g Float '() -> HVectorPseudoTensor g Float '() -> Rep g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @2 $ dunHVector (unHVectorPseudoTensor xh) V.! 0
                         in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector (unHVectorPseudoTensor a)))))
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
      g x = unHVectorPseudoTensor $
            srev (\v -> f (sfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
                 (HVectorPseudoTensor $ dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstRanked PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let v6 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (sreplicate 1.1))), sreplicate 1.1))) in [ssum (tproject2 v6) + tproject1 v6]"

testSin0FoldNestedR1PP :: Assertion
testSin0FoldNestedR1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor
            $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (HVectorPseudoTensor $ dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR1SimpPP :: Assertion
testSin0FoldNestedR1SimpPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor
            $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (HVectorPseudoTensor $ dmkHVector x)
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR1SimpNestedPP :: Assertion
testSin0FoldNestedR1SimpNestedPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor
            $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (HVectorPseudoTensor $ dmkHVector x)
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) (\\x7 -> let v14 = dmapAccumRDer (SNat @22) (\\x15 -> let x22 = cos (tproject2 (tproject2 (tproject2 x15))) in tpair (tproject1 x15, recip (x22 * x22) * tproject1 x15)) (\\x23 -> let x35 = cos (tproject2 (tproject2 (tproject2 (tproject2 x23)))) ; x36 = x35 * x35 ; x37 = tproject2 (tproject2 (tproject2 (tproject1 x23))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x23))))) in tpair (tproject1 (tproject1 x23), ((x37 * x35 + x37 * x35) * negate (recip (x36 * x36))) * tproject1 (tproject2 x23) + tproject1 (tproject1 x23) * recip x36)) (\\x38 -> let x47 = cos (tproject2 (tproject2 (tproject2 (tproject2 x38)))) ; x48 = x47 * x47 ; x49 = negate (recip (x48 * x48)) * (tproject1 (tproject2 x38) * tproject2 (tproject1 x38)) in tpair (recip x48 * tproject2 (tproject1 x38) + tproject1 (tproject1 x38), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x38))))) * (x47 * x49 + x47 * x49))))) (tproject1 x7) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x50 -> tpair (tproject1 x50 + tan (tproject2 x50), tpair (tproject1 x50, []))) (\\x56 -> let x68 = cos (tproject2 (tproject2 x56)) in tpair (tproject1 (tproject1 x56) + tproject2 (tproject1 x56) * recip (x68 * x68), tpair (tproject1 (tproject1 x56), []))) (\\x69 -> let x74 = cos (tproject2 (tproject2 x69)) in tpair (tproject1 (tproject1 x69) + tproject1 (tproject2 (tproject1 x69)), recip (x74 * x74) * tproject1 (tproject1 x69))) (tproject2 (tproject2 (tproject2 x7))) (rreplicate 22 (tproject1 (tproject2 (tproject2 x7)))))), rreplicate 22 (tproject1 (tproject2 (tproject2 x7)))))) in tpair (rsum (tproject2 v14), tproject1 v14)) (\\x75 -> let v79 = dmapAccumLDer (SNat @22) (\\x92 -> tpair (tproject1 x92 + tan (tproject2 x92), tpair (tproject1 x92, tpair (tproject1 x92, [])))) (\\x98 -> let x101 = cos (tproject2 (tproject2 x98)) in tpair (tproject1 (tproject1 x98) + tproject2 (tproject1 x98) * recip (x101 * x101), tpair (tproject1 (tproject1 x98), tpair (tproject1 (tproject1 x98), [])))) (\\x106 -> let x109 = cos (tproject2 (tproject2 x106)) in tpair (tproject1 (tproject2 (tproject1 x106)) + tproject1 (tproject1 x106) + tproject1 (tproject2 (tproject2 (tproject1 x106))), recip (x109 * x109) * tproject1 (tproject1 x106))) (tproject2 (tproject2 (tproject2 (tproject2 x75)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))) ; v89 = dmapAccumRDer (SNat @22) (\\x113 -> let x118 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x113))))) ; x119 = x118 * x118 ; x120 = tproject2 (tproject2 (tproject1 (tproject2 x113))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x113)))))) in tpair (tproject1 x113, ((x120 * x118 + x120 * x118) * negate (recip (x119 * x119))) * tproject1 (tproject2 (tproject2 x113)) + tproject1 x113 * recip x119)) (\\x121 -> let x127 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x121)))))) ; x128 = x127 * x127 ; x129 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x121))))))) ; x130 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x121)))) * x129 ; x131 = x128 * x128 ; x132 = x130 * x127 + x130 * x127 ; x133 = negate (recip x131) ; x138 = tproject2 (tproject2 (tproject1 (tproject2 (tproject1 x121)))) * x129 + ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x121))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x121))))))) * -1.0) * tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x121)))) ; x139 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x121))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x121))))))) ; x143 = x139 * x127 + x139 * x127 in tpair (tproject1 (tproject1 x121), ((x138 * x127 + x139 * x130 + x138 * x127 + x139 * x130) * x133 + (((x143 * x128 + x143 * x128) * negate (recip (x131 * x131))) * -1.0) * x132) * tproject1 (tproject2 (tproject2 (tproject2 x121))) + tproject1 (tproject2 (tproject2 (tproject1 x121))) * (x132 * x133) + tproject1 (tproject1 x121) * recip x128 + (x143 * negate (recip (x128 * x128))) * tproject1 (tproject2 x121))) (\\x152 -> let x157 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x152)))))) ; x158 = x157 * x157 ; x159 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x152))))))) ; x160 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x152)))) * x159 ; x161 = x158 * x158 ; x162 = x160 * x157 + x160 * x157 ; x163 = negate (recip x161) ; x167 = tproject1 (tproject2 (tproject2 (tproject2 x152))) * tproject2 (tproject1 x152) ; x168 = negate (recip (x161 * x161)) * (-1.0 * (x162 * x167)) ; x169 = x163 * x167 ; x170 = x157 * x169 + x157 * x169 ; x171 = x158 * x168 + x158 * x168 + negate (recip (x158 * x158)) * (tproject1 (tproject2 x152) * tproject2 (tproject1 x152)) in tpair (recip x158 * tproject2 (tproject1 x152) + tproject1 (tproject1 x152), tpair (tpair ([], tpair (0.0, x159 * x170)), tpair ((x162 * x163) * tproject2 (tproject1 x152), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x152))))))) * (x157 * x171 + x157 * x171 + x160 * x169 + x160 * x169) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x152)))))) * (-1.0 * (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x152)))) * x170)))))))) (tproject1 (tproject1 x75)) (tpair (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x172 -> let x173 = cos (tproject2 (tproject2 (tproject2 x172))) in tpair (tproject1 x172 + tproject1 (tproject2 x172) * recip (x173 * x173), tpair (tproject1 x172, []))) (\\x174 -> let x178 = cos (tproject2 (tproject2 (tproject2 (tproject2 x174)))) ; x179 = x178 * x178 ; x181 = tproject2 (tproject2 (tproject2 (tproject1 x174))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x174))))) in tpair (tproject1 (tproject1 x174) + tproject1 (tproject2 (tproject1 x174)) * recip x179 + ((x181 * x178 + x181 * x178) * negate (recip (x179 * x179))) * tproject1 (tproject2 (tproject2 x174)), tpair (tproject1 (tproject1 x174), []))) (\\x186 -> let x189 = cos (tproject2 (tproject2 (tproject2 (tproject2 x186)))) ; x190 = x189 * x189 ; x193 = negate (recip (x190 * x190)) * (tproject1 (tproject2 (tproject2 x186)) * tproject1 (tproject1 x186)) in tpair (tproject1 (tproject1 x186) + tproject1 (tproject2 (tproject1 x186)), tpair (recip x190 * tproject1 (tproject1 x186), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x186))))) * (x189 * x193 + x189 * x193))))) (tproject2 (tproject2 (tproject2 (tproject1 x75)))) (tpair (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x75)))), tpair (tproject1 (tproject2 v79), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x75)))))), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x194 -> let x197 = cos (tproject2 (tproject2 (tproject2 x194))) in tpair (tproject1 x194, tpair (tproject1 x194, recip (x197 * x197) * tproject1 x194))) (\\x200 -> let x204 = let x201 = cos (tproject2 (tproject2 (tproject2 (tproject2 x200)))) ; x202 = x201 * x201 ; x203 = tproject2 (tproject2 (tproject2 (tproject1 x200))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x200))))) in tpair (tproject1 (tproject1 x200), ((x203 * x201 + x203 * x201) * negate (recip (x202 * x202))) * tproject1 (tproject2 x200) + tproject1 (tproject1 x200) * recip x202) in tpair (tproject1 x204, tpair (tproject1 (tproject1 x200), tproject2 x204))) (\\x205 -> let x213 = let x210 = cos (tproject2 (tproject2 (tproject2 (tproject2 x205)))) ; x211 = x210 * x210 ; x212 = negate (recip (x211 * x211)) * (tproject1 (tproject2 x205) * tproject2 (tproject2 (tproject1 x205))) in tpair (recip x211 * tproject2 (tproject2 (tproject1 x205)) + tproject1 (tproject1 x205), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x205))))) * (x210 * x212 + x210 * x212)))) in tpair (tproject1 x213 + tproject1 (tproject2 (tproject1 x205)), tproject2 x213)) (tproject1 (tproject2 x75)) (tpair ([], tpair (tproject1 (tproject2 (tproject2 v79)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))), tpair ([], tpair (tproject1 (tproject2 (tproject2 v79)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))) in tpair (rsum (tproject2 v89), tproject1 v89)) (\\x214 -> let v217 = dmapAccumLDer (SNat @22) (\\x232 -> tpair (tproject1 x232 + tan (tproject2 x232), tpair (tproject1 x232, tpair (tproject1 x232, [])))) (\\x238 -> let x241 = cos (tproject2 (tproject2 x238)) in tpair (tproject1 (tproject1 x238) + tproject2 (tproject1 x238) * recip (x241 * x241), tpair (tproject1 (tproject1 x238), tpair (tproject1 (tproject1 x238), [])))) (\\x246 -> let x249 = cos (tproject2 (tproject2 x246)) in tpair (tproject1 (tproject2 (tproject1 x246)) + tproject1 (tproject1 x246) + tproject1 (tproject2 (tproject2 (tproject1 x246))), recip (x249 * x249) * tproject1 (tproject1 x246))) (tproject2 (tproject2 (tproject2 (tproject2 x214)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x214))))) ; v226 = dmapAccumLDer (SNat @22) (\\x253 -> let x258 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x253))))) ; x259 = x258 * x258 ; x260 = negate (recip (x259 * x259)) * (tproject1 (tproject2 (tproject2 x253)) * tproject1 (tproject2 x253)) in tpair (recip x259 * tproject1 (tproject2 x253) + tproject1 x253, tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x253)))))) * (x258 * x260 + x258 * x260))))) (\\x261 -> let x267 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x261)))))) ; x268 = x267 * x267 ; x269 = x268 * x268 ; x270 = negate (recip x269) ; x271 = tproject1 (tproject2 (tproject2 (tproject2 x261))) * tproject1 (tproject2 (tproject2 x261)) ; x272 = x270 * x271 ; x276 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x261))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x261))))))) ; x277 = x276 * x267 + x276 * x267 ; x287 = (((x277 * x268 + x277 * x268) * negate (recip (x269 * x269))) * -1.0) * x271 + (tproject1 (tproject2 (tproject2 (tproject1 x261))) * tproject1 (tproject2 (tproject2 x261)) + tproject1 (tproject2 (tproject1 x261)) * tproject1 (tproject2 (tproject2 (tproject2 x261)))) * x270 in tpair (tproject1 (tproject1 x261) + (x277 * negate (recip (x268 * x268))) * tproject1 (tproject2 (tproject2 x261)) + tproject1 (tproject2 (tproject1 x261)) * recip x268, tpair ([], tpair (0.0, ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x261))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x261))))))) * -1.0) * (x267 * x272 + x267 * x272) + (x276 * x272 + x287 * x267 + x276 * x272 + x287 * x267) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x261))))))))))) (\\x292 -> let x297 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x292)))))) ; x298 = x297 * x297 ; x299 = x298 * x298 ; x300 = negate (recip x299) ; x301 = tproject1 (tproject2 (tproject2 (tproject2 x292))) * tproject1 (tproject2 (tproject2 x292)) ; x302 = x300 * x301 ; x307 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x292))))))) * tproject2 (tproject2 (tproject2 (tproject1 x292))) ; x308 = x297 * x307 + x297 * x307 ; x309 = x300 * x308 ; x310 = negate (recip (x299 * x299)) * (-1.0 * (x301 * x308)) ; x311 = x298 * x310 + x298 * x310 + negate (recip (x298 * x298)) * (tproject1 (tproject2 (tproject2 x292)) * tproject1 (tproject1 x292)) in tpair (tproject1 (tproject1 x292), tpair (tproject1 (tproject2 (tproject2 (tproject2 x292))) * x309 + recip x298 * tproject1 (tproject1 x292), tpair (tproject1 (tproject2 (tproject2 x292)) * x309, tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x292))))))) * (x297 * x311 + x297 * x311 + x302 * x307 + x302 * x307) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x292)))))) * (-1.0 * ((x297 * x302 + x297 * x302) * tproject2 (tproject2 (tproject2 (tproject1 x292))))))))))) (0.0 + tproject2 (tproject1 x214)) (tpair (rconst (rfromListLinear [22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + rreplicate 22 (tproject1 (tproject1 x214)), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x312 -> let x315 = cos (tproject2 (tproject2 (tproject2 x312))) in tpair (tproject1 x312, tpair (tproject1 x312, recip (x315 * x315) * tproject1 x312))) (\\x318 -> let x326 = let x323 = cos (tproject2 (tproject2 (tproject2 (tproject2 x318)))) ; x324 = x323 * x323 ; x325 = tproject2 (tproject2 (tproject2 (tproject1 x318))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x318))))) in tpair (tproject1 (tproject1 x318), ((x325 * x323 + x325 * x323) * negate (recip (x324 * x324))) * tproject1 (tproject2 x318) + tproject1 (tproject1 x318) * recip x324) in tpair (tproject1 x326, tpair (tproject1 (tproject1 x318), tproject2 x326))) (\\x327 -> let x331 = let x328 = cos (tproject2 (tproject2 (tproject2 (tproject2 x327)))) ; x329 = x328 * x328 ; x330 = negate (recip (x329 * x329)) * (tproject1 (tproject2 x327) * tproject2 (tproject2 (tproject1 x327))) in tpair (recip x329 * tproject2 (tproject2 (tproject1 x327)) + tproject1 (tproject1 x327), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x327))))) * (x328 * x330 + x328 * x330)))) in tpair (tproject1 x331 + tproject1 (tproject2 (tproject1 x327)), tproject2 x331)) (tproject1 (tproject2 x214)) (tpair ([], tpair (tproject1 (tproject2 (tproject2 v217)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x214))))))))), tpair ([], tpair (tproject1 (tproject2 (tproject2 v217)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x214))))))))) ; v230 = dmapAccumRDer (SNat @22) (\\x332 -> let x333 = cos (tproject2 (tproject2 (tproject2 x332))) in tpair (tproject1 x332 + tproject1 (tproject1 (tproject2 x332)), recip (x333 * x333) * tproject1 x332)) (\\x334 -> let x338 = cos (tproject2 (tproject2 (tproject2 (tproject2 x334)))) ; x339 = x338 * x338 ; x342 = tproject2 (tproject2 (tproject2 (tproject1 x334))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x334))))) in tpair (tproject1 (tproject1 x334) + tproject1 (tproject1 (tproject2 (tproject1 x334))), ((x342 * x338 + x342 * x338) * negate (recip (x339 * x339))) * tproject1 (tproject2 x334) + tproject1 (tproject1 x334) * recip x339)) (\\x346 -> let x349 = cos (tproject2 (tproject2 (tproject2 (tproject2 x346)))) ; x350 = x349 * x349 ; x353 = negate (recip (x350 * x350)) * (tproject1 (tproject2 x346) * tproject2 (tproject1 x346)) in tpair (tproject1 (tproject1 x346) + recip x350 * tproject2 (tproject1 x346), tpair (tpair (tproject1 (tproject1 x346), []), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x346))))) * (x349 * x353 + x349 * x353))))) 0.0 (tpair (tpair (tproject1 (tproject2 (tproject2 v226)), []), tpair (tproject1 (tproject2 v217), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x214))))))) in tpair (tproject1 v226, tpair ([], tpair (rsum (tproject2 v230) + rsum (tproject2 (tproject2 (tproject2 v226))), tproject1 v230)))) 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) (\\x354 -> tpair (tproject1 (dmapAccumLDer (SNat @22) (\\x359 -> tpair (tproject1 x359 + tan (tproject2 x359), [])) (\\x361 -> let x368 = cos (tproject2 (tproject2 x361)) in tpair (tproject1 (tproject1 x361) + tproject2 (tproject1 x361) * recip (x368 * x368), [])) (\\x369 -> let x374 = cos (tproject2 (tproject2 x369)) in tpair (tproject1 (tproject1 x369), recip (x374 * x374) * tproject1 (tproject1 x369))) (tproject2 x354) (rreplicate 22 (tproject1 x354))), tpair (tproject1 x354, []))) (\\x375 -> tpair (tproject1 (dmapAccumLDer (SNat @22) (\\x385 -> let x394 = cos (tproject2 (tproject2 (tproject2 x385))) in tpair (tproject1 x385 + tproject1 (tproject2 x385) * recip (x394 * x394), [])) (\\x395 -> let x408 = cos (tproject2 (tproject2 (tproject2 (tproject2 x395)))) ; x409 = x408 * x408 ; x410 = tproject2 (tproject2 (tproject2 (tproject1 x395))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x395))))) in tpair (tproject1 (tproject1 x395) + tproject1 (tproject2 (tproject1 x395)) * recip x409 + ((x410 * x408 + x410 * x408) * negate (recip (x409 * x409))) * tproject1 (tproject2 (tproject2 x395)), [])) (\\x411 -> let x420 = cos (tproject2 (tproject2 (tproject2 (tproject2 x411)))) ; x421 = x420 * x420 ; x422 = negate (recip (x421 * x421)) * (tproject1 (tproject2 (tproject2 x411)) * tproject1 (tproject1 x411)) in tpair (tproject1 (tproject1 x411), tpair (recip x421 * tproject1 (tproject1 x411), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x411))))) * (x420 * x422 + x420 * x422))))) (tproject2 (tproject1 x375)) (tpair (rreplicate 22 (tproject1 (tproject1 x375)), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x423 -> tpair (tproject1 x423 + tan (tproject2 x423), tpair (tproject1 x423, []))) (\\x429 -> let x435 = cos (tproject2 (tproject2 x429)) in tpair (tproject1 (tproject1 x429) + tproject2 (tproject1 x429) * recip (x435 * x435), tpair (tproject1 (tproject1 x429), []))) (\\x436 -> let x445 = cos (tproject2 (tproject2 x436)) in tpair (tproject1 (tproject1 x436) + tproject1 (tproject2 (tproject1 x436)), recip (x445 * x445) * tproject1 (tproject1 x436))) (tproject2 (tproject2 x375)) (rreplicate 22 (tproject1 (tproject2 x375))))), rreplicate 22 (tproject1 (tproject2 x375)))))), tpair (tproject1 (tproject1 x375), []))) (\\x446 -> let v447 = dmapAccumRDer (SNat @22) (\\x450 -> let x451 = cos (tproject2 (tproject2 (tproject2 x450))) in tpair (tproject1 x450, recip (x451 * x451) * tproject1 x450)) (\\x452 -> let x453 = cos (tproject2 (tproject2 (tproject2 (tproject2 x452)))) ; x454 = x453 * x453 ; x455 = tproject2 (tproject2 (tproject2 (tproject1 x452))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x452))))) in tpair (tproject1 (tproject1 x452), ((x455 * x453 + x455 * x453) * negate (recip (x454 * x454))) * tproject1 (tproject2 x452) + tproject1 (tproject1 x452) * recip x454)) (\\x456 -> let x457 = cos (tproject2 (tproject2 (tproject2 (tproject2 x456)))) ; x458 = x457 * x457 ; x459 = negate (recip (x458 * x458)) * (tproject1 (tproject2 x456) * tproject2 (tproject1 x456)) in tpair (recip x458 * tproject2 (tproject1 x456) + tproject1 (tproject1 x456), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x456))))) * (x457 * x459 + x457 * x459))))) (tproject1 (tproject1 x446)) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x460 -> tpair (tproject1 x460 + tan (tproject2 x460), tpair (tproject1 x460, []))) (\\x461 -> let x462 = cos (tproject2 (tproject2 x461)) in tpair (tproject1 (tproject1 x461) + tproject2 (tproject1 x461) * recip (x462 * x462), tpair (tproject1 (tproject1 x461), []))) (\\x463 -> let x464 = cos (tproject2 (tproject2 x463)) in tpair (tproject1 (tproject1 x463) + tproject1 (tproject2 (tproject1 x463)), recip (x464 * x464) * tproject1 (tproject1 x463))) (tproject2 (tproject2 x446)) (rreplicate 22 (tproject1 (tproject2 x446))))), rreplicate 22 (tproject1 (tproject2 x446))))) in tpair (rsum (tproject2 v447) + tproject1 (tproject2 (tproject1 x446)), tproject1 v447)) 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInline
       $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 1687

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInline
       $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 21119

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
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 288587

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
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4511499

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
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
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
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
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
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 81082

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
                     (\x2 a2 -> let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x2) V.! 0
                                    w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a2) V.! 0
                                in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h15 = dmapAccumRDer (SNat @2) (\\h19 -> let h30 = dmapAccumRDer (SNat @2) (\\h31 -> let x38 = cos (rproject (tproject2 (tproject2 (tproject2 h31))) 0) in tpair ([rproject (tproject1 h31) 0], [recip (x38 * x38) * rproject (tproject1 h31) 0])) (\\h39 -> let x51 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h39)))) 0) ; x52 = x51 * x51 ; x53 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h39)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h39)))) 0)) in tpair ([rproject (tproject1 (tproject1 h39)) 0], [((x53 * x51 + x53 * x51) * negate (recip (x52 * x52))) * rproject (tproject1 (tproject2 h39)) 0 + rproject (tproject1 (tproject1 h39)) 0 * recip x52])) (\\h54 -> let x63 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h54)))) 0) ; x64 = x63 * x63 ; x65 = negate (recip (x64 * x64)) * (rproject (tproject1 (tproject2 h54)) 0 * rproject (tproject2 (tproject1 h54)) 0) in tpair ([recip x64 * rproject (tproject2 (tproject1 h54)) 0 + rproject (tproject1 (tproject1 h54)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h54)))) 0)) * (x63 * x65 + x63 * x65)])))) [rproject (tproject1 h19) 0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h66 -> tpair ([rproject (tproject1 h66) 0 + tan (rproject (tproject2 h66) 0)], tpair (tproject1 h66, []))) (\\h73 -> let x86 = cos (rproject (tproject2 (tproject2 h73)) 0) in tpair ([rproject (tproject1 (tproject1 h73)) 0 + rproject (tproject2 (tproject1 h73)) 0 * recip (x86 * x86)], tpair (tproject1 (tproject1 h73), []))) (\\h87 -> let x93 = cos (rproject (tproject2 (tproject2 h87)) 0) in tpair ([rproject (tproject1 (tproject1 h87)) 0 + rproject (tproject1 (tproject2 (tproject1 h87))) 0], [recip (x93 * x93) * rproject (tproject1 (tproject1 h87)) 0])) [rproject (tproject2 (tproject2 (tproject2 h19))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h19))) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h19))) 0)]))) in tpair ([rsum (rproject (tproject2 h30) 0)], [rproject (tproject1 h30) 0])) (\\h94 -> let h98 = dmapAccumLDer (SNat @2) (\\h119 -> tpair ([rproject (tproject1 h119) 0 + tan (rproject (tproject2 h119) 0)], tpair (tproject1 h119, tpair (tproject1 h119, [])))) (\\h126 -> let x129 = cos (rproject (tproject2 (tproject2 h126)) 0) in tpair ([rproject (tproject1 (tproject1 h126)) 0 + rproject (tproject2 (tproject1 h126)) 0 * recip (x129 * x129)], tpair (tproject1 (tproject1 h126), tpair (tproject1 (tproject1 h126), [])))) (\\h135 -> let x138 = cos (rproject (tproject2 (tproject2 h135)) 0) in tpair ([rproject (tproject1 (tproject2 (tproject1 h135))) 0 + rproject (tproject1 (tproject1 h135)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h135)))) 0], [recip (x138 * x138) * rproject (tproject1 (tproject1 h135)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h94)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h94)))) 0)] ; h114 = dmapAccumRDer (SNat @2) (\\h144 -> let x149 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h144))))) 0) ; x150 = x149 * x149 ; x151 = rproject (tproject2 (tproject2 (tproject1 (tproject2 h144)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h144))))) 0)) in tpair ([rproject (tproject1 h144) 0], [((x151 * x149 + x151 * x149) * negate (recip (x150 * x150))) * rproject (tproject1 (tproject2 (tproject2 h144))) 0 + rproject (tproject1 h144) 0 * recip x150])) (\\h152 -> let x158 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h152)))))) 0) ; x159 = x158 * x158 ; x160 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h152)))))) 0)) ; x161 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h152))))) 0 * x160 ; x162 = x159 * x159 ; x163 = x161 * x158 + x161 * x158 ; x164 = negate (recip x162) ; x169 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 h152))))) 0 * x160 + ((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h152)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h152)))))) 0)) * -1.0) * rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h152))))) 0 ; x170 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h152)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h152)))))) 0)) ; x174 = x170 * x158 + x170 * x158 in tpair ([rproject (tproject1 (tproject1 h152)) 0], [((x169 * x158 + x170 * x161 + x169 * x158 + x170 * x161) * x164 + (((x174 * x159 + x174 * x159) * negate (recip (x162 * x162))) * -1.0) * x163) * rproject (tproject1 (tproject2 (tproject2 (tproject2 h152)))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h152)))) 0 * (x163 * x164) + rproject (tproject1 (tproject1 h152)) 0 * recip x159 + (x174 * negate (recip (x159 * x159))) * rproject (tproject1 (tproject2 h152)) 0])) (\\h183 -> let x188 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0) ; x189 = x188 * x188 ; x190 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0)) ; x191 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h183))))) 0 * x190 ; x192 = x189 * x189 ; x193 = x191 * x188 + x191 * x188 ; x194 = negate (recip x192) ; x198 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h183)))) 0 * rproject (tproject2 (tproject1 h183)) 0 ; x199 = negate (recip (x192 * x192)) * (-1.0 * (x193 * x198)) ; x200 = x194 * x198 ; x201 = x188 * x200 + x188 * x200 ; x202 = x189 * x199 + x189 * x199 + negate (recip (x189 * x189)) * (rproject (tproject1 (tproject2 h183)) 0 * rproject (tproject2 (tproject1 h183)) 0) in tpair ([recip x189 * rproject (tproject2 (tproject1 h183)) 0 + rproject (tproject1 (tproject1 h183)) 0], tpair (tpair ([], tpair ([0], [x190 * x201])), tpair ([(x193 * x194) * rproject (tproject2 (tproject1 h183)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0)) * (x188 * x202 + x188 * x202 + x191 * x200 + x191 * x200) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h183)))))) 0) * (-1.0 * (rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h183))))) 0 * x201))])))))) [rproject (tproject1 (tproject1 h94)) 0] (tpair (tpair ([], tpair ([rproject (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h203 -> let x204 = cos (rproject (tproject2 (tproject2 (tproject2 h203))) 0) in tpair ([rproject (tproject1 h203) 0 + rproject (tproject1 (tproject2 h203)) 0 * recip (x204 * x204)], tpair (tproject1 h203, []))) (\\h205 -> let x209 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h205)))) 0) ; x210 = x209 * x209 ; x212 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h205)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h205)))) 0)) in tpair ([rproject (tproject1 (tproject1 h205)) 0 + rproject (tproject1 (tproject2 (tproject1 h205))) 0 * recip x210 + ((x212 * x209 + x212 * x209) * negate (recip (x210 * x210))) * rproject (tproject1 (tproject2 (tproject2 h205))) 0], tpair ([rproject (tproject1 (tproject1 h205)) 0], []))) (\\h217 -> let x220 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h217)))) 0) ; x221 = x220 * x220 ; x224 = negate (recip (x221 * x221)) * (rproject (tproject1 (tproject2 (tproject2 h217))) 0 * rproject (tproject1 (tproject1 h217)) 0) in tpair ([rproject (tproject1 (tproject1 h217)) 0 + rproject (tproject1 (tproject2 (tproject1 h217))) 0], tpair ([recip x221 * rproject (tproject1 (tproject1 h217)) 0], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h217)))) 0)) * (x220 * x224 + x220 * x224)])))) [rproject (tproject2 (tproject2 (tproject2 (tproject1 h94)))) 0] (tpair ([rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h94)))) 0)], tpair (tproject1 (tproject2 h98), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h94)))) 0)])))))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h94)))) 0)])), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h225 -> let x228 = cos (rproject (tproject2 (tproject2 (tproject2 h225))) 0) in tpair ([rproject (tproject1 h225) 0], tpair (tproject1 h225, [recip (x228 * x228) * rproject (tproject1 h225) 0]))) (\\h232 -> let h236 = let x233 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h232)))) 0) ; x234 = x233 * x233 ; x235 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h232)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h232)))) 0)) in tpair ([rproject (tproject1 (tproject1 h232)) 0], [((x235 * x233 + x235 * x233) * negate (recip (x234 * x234))) * rproject (tproject1 (tproject2 h232)) 0 + rproject (tproject1 (tproject1 h232)) 0 * recip x234]) in tpair (tproject1 h236, tpair (tproject1 (tproject1 h232), tproject2 h236))) (\\h237 -> let h245 = let x242 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h237)))) 0) ; x243 = x242 * x242 ; x244 = negate (recip (x243 * x243)) * (rproject (tproject1 (tproject2 h237)) 0 * rproject (tproject2 (tproject2 (tproject1 h237))) 0) in tpair ([recip x243 * rproject (tproject2 (tproject2 (tproject1 h237))) 0 + rproject (tproject1 (tproject1 h237)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h237)))) 0)) * (x242 * x244 + x242 * x244)]))) in tpair ([rproject (tproject1 h245) 0 + rproject (tproject1 (tproject2 (tproject1 h237))) 0], tproject2 h245)) [rproject (tproject1 (tproject2 h94)) 0] (tpair ([], tpair ([rproject (tproject1 (tproject2 (tproject2 h98))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h94)))) 0)]))))), tpair ([], tpair ([rproject (tproject1 (tproject2 (tproject2 h98))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h94)))) 0)]))))) in tpair ([rsum (rproject (tproject2 h114) 0)], [rproject (tproject1 h114) 0])) (\\h246 -> let h249 = dmapAccumLDer (SNat @2) (\\h274 -> tpair ([rproject (tproject1 h274) 0 + tan (rproject (tproject2 h274) 0)], tpair (tproject1 h274, tpair (tproject1 h274, [])))) (\\h281 -> let x284 = cos (rproject (tproject2 (tproject2 h281)) 0) in tpair ([rproject (tproject1 (tproject1 h281)) 0 + rproject (tproject2 (tproject1 h281)) 0 * recip (x284 * x284)], tpair (tproject1 (tproject1 h281), tpair (tproject1 (tproject1 h281), [])))) (\\h290 -> let x293 = cos (rproject (tproject2 (tproject2 h290)) 0) in tpair ([rproject (tproject1 (tproject2 (tproject1 h290))) 0 + rproject (tproject1 (tproject1 h290)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h290)))) 0], [recip (x293 * x293) * rproject (tproject1 (tproject1 h290)) 0])) [rproject (tproject2 (tproject2 (tproject2 (tproject2 h246)))) 0] [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h246)))) 0)] ; h263 = dmapAccumLDer (SNat @2) (\\h299 -> let x304 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h299))))) 0) ; x305 = x304 * x304 ; x306 = negate (recip (x305 * x305)) * (rproject (tproject1 (tproject2 (tproject2 h299))) 0 * rproject (tproject1 (tproject2 h299)) 0) in tpair ([recip x305 * rproject (tproject1 (tproject2 h299)) 0 + rproject (tproject1 h299) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h299))))) 0)) * (x304 * x306 + x304 * x306)])))) (\\h307 -> let x313 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h307)))))) 0) ; x314 = x313 * x313 ; x315 = x314 * x314 ; x316 = negate (recip x315) ; x317 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h307)))) 0 * rproject (tproject1 (tproject2 (tproject2 h307))) 0 ; x318 = x316 * x317 ; x322 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h307)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h307)))))) 0)) ; x323 = x322 * x313 + x322 * x313 ; x333 = (((x323 * x314 + x323 * x314) * negate (recip (x315 * x315))) * -1.0) * x317 + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h307)))) 0 * rproject (tproject1 (tproject2 (tproject2 h307))) 0 + rproject (tproject1 (tproject2 (tproject1 h307))) 0 * rproject (tproject1 (tproject2 (tproject2 (tproject2 h307)))) 0) * x316 in tpair ([rproject (tproject1 (tproject1 h307)) 0 + (x323 * negate (recip (x314 * x314))) * rproject (tproject1 (tproject2 (tproject2 h307))) 0 + rproject (tproject1 (tproject2 (tproject1 h307))) 0 * recip x314], tpair ([], tpair ([0.0], [((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h307)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h307)))))) 0)) * -1.0) * (x313 * x318 + x313 * x318) + (x322 * x318 + x333 * x313 + x322 * x318 + x333 * x313) * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h307)))))) 0))])))) (\\h338 -> let x343 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h338)))))) 0) ; x344 = x343 * x343 ; x345 = x344 * x344 ; x346 = negate (recip x345) ; x347 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h338)))) 0 * rproject (tproject1 (tproject2 (tproject2 h338))) 0 ; x348 = x346 * x347 ; x353 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h338)))))) 0)) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h338)))) 0 ; x354 = x343 * x353 + x343 * x353 ; x355 = x346 * x354 ; x356 = negate (recip (x345 * x345)) * (-1.0 * (x347 * x354)) ; x357 = x344 * x356 + x344 * x356 + negate (recip (x344 * x344)) * (rproject (tproject1 (tproject2 (tproject2 h338))) 0 * rproject (tproject1 (tproject1 h338)) 0) in tpair ([rproject (tproject1 (tproject1 h338)) 0], tpair ([rproject (tproject1 (tproject2 (tproject2 (tproject2 h338)))) 0 * x355 + recip x344 * rproject (tproject1 (tproject1 h338)) 0], tpair ([rproject (tproject1 (tproject2 (tproject2 h338))) 0 * x355], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h338)))))) 0)) * (x343 * x357 + x343 * x357 + x348 * x353 + x348 * x353) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h338)))))) 0) * (-1.0 * ((x343 * x348 + x343 * x348) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h338)))) 0))])))))) [0.0 + rproject (tproject2 (tproject1 h246)) 0] (tpair ([rconst (rfromListLinear [2] [0.0,0.0]) + rreplicate 2 (rproject (tproject1 (tproject1 h246)) 0)], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h358 -> let x361 = cos (rproject (tproject2 (tproject2 (tproject2 h358))) 0) in tpair ([rproject (tproject1 h358) 0], tpair (tproject1 h358, [recip (x361 * x361) * rproject (tproject1 h358) 0]))) (\\h365 -> let h373 = let x370 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h365)))) 0) ; x371 = x370 * x370 ; x372 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h365)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h365)))) 0)) in tpair ([rproject (tproject1 (tproject1 h365)) 0], [((x372 * x370 + x372 * x370) * negate (recip (x371 * x371))) * rproject (tproject1 (tproject2 h365)) 0 + rproject (tproject1 (tproject1 h365)) 0 * recip x371]) in tpair (tproject1 h373, tpair (tproject1 (tproject1 h365), tproject2 h373))) (\\h374 -> let h378 = let x375 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h374)))) 0) ; x376 = x375 * x375 ; x377 = negate (recip (x376 * x376)) * (rproject (tproject1 (tproject2 h374)) 0 * rproject (tproject2 (tproject2 (tproject1 h374))) 0) in tpair ([recip x376 * rproject (tproject2 (tproject2 (tproject1 h374))) 0 + rproject (tproject1 (tproject1 h374)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h374)))) 0)) * (x375 * x377 + x375 * x377)]))) in tpair ([rproject (tproject1 h378) 0 + rproject (tproject1 (tproject2 (tproject1 h374))) 0], tproject2 h378)) [rproject (tproject1 (tproject2 h246)) 0] (tpair ([], tpair ([rproject (tproject1 (tproject2 (tproject2 h249))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h246)))) 0)]))))), tpair ([], tpair ([rproject (tproject1 (tproject2 (tproject2 h249))) 0], [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h246)))) 0)]))))) ; h270 = dmapAccumRDer (SNat @2) (\\h379 -> let x380 = cos (rproject (tproject2 (tproject2 (tproject2 h379))) 0) in tpair ([rproject (tproject1 h379) 0 + rproject (tproject1 (tproject1 (tproject2 h379))) 0], [recip (x380 * x380) * rproject (tproject1 h379) 0])) (\\h381 -> let x385 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h381)))) 0) ; x386 = x385 * x385 ; x389 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h381)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h381)))) 0)) in tpair ([rproject (tproject1 (tproject1 h381)) 0 + rproject (tproject1 (tproject1 (tproject2 (tproject1 h381)))) 0], [((x389 * x385 + x389 * x385) * negate (recip (x386 * x386))) * rproject (tproject1 (tproject2 h381)) 0 + rproject (tproject1 (tproject1 h381)) 0 * recip x386])) (\\h393 -> let x396 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h393)))) 0) ; x397 = x396 * x396 ; x400 = negate (recip (x397 * x397)) * (rproject (tproject1 (tproject2 h393)) 0 * rproject (tproject2 (tproject1 h393)) 0) in tpair ([rproject (tproject1 (tproject1 h393)) 0 + recip x397 * rproject (tproject2 (tproject1 h393)) 0], tpair (tpair ([rproject (tproject1 (tproject1 h393)) 0], []), tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h393)))) 0)) * (x396 * x400 + x396 * x400)])))) [0.0] (tpair (tpair ([rproject (tproject1 (tproject2 (tproject2 h263))) 0], []), tpair (tproject1 (tproject2 h249), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h246)))) 0)]))) in tpair ([rproject (tproject1 h263) 0], tpair ([], tpair ([rsum (rproject (tproject2 h270) 0) + rsum (rproject (tproject2 (tproject2 (tproject2 h263))) 0)], [rproject (tproject1 h270) 0])))) [1.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h401 -> let h403 = dmapAccumLDer (SNat @2) (\\h404 -> tpair ([rproject (tproject1 h404) 0 + tan (rproject (tproject2 h404) 0)], [])) (\\h406 -> let x413 = cos (rproject (tproject2 (tproject2 h406)) 0) in tpair ([rproject (tproject1 (tproject1 h406)) 0 + rproject (tproject2 (tproject1 h406)) 0 * recip (x413 * x413)], [])) (\\h414 -> let x419 = cos (rproject (tproject2 (tproject2 h414)) 0) in tpair ([rproject (tproject1 (tproject1 h414)) 0], [recip (x419 * x419) * rproject (tproject1 (tproject1 h414)) 0])) (tproject2 h401) [rreplicate 2 (rproject (tproject1 h401) 0)] in tpair (tproject1 h403, tpair (tproject1 h401, tproject2 h403))) (\\h420 -> tpair ([rproject (tproject1 (dmapAccumLDer (SNat @2) (\\h435 -> let x444 = cos (rproject (tproject2 (tproject2 (tproject2 h435))) 0) in tpair ([rproject (tproject1 h435) 0 + rproject (tproject1 (tproject2 h435)) 0 * recip (x444 * x444)], [])) (\\h445 -> let x458 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h445)))) 0) ; x459 = x458 * x458 ; x460 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h445)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h445)))) 0)) in tpair ([rproject (tproject1 (tproject1 h445)) 0 + rproject (tproject1 (tproject2 (tproject1 h445))) 0 * recip x459 + ((x460 * x458 + x460 * x458) * negate (recip (x459 * x459))) * rproject (tproject1 (tproject2 (tproject2 h445))) 0], [])) (\\h461 -> let x470 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h461)))) 0) ; x471 = x470 * x470 ; x472 = negate (recip (x471 * x471)) * (rproject (tproject1 (tproject2 (tproject2 h461))) 0 * rproject (tproject1 (tproject1 h461)) 0) in tpair ([rproject (tproject1 (tproject1 h461)) 0], tpair ([recip x471 * rproject (tproject1 (tproject1 h461)) 0], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h461)))) 0)) * (x470 * x472 + x470 * x472)])))) [rproject (tproject2 (tproject1 h420)) 0] (tpair ([rreplicate 2 (rproject (tproject1 (tproject1 h420)) 0)], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h473 -> tpair ([rproject (tproject1 h473) 0 + tan (rproject (tproject2 h473) 0)], tpair (tproject1 h473, []))) (\\h480 -> let x487 = cos (rproject (tproject2 (tproject2 h480)) 0) in tpair ([rproject (tproject1 (tproject1 h480)) 0 + rproject (tproject2 (tproject1 h480)) 0 * recip (x487 * x487)], tpair (tproject1 (tproject1 h480), []))) (\\h488 -> let x498 = cos (rproject (tproject2 (tproject2 h488)) 0) in tpair ([rproject (tproject1 (tproject1 h488)) 0 + rproject (tproject1 (tproject2 (tproject1 h488))) 0], [recip (x498 * x498) * rproject (tproject1 (tproject1 h488)) 0])) [rproject (tproject2 (tproject2 h420)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h420)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h420)) 0)]))))) 0], tpair (tproject1 (tproject1 h420), []))) (\\h499 -> let h500 = dmapAccumRDer (SNat @2) (\\h504 -> let x505 = cos (rproject (tproject2 (tproject2 (tproject2 h504))) 0) in tpair ([rproject (tproject1 h504) 0], [recip (x505 * x505) * rproject (tproject1 h504) 0])) (\\h506 -> let x507 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h506)))) 0) ; x508 = x507 * x507 ; x509 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h506)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h506)))) 0)) in tpair ([rproject (tproject1 (tproject1 h506)) 0], [((x509 * x507 + x509 * x507) * negate (recip (x508 * x508))) * rproject (tproject1 (tproject2 h506)) 0 + rproject (tproject1 (tproject1 h506)) 0 * recip x508])) (\\h510 -> let x511 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h510)))) 0) ; x512 = x511 * x511 ; x513 = negate (recip (x512 * x512)) * (rproject (tproject1 (tproject2 h510)) 0 * rproject (tproject2 (tproject1 h510)) 0) in tpair ([recip x512 * rproject (tproject2 (tproject1 h510)) 0 + rproject (tproject1 (tproject1 h510)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h510)))) 0)) * (x511 * x513 + x511 * x513)])))) [rproject (tproject1 (tproject1 h499)) 0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h514 -> tpair ([rproject (tproject1 h514) 0 + tan (rproject (tproject2 h514) 0)], tpair (tproject1 h514, []))) (\\h515 -> let x516 = cos (rproject (tproject2 (tproject2 h515)) 0) in tpair ([rproject (tproject1 (tproject1 h515)) 0 + rproject (tproject2 (tproject1 h515)) 0 * recip (x516 * x516)], tpair (tproject1 (tproject1 h515), []))) (\\h517 -> let x518 = cos (rproject (tproject2 (tproject2 h517)) 0) in tpair ([rproject (tproject1 (tproject1 h517)) 0 + rproject (tproject1 (tproject2 (tproject1 h517))) 0], [recip (x518 * x518) * rproject (tproject1 (tproject1 h517)) 0])) [rproject (tproject2 (tproject2 h499)) 0] [rreplicate 2 (rproject (tproject1 (tproject2 h499)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h499)) 0)]))) in tpair ([rsum (rproject (tproject2 h500) 0) + rproject (tproject1 (tproject2 (tproject1 h499))) 0], [rproject (tproject1 h500) 0])) [1.1] [rreplicate 2 1.1])), [rreplicate 2 1.1]))) in [rsum (rproject (tproject2 h15) 0) + rproject (tproject1 h15) 0]"

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
                         (\x4 a4 -> let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x4) V.! 0
                                        w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a4) V.! 0
                                    in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      g x = unHVectorPseudoTensor $ rrev (\v -> f (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (HVectorPseudoTensor $ dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstRanked PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 5949393

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
                           (\x5 a5 -> let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x5) V.! 0
                                          w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a5) V.! 0
                                      in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x6) V.! 0
                                            w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a6) V.! 0
                                        in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * (y + tan w))
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x6) V.! 0
                                            w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a6) V.! 0
                                        in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                                          let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x11) V.! 0
                                              w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a11) V.! 0
                                          in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                                       a10 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x10))
                                     a9 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x9))
                                   a8 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x8))
                                 a7 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x7))
                               a6 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x6))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                                          let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x11) V.! 0
                                              w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a11) V.! 0
                                          in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                                       a10 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x10))
                                     a9 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x9))
                                   a8 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x8))
                                 a7 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x7))
                               a6 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x6))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                                          let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x11) V.! 0
                                              w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a11) V.! 0
                                          in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                                       a10 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x10))
                                     a9 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x9))
                                   a8 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x8))
                                 a7 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x7))
                               a6 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x6))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      f :: forall f. ADReady f => f Double 0
        -> Rep f (TKProduct (TKS Float '[1]) (TKR Double 0))
      f x = tpair (sfromList [scast $ sfromR $ g x]) (g x + rscalar 0.2)
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
                                          let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x11) V.! 0
                                              w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a11) V.! 0
                                          in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                                       a10 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x10))
                                     a9 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x9))
                                   a8 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x8))
                                 a7 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x7))
                               a6 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x6))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
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
                                          let y = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor x11) V.! 0
                                              w = rfromD @Double @0 $ dunHVector (unHVectorPseudoTensor a11) V.! 0
                                          in tpair (HVectorPseudoTensor $ dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (HVectorPseudoTensor $ dmkHVector V.empty))
                                       a10 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x10))
                                     a9 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x9))
                                   a8 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x8))
                                 a7 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x7))
                               a6 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x6))
                             a5 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x5))
                           a4 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x4))
                         a3 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x3))
                       a2 (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x2))
                     a (HVectorPseudoTensor $ mkreplicate1HVector (SNat @2) $ dunHVector $ unHVectorPseudoTensor x))
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked z)
                   (HVectorPseudoTensor $ dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rrev1 f) (rscalar 0.0001))

productToVectorOf
  :: ADReady f
  => Rep f (TKProduct TKUntyped TKUntyped)
  -> HVectorOf f
productToVectorOf p = unHVectorPseudoTensor
                      $ tlet @_ @_ @TKUntyped (tproject1 p) $ \p1 ->
                          tlet (tproject2 p) $ \p2 ->
                            HVectorPseudoTensor $ dmkHVector $ dunHVector (unHVectorPseudoTensor p1) V.++ dunHVector (unHVectorPseudoTensor p2)

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
               f a0 = rfold (\x a -> tlet (x + a) $ \xpa ->
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
               f a0 = rfold (\x a -> tlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInline $ unAstRanked a1))
    @?= 43092

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      f x =
        unHVectorPseudoTensor $ rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (HVectorPseudoTensor $ dmkHVector x)
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (rscalar 0.4535961214255773))
    (f @ORArray (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

testSin0revhVPP :: Assertion
testSin0revhVPP = do
  resetVarCounter
  let f :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      f x =
        unHVectorPseudoTensor $ rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (HVectorPseudoTensor $ dmkHVector x)
  printAstSimple IM.empty (f @(AstRanked PrimalSpan)
                                    (V.singleton
                                     $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (cos 1.1 * 1.0)])"

testSin0revhV2 :: Assertion
testSin0revhV2 = do
  let f :: forall g. BaseTensor g
        => HVector g -> HVectorOf g
      f x =
        unHVectorPseudoTensor $ rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (HVectorPseudoTensor $ dmkHVector x)
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
        unHVectorPseudoTensor $
        srev @g @_ @Double @'[] (\v -> sin (sfromD $ dunHVector (unHVectorPseudoTensor v) V.! 0))
             (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
             (HVectorPseudoTensor $ dmkHVector x)
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
      f :: forall g. (RankedTensor g, BaseTensor g)
        => HVector g -> HVectorOf g
      f x =
        unHVectorPseudoTensor $
        rrevDt @g @_ @Double @1 (rscanZip const doms 5 . dunHVector . unHVectorPseudoTensor)
               (FTKUntyped doms3) (HVectorPseudoTensor $ dmkHVector x) (ringestData1 [1, 2, 3, 4])
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
      f :: forall g. (ShapedTensor (ShapedOf g), BaseTensor g)
        => HVector g -> HVectorOf g
      f x = unHVectorPseudoTensor $
        srevDt @g @_ @Double @'[4] (sscanZip const doms (srepl 5) . dunHVector . unHVectorPseudoTensor)
               (FTKUntyped doms3) (HVectorPseudoTensor $ dmkHVector x) (ingestData [1, 2, 3, 4])
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
      f :: forall g. (RankedTensor g, BaseTensor g)
        => HVector g -> HVectorOf g
      f x =
        unHVectorPseudoTensor $
        rrevDt @g @_ @Double @1
               (\v -> rscanZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 (dunHVector (unHVectorPseudoTensor v)))
                (FTKUntyped doms3) (HVectorPseudoTensor $ dmkHVector x) (ringestData1 [1, 2, 3, 4])
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
      f :: forall g. (ShapedTensor (ShapedOf g), BaseTensor g)
        => HVector g -> HVectorOf g
      f x =unHVectorPseudoTensor $
        srevDt @g @_ @Double @'[4]
               (\v -> sscanZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms (srepl 5) (dunHVector (unHVectorPseudoTensor v)))
               (FTKUntyped doms3) (HVectorPseudoTensor $ dmkHVector x) (ingestData [1, 2, 3, 4])
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
  let f :: forall g. BaseTensor g
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
              in tlet @_ @TKUntyped (HVectorPseudoTensor (rf cr x a)) $ \ !rfRes ->
                   fst (domsToPair (dunHVector (unHVectorPseudoTensor rfRes))))
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
                     in unHVectorPseudoTensor
                        $ tlet @_ @TKUntyped @TKUntyped
                               (HVectorPseudoTensor (rf cr x a))
                               $ \ !rfRes ->
                                   HVectorPseudoTensor $ dmkHVector $ snd $ domsToPair (dunHVector (unHVectorPseudoTensor rfRes)))
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
  let f :: forall f. ADReady f => f Double 0 -> HVectorPseudoTensor f Float '() -> f Double 0
      f _t v = sin (rfromD (dunHVector (unHVectorPseudoTensor v) V.! 1)) * rfromD (dunHVector (unHVectorPseudoTensor v) V.! 1)
      doms = V.fromList [ voidFromSh @Double ZSR
                        , voidFromSh @Double ZSR ]
      p :: ranked Double 1
      p = rscanZip (\x y -> f x (HVectorPseudoTensor $ dmkHVector y)) doms 7 as
      rf :: forall f. ADReady f
         => f Double 0 -> f Double 0 -> HVector f -> HVectorOf f
      rf _x _y = unHVectorPseudoTensor . rrev @f (f 42) (FTKUntyped doms) . HVectorPseudoTensor . dmkHVector  -- not exactly the rev of f
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
     , ADReadyS shaped, KnownNat m, Rank shm ~ m)
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
                    in tlet @_ @TKUntyped (HVectorPseudoTensor
                         (rf cr x a)) $ \ !rfRes ->
                           fst (domsToPair (dunHVector (unHVectorPseudoTensor rfRes))))
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
                         tlet @_ @TKUntyped (HVectorPseudoTensor (rf cr x a)) $ \ !rfRes ->
                           snd $ domsToPair (dunHVector (unHVectorPseudoTensor rfRes)))
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
      rf _x _y z = unHVectorPseudoTensor $
                   srev @(RankedOf f) (\v -> f (sscalar 42) (sfromD (dunHVector (unHVectorPseudoTensor v) V.! 1)))
                        (FTKUntyped doms)
                        (HVectorPseudoTensor $ dmkHVector $ V.fromList [ DynamicShaped @Double @'[] z
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
            tlet @_ @TKUntyped (HVectorPseudoTensor asD) (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1) ]))
-}
