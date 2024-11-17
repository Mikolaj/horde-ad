{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.IntMap.Strict qualified as IM
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, type (+))
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)

import Data.Array.Nested
  ( IShR
  , IxS (..)
  , KnownShS (..)
  , Rank
  , ShR (..)
  , pattern (:$:)
  , pattern (:.$)
  , pattern (:.:)
  , pattern ZIR
  , pattern ZIS
  , pattern ZSR
  )
import Data.Array.Nested qualified as Nested

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)
import HordeAd.Core.OpsAst
import HordeAd.Core.OpsConcrete ()
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), RealFloatF (..))

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
  , testCase "4S0RfwdPP4" testSin0RfwdPP4
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
  , testCase "4S0Scan1RevPP1" testSin0Scan1RevPP1
  , testCase "4S0Scan1RevPPForComparison" testSin0Scan1RevPPForComparison
  , testCase "4S0ScanFwdPP" testSin0ScanFwdPP
  , testCase "4S0ScanFwdPPFull" testSin0ScanFwdPPFull
  , testCase "4S0Scan1Rev2PP1" testSin0Scan1Rev2PP1
  , testCase "4S0Scan1Rev2PPA" testSin0Scan1Rev2PPA
  , testCase "4S0Scan1Rev2PPForComparison" testSin0Scan1Rev2PPForComparison
  , testCase "4S0Scan1Rev2" testSin0Scan1Rev2
  , testCase "4S0Scan1Rev2ForComparison" testSin0Scan1Rev2ForComparison
  , testCase "4S0Scan1Rev3PP" testSin0Scan1Rev3PP
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
  , testCase "4S0ScanD0" testSin0ScanD0
  , testCase "4S0rmapAccumRD0SC" testSin0rmapAccumRD0SC
  , testCase "4S0rmapAccumRD0S" testSin0rmapAccumRD0S
  , testCase "4S0rmapAccumRD00SC" testSin0rmapAccumRD00SC
  , testCase "4S0rmapAccumRD00S0" testSin0rmapAccumRD00S0
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD00S" testSin0rmapAccumRD00S
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD00S7" testSin0rmapAccumRD00S7
  , testCase "4S0rmapAccumRD00SCacc0" testSin0rmapAccumRD00SCacc0
  , testCase "4S0rmapAccumRD00SCacc" testSin0rmapAccumRD00SCacc
  , testCase "4S0rmapAccumRD00Sacc0" testSin0rmapAccumRD00Sacc0
  , testCase "4S0rmapAccumRD00Sacc" testSin0rmapAccumRD00Sacc
  , testCase "4S0rmapAccumRD00SCall0" testSin0rmapAccumRD00SCall0
  , testCase "4S0rmapAccumRD00SCall" testSin0rmapAccumRD00SCall
  , testCase "4S0rmapAccumRD00Sall0" testSin0rmapAccumRD00Sall0
  , testCase "4S0rmapAccumRD00Sall" testSin0rmapAccumRD00Sall
  , testCase "4S0rmapAccumRD0RC" testSin0rmapAccumRD0RC
  , testCase "4S0rmapAccumRD0R" testSin0rmapAccumRD0R
  , testCase "4S0ScanD01" testSin0ScanD01
  , testCase "4S0rmapAccumRD01SC" testSin0rmapAccumRD01SC
  , testCase "4S0rmapAccumRD01SN" testSin0rmapAccumRD01SN
  , testCase "4S0rmapAccumRD01SN2" testSin0rmapAccumRD01SN2
  , testCase "4S0rmapAccumRD01SN3" testSin0rmapAccumRD01SN3
  , testCase "4S0rmapAccumRD01SN4" testSin0rmapAccumRD01SN4
  , testCase "4S0rmapAccumRD01SN5" testSin0rmapAccumRD01SN5
  , testCase "4S0rmapAccumRD01SN51" testSin0rmapAccumRD01SN51
  , testCase "4S0rmapAccumRD01SN52" testSin0rmapAccumRD01SN52
  , testCase "4S0rmapAccumRD01SN53" testSin0rmapAccumRD01SN53
  , testCase "4S0rmapAccumRD01SN531" testSin0rmapAccumRD01SN531
  , testCase "4S0rmapAccumRD01SN531a" testSin0rmapAccumRD01SN531a
  , testCase "4S0rmapAccumRD01SN531b0" testSin0rmapAccumRD01SN531b0
  , testCase "4S0rmapAccumRD01SN531bS" testSin0rmapAccumRD01SN531bS
  , testCase "4S0rmapAccumRD01SN531bR" testSin0rmapAccumRD01SN531bR
  , testCase "4S0rmapAccumRD01SN531b0PP" testSin0rmapAccumRD01SN531b0PP
  , testCase "4S0rmapAccumRD01SN531bSPP" testSin0rmapAccumRD01SN531bSPP
  , testCase "4S0rmapAccumRD01SN531bSPPFull" testSin0rmapAccumRD01SN531bSPPFull
  , testCase "4S0rmapAccumRD01SN531bRPP" testSin0rmapAccumRD01SN531bRPP
  , testCase "4S0rmapAccumRD01SN531b0PPj" testSin0rmapAccumRD01SN531b0PPj
  , testCase "4S0rmapAccumRD01SN531bSPPj" testSin0rmapAccumRD01SN531bSPPj
  , testCase "4S0rmapAccumRD01SN531bRPPj" testSin0rmapAccumRD01SN531bRPPj
  , testCase "4S0rmapAccumRD01SN531c" testSin0rmapAccumRD01SN531c
  , testCase "4S0rmapAccumRD01SN531d" testSin0rmapAccumRD01SN531d
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD01SN531Slice" testSin0rmapAccumRD01SN531Slice
  , testCase "4S0rmapAccumRD01SN54" testSin0rmapAccumRD01SN54
-- empty tensors ambiguity:  , testCase "4S0rmapAccumRD01SN55" testSin0rmapAccumRD01SN55
  , testCase "4S0rmapAccumRD01SN55acc" testSin0rmapAccumRD01SN55acc
  , testCase "4S0rmapAccumRD01SN56" testSin0rmapAccumRD01SN56
  , testCase "4S0rmapAccumRD01SN57" testSin0rmapAccumRD01SN57
  , testCase "4S0rmapAccumRD01SN58" testSin0rmapAccumRD01SN58
  , testCase "4S0rmapAccumRD01SN59" testSin0rmapAccumRD01SN59
  , testCase "4S0rmapAccumRD01SN6" testSin0rmapAccumRD01SN6
  , testCase "4S0rmapAccumRD01SN7" testSin0rmapAccumRD01SN7
  , testCase "4S0ScanD1" testSin0ScanD1
  , testCase "4S0ScanD2" testSin0ScanD2
  , testCase "4S0ScanD3" testSin0ScanD3
  , testCase "4S0ScanD4" testSin0ScanD4
  , testCase "4S0ScanD5" testSin0ScanD5
  , testCase "4S0ScanD51" testSin0ScanD51
  , testCase "4S0ScanD51S" testSin0ScanD51S
  , testCase "4S0ScanD6" testSin0ScanD6
  , testCase "4S0ScanD7" testSin0ScanD7
  , testCase "4S0ScanD8" testSin0ScanD8
  , testCase "4S0ScanD8MapAccum" testSin0ScanD8MapAccum
  , testCase "4S0ScanD8rev" testSin0ScanD8rev
  , testCase "4S0ScanD8rev2" testSin0ScanD8rev2
  , testCase "4S0ScanD8rev3" testSin0ScanD8rev3
  , testCase "4S0ScanD8rev4" testSin0ScanD8rev4
  , testCase "4S0ScanD1RevPP" testSin0ScanD1RevPP
  , testCase "4S0ScanDFwdPP" testSin0ScanDFwdPP
  , testCase "4S0ScanD1Rev2PP" testSin0ScanD1Rev2PP
  , testCase "4S0ScanDFwd2PP" testSin0ScanDFwd2PP
  , testCase "4S0ScanD1Rev2" testSin0ScanD1Rev2
  , testCase "4S0ScanD1Rev3" testSin0ScanD1Rev3
  , testCase "4S0ScanD1Rev3PP" testSin0ScanD1Rev3PP
  , testCase "4S0ScanDFwd3PP" testSin0ScanDFwd3PP
  , testCase "4S0ScanD0fwd" testSin0ScanD0fwd
  , testCase "4S0ScanD1fwd" testSin0ScanD1fwd
  , testCase "4S0ScanD8fwd" testSin0ScanD8fwd
  , testCase "4S0ScanD8fwdMapAccum" testSin0ScanD8fwdMapAccum
  , testCase "4S0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4S0FoldNestedS1" testSin0FoldNestedS1
  , testCase "4S0FoldNestedS1PP" testSin0FoldNestedS1PP
  , testCase "4S0FoldNestedR1PP" testSin0FoldNestedR1PP
  , testCase "4S0FoldNestedR1SimpPP" testSin0FoldNestedR1SimpPP
  , testCase "4S0FoldNestedR1SimpNestedPP" testSin0FoldNestedR1SimpNestedPP
  , testCase "4S0FoldNestedR0LengthPPs" testSin0FoldNestedR0LengthPPs
  , testCase "4S0FoldNestedR1LengthPPs" testSin0FoldNestedR1LengthPPs
  , testCase "4S0FoldNestedR2LengthPPs" testSin0FoldNestedR2LengthPPs
  , testCase "4S0FoldNestedR3LengthPPs" testSin0FoldNestedR3LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR4LengthPPs" testSin0FoldNestedR4LengthPPs
-- takes too long:    , testCase "4S0FoldNestedR5LengthPPs" testSin0FoldNestedR5LengthPPs
  , testCase "4S0FoldNestedR2LengthPPsDummy7" testSin0FoldNestedR2LengthPPsDummy7
  , testCase "4S0FoldNestedR2Dummy7" testSin0FoldNestedR2Dummy7
  , testCase "4S0FoldNestedR2Tan" testSin0FoldNestedR2Tan
  , testCase "4S0MapAccumNestedR1PP" testSin0MapAccumNestedR1PP
  , testCase "4S0MapAccumNestedR3LengthPP" testSin0MapAccumNestedR3LengthPP
  , testCase "4S0MapAccumNestedR4" testSin0MapAccumNestedR4
  , testCase "4S0MapAccumNestedR5" testSin0MapAccumNestedR5
  , testCase "4S0MapAccumNestedR5r" testSin0MapAccumNestedR5r
  , testCase "4S0MapAccumNestedR10r" testSin0MapAccumNestedR10r
  , testCase "4S0MapAccumNestedR10f" testSin0MapAccumNestedR10f
  , testCase "4S0MapAccumNestedR10fN" testSin0MapAccumNestedR10fN
  , testCase "4S0MapAccumNestedR10rf" testSin0MapAccumNestedR10rf
  , testCase "4S0MapAccumNestedR10rr" testSin0MapAccumNestedR10rr
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
  , testCase "4S0revhV2" testSin0revhV2
  , testCase "4S0revhV3" testSin0revhV3
  , testCase "4S0revhV4" testSin0revhV4
  , testCase "4S0revhV5" testSin0revhV5
  , testCase "4S0revhV6" testSin0revhV6
  , testCase "4S0revhV7" testSin0revhV7
  , testCase "4S0revhV8" testSin0revhV8
  , testCase "4S0revhFoldZipR" testSin0revhFoldZipR
-- TODO:   , testCase "4S0revhFoldZip4R" testSin0revhFoldZip4R
  , testCase "4S0revhFoldS" testSin0revhFoldS
  , testCase "4S0revhFold2S" testSin0revhFold2S
  , testCase "4S0revhFold3S" testSin0revhFold3S
-- TODO: , testCase "4S0revhFold4S" testSin0revhFold4S
-- TODO: see `instance AdaptableHVector (AstRanked s) (AstTensor AstMethodLet s TKUntyped)`:  , testCase "4S0revhFold5S" testSin0revhFold5S
  ]

foo :: RealFloatF a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2F z w + z * w

fooRrev :: forall g a. (ADReady g, GoodScalar a, Differentiable a)
        => (a, a, a) -> (g (TKR a 0), g (TKR a 0), g (TKR a 0))
fooRrev (x, y, z) =
  let fHVector :: forall f. ADReady f => f TKUntyped -> f (TKR a 0)
      fHVector v = foo (rfromD $ dunHVector v V.! 0, rfromD $ dunHVector v V.! 1, rfromD $ dunHVector v V.! 2)
      sh = []
      zero = voidFromSh @a @0 sh
      shapes = V.fromList [zero, zero, zero]
      domsOf = rrev @g fHVector (FTKUntyped shapes)
                    (dmkHVector $ V.fromList
                       [ DynamicRanked $ rconcrete @g $ Nested.rscalar x
                       , DynamicRanked $ rconcrete @g $ Nested.rscalar y
                       , DynamicRanked $ rconcrete @g $ Nested.rscalar z ])
  in ( tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 0)
     , tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 1)
     , tlet @_ @TKUntyped domsOf (\v -> rfromD $ dunHVector v V.! 2) )

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
    @?= "let h44 = let x8 = sin 2.2 ; x10 = 1.1 * x8 ; x11 = recip (3.3 * 3.3 + x10 * x10) ; x17 = sin 2.2 ; x20 = 3.3 * 1.0 ; x21 = (negate 3.3 * x11) * 1.0 in [x8 * x21 + x17 * x20, cos 2.2 * (1.1 * x21) + cos 2.2 * (1.1 * x20), (x10 * x11) * 1.0 + (1.1 * x17) * 1.0] in rproject h44 0"

testFooRrevPP2 :: Assertion
testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstTensor AstMethodLet PrimalSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty (simplifyInline a1)
    @?= "tlet (sin 2.2) (\\x52 -> tlet (1.1 * x52) (\\x54 -> x52 * ((negate 3.3 * recip (3.3 * 3.3 + x54 * x54)) * 1.0) + sin 2.2 * (3.3 * 1.0)))"

testFooRrev3 :: Assertion
testFooRrev3 = do
  let f (D a _) =
        let (a1, _, _) = fooRrev @(ADVal RepN) @Double
                                 (Nested.runScalar (runFlipR $ unRepN a), 2.2, 3.3)
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
    @?= "cos 1.1 * 1.0"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstSimple IM.empty a1
    @?= "cos 1.1 * 1.0"

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
  printAstPretty IM.empty (simplifyInline a1)
    @?= "cos (cos 1.1 * 1.0) * 1.0"

testSin0Rrev5 :: Assertion
testSin0Rrev5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (rrev1 @RepN @Double @0 @0 (rrev1 sin) (rscalar 1.1))

testSin0RrevPP5 :: Assertion
testSin0RrevPP5 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 (rrev1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "negate (sin 1.1) * 1.0"

testSin0Rrev3' :: Assertion
testSin0Rrev3' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.8912073600614354) :: RepN (TKR Double 0))
    (rev' (rrev1 sin) (rscalar 1.1))

testSin0Rrev4' :: Assertion
testSin0Rrev4' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.39052780643689855 :: RepN (TKR Double 0))
    (rev' (rrev1 sin . rrev1 sin) (rscalar 1.1))

testSin0Rrev5' :: Assertion
testSin0Rrev5' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.4535961214255773) :: RepN (TKR Double 0))
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
    @?= "1.0 * cos 1.1"

testSin0RfwdPP1 :: Assertion
testSin0RfwdPP1 = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "1.0 * cos 1.1"

testSin0RfwdPP1FullUnsimp :: Assertion
testSin0RfwdPP1FullUnsimp = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (tpair (1.0, 1.1))"

testSin0RfwdPP1Full :: Assertion
testSin0RfwdPP1Full = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @0 sin (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "(\\x1 -> tproject1 x1 * cos (tproject2 x1)) (tpair (1.0, 1.1))"

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

testSin0RfwdPP4 :: Assertion
testSin0RfwdPP4 = do
  let a1 = (rfwd1 sin . rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "1.0 * cos (1.0 * cos 1.1)"

testSin0RfwdPP4Dual :: Assertion
testSin0RfwdPP4Dual = do
  let a1 = (rfwd1 sin . rfwd1 @(AstTensor AstMethodLet DualSpan) @Double @0 @0 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "(\\x18 -> tproject1 x18 * cos (tproject2 x18)) (tpair (rdualPart 1.0, (\\x14 -> tproject1 x14 * cos (tproject2 x14)) (tpair (rdualPart 1.0, rdualPart 1.1))))"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.8912073600614354))
    (rfwd1 @RepN @Double @0 @0 (rfwd1 sin) (rscalar 1.1))

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @0 (rfwd1 sin) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "(1.0 * negate (sin 1.1)) * 1.0"

testSin0Rfwd3' :: Assertion
testSin0Rfwd3' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.8912073600614354) :: RepN (TKR Double 0))
    (rev' (rfwd1 sin) (rscalar 1.1))

testSin0Rfwd4' :: Assertion
testSin0Rfwd4' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.39052780643689855 :: RepN (TKR Double 0))
    (rev' (rfwd1 sin . rfwd1 sin) (rscalar 1.1))

testSin0Rfwd5' :: Assertion
testSin0Rfwd5' = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-0.4535961214255773) :: RepN (TKR Double 0))
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
  printAstPretty IM.empty (simplifyInline a1)
    @?= "negate (sin 1.1) * (1.0 * 1.0)"

testSin0Fold0 :: Assertion
testSin0Fold0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = rfold (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0Fold0ForComparison :: Assertion
testSin0Fold0ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. f (TKR Double 0) -> f (TKR Double 0)
               f = id
           in f) (rscalar 1.1))

testSin0Fold1 :: Assertion
testSin0Fold1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR Double 0))
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @Double @1 [1] 42)) (rscalar 1.1))

testSin0FoldB1 :: Assertion
testSin0FoldB1 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: RepN (TKR Double 0))
    (rrev1 (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
                f x0 = rfold (\_x _a -> rscalar 7)
                         (rscalar 5) (rreplicate 1 x0)
            in f) (rscalar 1.1))

testSin0FoldB1PP :: Assertion
testSin0FoldB1PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan)
             (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
                  f x0 = rfold (\_x _a -> rscalar 7)
                           (rscalar 5) (rreplicate 1 x0)
              in f) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "rsum (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> 5.0 (rreplicate 1 1.1))), rreplicate 1 1.1)))))"

testSin0FoldB2 :: Assertion
testSin0FoldB2 = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 0 :: RepN (TKR Double 0))
    (rev (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
              f x0 = rfold (\_x _a -> rscalar 7)
                       (rscalar 5) (rreplicate 1 x0)
          in f) (rscalar 1.1))

testSin0FoldB3 :: Assertion
testSin0FoldB3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = rfold (\_x _a -> rscalar 7)
                        (rscalar 5) (rreplicate 1 x0)
           in f) (rscalar 1.1))

testSin0FoldB4 :: Assertion
testSin0FoldB4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = rfold (\_x _a -> rscalar 7)
                        x0 (rrepl @Double @1 [1] 42)
           in f) (rscalar 1.1))

testSin0Fold2 :: Assertion
testSin0Fold2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR Double 0))
    (rev' (\x0 -> rfold (\x _a -> sin x)
                        x0 (rrepl @Double @1 [5] 42)) (rscalar 1.1))

testSin0FoldForComparison :: Assertion
testSin0FoldForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR Double 0))
    (rev' (sin . sin . sin . sin . sin) (rscalar 1.1))

testSin0Fold3 :: Assertion
testSin0Fold3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\_x a -> sin a)
                        (rscalar 84) (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold4 :: Assertion
testSin0Fold4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar  (-0.7053476446727861) :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\x a -> atan2F (sin x) (sin a))
                        (rscalar 2 * a0) (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold5 :: Assertion
testSin0Fold5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2992412552109085 :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                          (rsum $ sin $ rsum
                                           $ rtr $ rreplicate 7 a))
                        (rscalar 2 * a0)
                        (rreplicate 3 (rreplicate 2 (rreplicate 5 a0)))) (rscalar 1.1))

testSin0Fold6 :: Assertion
testSin0Fold6 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6 :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (rscalar 1.1))

testSin0Fold7 :: Assertion
testSin0Fold7 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 250 :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (rscalar 1.1))

testSin0Fold8 :: Assertion
testSin0Fold8 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR Double 0))
    (rev' (\a0 -> rfold (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rsum $ rreplicate 7 a)))
                        (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                        (rreplicate 3 a0)) (rscalar 1.1))

testSin0Fold0S :: Assertion
testSin0Fold0S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = sfold @f @Double @Double @'[] @'[] @0
                            (\x _a -> sin x)
                            x0 (srepl 0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold1S :: Assertion
testSin0Fold1S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR Double 0))
    (rev' ((let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
                f x0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS Double '[]) -> f2 (TKS Double '[])
                                   -> f2 (TKS Double '[])
                                  g x _a = sin x
                              in g)
                        x0 (srepl @'[1] 42)
            in rfromS . f . sfromR)) (rscalar 1.1))

testSin0Fold2S :: Assertion
testSin0Fold2S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = sfold (\x _a -> sin x)
                        x0 (srepl @'[5] @Double 42)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldForComparisonS :: Assertion
testSin0FoldForComparisonS = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.12389721944941383 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f = sin . sin . sin . sin . sin
          in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold3S :: Assertion
testSin0Fold3S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\_x a -> sin a)
                        (srepl 84) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold4S :: Assertion
testSin0Fold4S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar  (-0.7053476446727861) :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\x a -> atan2F (sin x) (sin a))
                        (srepl 2 * a0) (sreplicate @f @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold5S :: Assertion
testSin0Fold5S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2992412552109085 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS Double '[]) -> f2 (TKS Double '[2, 5])
                                   -> f2 (TKS Double '[])
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
    (rscalar 6 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 1])
               f a0 = sfold @f @Double @Double @'[2, 1] @'[] @2
                        (\x a -> str
                                 $ str x + sreplicate @_ @1
                                                      (sreplicate @_ @2 a))
                        (sreplicate @_ @2 (sreplicate @_ @1 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold7S :: Assertion
testSin0Fold7S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 250 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 5])
               f a0 = sfold @f @Double @Double @'[2, 5] @'[] @2
                        (\x _a -> str $ sreplicate @_ @5 $ ssum (str x))
                        (sreplicate @_ @2 (sreplicate @_ @5 a0))
                        (sreplicate @_ @2 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0Fold8S :: Assertion
testSin0Fold8S = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-2.200311410593445) :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 5])
               f a0 = sfold @f @Double @Double @'[2, 5] @'[] @3
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
    (rscalar (-2.200311410593445) :: RepN (TKR Double 0))
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
    (rscalar (-2.200311410593445) :: RepN (TKR Double 0))
    (rrev1 (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 5])
                f a0 = sfold @f @Double @Double @'[2, 5] @'[] @3
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
                       => f (TKS Double '[]) -> f (TKS Double '[2, 5])
                     f a0 = sfold @f @Double @Double @'[2, 5] @'[] @3
                        (\x a -> str $ sreplicate @_ @5
                                 $ atan2F (ssum (str $ sin x))
                                          (sreplicate @_ @2
                                           $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @2 (sreplicate @_ @5 (sscalar 2 * a0)))
                        (sreplicate @_ @3 a0)
                 in f)
  assertEqualUpToEpsilon 1e-10
    (RepN $ FlipS $ Nested.sscalar 6.182232283434464e-2)  -- seems quite unstable
    (crev h (srepl 0.0001))

testSin0Fold182Srev :: Assertion
testSin0Fold182Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-0.4409160296923509) :: RepN (TKR Double 0))
    (rrev1 (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5])
                f a0 = sfold @f @Double @Double @'[5] @'[] @1
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
           (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5])
                f a0 = sfold @f @Double @Double @'[5] @'[] @1
                        (\_x a -> atan2F (sreplicate @_ @5 a)
                                         (sreplicate @_ @5
                                          $ sin (ssum $ sreplicate @_ @7 a)))
                        (sreplicate @_ @5 a0)
                        (sreplicate @_ @1 a0)
            in rfromS . f . sfromR) (rscalar 1.1)
  printAstPretty IM.empty a1
    @?= "let v5 = dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> (sconcrete @[5] (sfromListLinear [5] [1.0,1.0,1.0,1.0,1.0])) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> (sreplicate 1.1) (sreplicate 1.1))), sreplicate 1.1))) in rfromS (ssum (tproject1 v5)) + rfromS (sreshape (tproject2 v5))"

testSin0Fold18Srev :: Assertion
testSin0Fold18Srev = do
  assertEqualUpToEpsilon 1e-10
    (rscalar (-2.4026418024701366) :: RepN (TKR Double 0))
    (rrev1 (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 5])
                f a0 = sfold @f @Double @Double @'[2, 5] @'[] @2
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
           (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2, 5])
                f a0 = sfold @f @Double @Double @'[2, 5] @'[] @3
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
                       => f (TKS Double '[]) -> f (TKS Double '[2, 5])
                     f a0 = sfold @f @Double @Double @'[2, 5] @'[] @3
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
    (cfwd (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS Double '[]) -> f2 (TKS Double '[2, 5])
                                   -> f2 (TKS Double '[])
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
    (cfwd (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (let g :: forall f2. ADReady f2
                                   => f2 (TKS Double '[]) -> f2 (TKS Double '[2, 5])
                                   -> f2 (TKS Double '[])
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
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 1)
               f x0 = rscan (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0Scan1 :: Assertion
testSin0Scan1 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR Double 5))
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rrepl @Double @1 [1] 42))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan1ForComparison :: Assertion
testSin0Scan1ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR Double 5))
    (rev' (\x0 -> rfromList [x0, sin x0])
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan2 :: Assertion
testSin0Scan2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [2.2207726343670955] :: RepN (TKR Double 5))
    (rev' (\x0 -> rscan (\x _a -> sin x)
                        x0 (rrepl @Double @1 [5] 42))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan3 :: Assertion
testSin0Scan3 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.360788364276732] :: RepN (TKR Double 5))
    (rev' (\a0 -> rscan (\_x a -> sin a)
                        (rreplicate0N [1,1,1,1,1] (rscalar 84))
                        (rreplicate 3 a0)) (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan4 :: Assertion
testSin0Scan4 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [-0.4458209450295252] :: RepN (TKR Double 5))
    (rev' (\a0 -> rscan (\x a -> atan2F (sin x) (sin a))
                        (rreplicate0N [1,1,1,1,1] (rscalar 2) * a0)
                        (rreplicate 3 a0)) (ringestData [1,1,1,1,1] [1.1]))

testSin0Scan5 :: Assertion
testSin0Scan5 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [4.126141830000979] :: RepN (TKR Double 4))
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
    (ringestData [1,1] [12] :: RepN (TKR Double 2))
    (rev' (\a0 -> rscan (\x a -> rtr
                                 $ rtr x + rreplicate 1 (rreplicate 2 a))
                        (rreplicate 2 (rreplicate 1 a0))
                        (rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0Scan7 :: Assertion
testSin0Scan7 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1] [310] :: RepN (TKR Double 2))
    (rev' (\a0 -> rscan (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                        (rreplicate 2 (rreplicate 5 a0))
                        (rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0Scan8 :: Assertion
testSin0Scan8 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR Double 3))
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

testSin0Scan1RevPP1 :: Assertion
testSin0Scan1RevPP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInline a1)
    @?= "let v3 = rconcrete (rfromListLinear [2] [42.0,42.0]) ; v6 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) (\\x9 -> tpair (cos (tproject1 (tproject2 (tproject2 x9))) * (tproject1 (tproject2 x9) + tproject1 x9), 0.0)) (\\x15 -> tpair ((tproject1 (tproject2 (tproject2 (tproject1 x15))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x15)))))) * (tproject1 (tproject2 (tproject2 x15)) + tproject1 (tproject2 x15)) + (tproject1 (tproject2 (tproject1 x15)) + tproject1 (tproject1 x15)) * cos (tproject1 (tproject2 (tproject2 (tproject2 x15)))), 0.0)) (\\x23 -> let x28 = cos (tproject1 (tproject2 (tproject2 (tproject2 x23)))) * tproject1 (tproject1 x23) in tpair (x28, tpair (x28, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x23))))) * ((tproject1 (tproject2 (tproject2 x23)) + tproject1 (tproject2 x23)) * tproject1 (tproject1 x23)), 0.0)))) 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x29 -> let x32 = sin (tproject1 x29) in tpair (x32, tpair (tproject1 x29, x32))) (\\x34 -> let x41 = tproject1 (tproject1 x34) * cos (tproject1 (tproject2 x34)) in tpair (x41, tpair (tproject1 (tproject1 x34), x41))) (\\x43 -> tpair (cos (tproject1 (tproject2 x43)) * (tproject2 (tproject2 (tproject1 x43)) + tproject1 (tproject1 x43)) + tproject1 (tproject2 (tproject1 x43)), 0.0)) 1.1 v3)), v3))))"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v4 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) in cos 1.1 * (cos (sin 1.1) * v4 ! [0]) + cos 1.1 * v4 ! [1] + v4 ! [2]"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInline a1)
    @?= "let v4 = rconcrete (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in tpair (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in tpair (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in tpair (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, tpair (0.0, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) 1.0 (tpair (rreplicate 2 0.0, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in tpair (x35, tpair (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in tpair (x38, tpair (tproject1 (tproject1 x37), x38))) (\\x40 -> tpair (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) 1.1 v4)), v4)))))"

testSin0ScanFwdPPFull :: Assertion
testSin0ScanFwdPPFull = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rrepl @Double @1 [2] 42)) (rscalar 1.1)
  printAstPrettyButNested IM.empty (simplifyInline a1)
    @?= "(\\x1 -> let v4 = rconcrete (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 (tproject1 x1)) (tproject2 (dmapAccumLDer (SNat @2) (\\x9 -> let x16 = tproject1 x9 * cos (tproject1 (tproject2 (tproject2 x9))) in tpair (x16, x16)) (\\x17 -> let x24 = tproject1 (tproject1 x17) * cos (tproject1 (tproject2 (tproject2 (tproject2 x17)))) + (tproject1 (tproject2 (tproject2 (tproject1 x17))) * negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x17)))))) * tproject1 (tproject2 x17) in tpair (x24, x24)) (\\x25 -> let x31 = tproject2 (tproject1 x25) + tproject1 (tproject1 x25) in tpair (cos (tproject1 (tproject2 (tproject2 (tproject2 x25)))) * x31, tpair (0.0, tpair (negate (sin (tproject1 (tproject2 (tproject2 (tproject2 x25))))) * (tproject1 (tproject2 x25) * x31), 0.0)))) (tproject1 x1) (tpair (rreplicate 2 0.0, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\x32 -> let x35 = sin (tproject1 x32) in tpair (x35, tpair (tproject1 x32, x35))) (\\x37 -> let x38 = tproject1 (tproject1 x37) * cos (tproject1 (tproject2 x37)) in tpair (x38, tpair (tproject1 (tproject1 x37), x38))) (\\x40 -> tpair (cos (tproject1 (tproject2 x40)) * (tproject2 (tproject2 (tproject1 x40)) + tproject1 (tproject1 x40)) + tproject1 (tproject2 (tproject1 x40)), 0.0)) (tproject2 x1) v4)), v4)))))) (tpair (1.0, 1.1))"

testSin0Scan1Rev2PP1 :: Assertion
testSin0Scan1Rev2PP1 = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v3 = rconcrete (rfromListLinear [2] [5.0,7.0]) ; v6 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) in v6 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))))"

testSin0Scan1Rev2PPA :: Assertion
testSin0Scan1Rev2PPA = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7])))
                 (rscalar 1.1)
  printArtifactPretty IM.empty (simplifyArtifact art)
    @?= "\\v5 x1 -> let v2 = rconcrete (rfromListLinear [2] [5.0,7.0]) in v5 ! [0] + tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v5, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> x1 v2)), v2))))"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let (art, _) =
        revArtifactAdapt
                 True
                 (\x0 -> rfromList [sin (sin x0 - rscalar 5) - rscalar 7, sin x0 - rscalar 5, x0])
                 (rscalar 1.1)
  printArtifactPretty @_ @(TKR Double 1) IM.empty (simplifyArtifact art)
    @?= "\\v3 x1 -> cos x1 * (cos (sin x1 - 5.0) * v3 ! [0]) + cos x1 * v3 ! [1] + v3 ! [2]"

testSin0Scan1Rev2 :: Assertion
testSin0Scan1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [1.1961317861865948] :: RepN (TKR Double 0))
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                    (rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1))

testSin0Scan1Rev2ForComparison :: Assertion
testSin0Scan1Rev2ForComparison = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [1.1961317861865948] :: RepN (TKR Double 0))
    (rev' (\x0 -> rfromList [sin (sin x0 - rscalar 5) - rscalar 7, sin x0 - rscalar 5, x0]) (rscalar 1.1))

testSin0Scan1Rev3PP :: Assertion
testSin0Scan1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v3 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) ; v6 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) ; v7 = dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> 0.0 (tpair (rslice 1 2 v6, tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v3)), v3))) in v6 ! [0] + 5.0 * tproject2 v7 ! [0] + 7.0 * tproject2 v7 ! [1] + tproject1 v7"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * rscalar 5) - x0 * rscalar 7, sin x0 - x0 * rscalar 5, x0]) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v4 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) ; x5 = v4 ! [1] ; x6 = v4 ! [0] ; x7 = cos (sin 1.1 - 1.1 * 5.0) * x6 in cos 1.1 * x7 + 5.0 * (-1.0 * x7) + 7.0 * (-1.0 * x6) + cos 1.1 * x5 + 5.0 * (-1.0 * x5) + v4 ! [2]"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v4 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.0 (tpair (rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0]), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> 1.1 v4)), v4)))))"

testSin0Scan1Rev3 :: Assertion
testSin0Scan1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (ringestData [] [-10.076255083995068] :: RepN (TKR Double 0))
    (rev' (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1))

testSin0Scan1Rev3ForComparison :: Assertion
testSin0Scan1Rev3ForComparison = do
  assertEqualUpToEpsilon' 1e-5
    (ringestData [] [-10.076255083995068] :: RepN (TKR Double 0))
    (rev' (\x0 -> rfromList [sin (sin x0 - x0 * rscalar 5) - x0 * rscalar 7, sin x0 - x0 * rscalar 5, x0]) (rscalar 1.1))

testSin0Scan0fwd :: Assertion
testSin0Scan0fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [1] [1.0])
    (rfwd1 @RepN @Double @0 @1
    (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 1)
         f x0 = rscan (\x _a -> sin x)
                      x0 (rzero @f @Double (0 :$: ZSR))
     in f) (rscalar 1.1))

testSin0Scan1fwd :: Assertion
testSin0Scan1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
    (\x0 -> rscan (\x _a -> sin x)
                  x0 (rrepl @Double @1 [1] 42))
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
      a1 = rbuild1 @(AstTensor AstMethodLet PrimalSpan) @Double @1 k
           $ \i -> rbuild1 k
           $ \j -> ifF (i <=. j) (rscalar 0) (rscalar 1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "rgather [1000000,1000000] (rconcrete (rfromListLinear [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1])"

unitriangular1 :: (KnownNat k, GoodScalar rk, ADReady target)
               => Int -> IShR k -> target (TKR rk (2 + k))
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
  printAstPretty IM.empty (simplifyInline a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromVector (fromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))])) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6])"

unitriangular2 :: (KnownNat k, GoodScalar rk, ADReady target)
               => Int -> IShR k -> target (TKR rk (2 + k))
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
  printAstPretty IM.empty (simplifyInline a1)
    @?= "rgather [1000000,1000000,200,300,600] (rfromVector (fromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 0.0)))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 1.0))))])) (\\[i3, i4] -> [ifF (i3 <. i4) 0 1, i3, i4])"

rscanZip :: forall rn n target. (GoodScalar rn, KnownNat n, ADReady target)
         => (forall f. ADReady f => f (TKR rn n) -> HVector f -> f (TKR rn n))
         -> VoidHVector  -- shapes of the HVector above, not below
         -> target (TKR rn n)
         -> HVector target  -- one rank higher than above
         -> target (TKR rn (1 + n))
rscanZip f eShs acc0 es =
  let width = case V.unsnoc es of
        Nothing -> error "rscanZip: can't determine argument width"
        Just (_, d) -> case shapeDynamicF (shapeToList . rshape) d of
          [] -> error "rscanZip: wrong rank of argument"
          w : _shm -> w
      sh = rshape acc0
  in withSNat width $ \snat ->
    tlet @_ @TKUntyped (
      (productToVectorOf $ dmapAccumL Proxy
         snat
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped $ V.singleton $ voidFromSh @rn sh)
         (FTKUntyped eShs)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> f (TKProduct TKUntyped TKUntyped)
              g acc e =
               tlet
                (f (rfromD $ acc V.! 0) e)
                (\res -> tpair (dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ])
                             (dmkHVector
                         $ V.fromList
                             [ DynamicRanked @rn @n @f res ]))
          in \x y -> g (dunHVector x) (dunHVector y))
         (dmkHVector $ V.singleton $ DynamicRanked acc0)
         (dmkHVector es)))
      (\res -> rappend (rfromList [acc0]) (rfromD $ dunHVector res V.! 1))

sscanZip :: forall rn sh k target.
            ( GoodScalar rn, KnownShS sh, KnownNat k
            , ADReady target )
       => (forall f. ADReady f
           => f (TKS rn sh) -> HVector f -> f (TKS rn sh))
       -> VoidHVector
       -> target (TKS rn sh)
       -> HVector target
       -> target (TKS rn (1 + k ': sh))
sscanZip f eShs acc0 es =
  tlet @_ @TKUntyped (
    (productToVectorOf $ dmapAccumL Proxy
       (SNat @k)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped $ V.singleton $ voidFromShS @rn @sh)
       (FTKUntyped eShs)
       (let g :: forall f. ADReady f
              => HVector f -> HVector f -> f (TKProduct TKUntyped TKUntyped)
            g acc e =
             tlet
                (f (sfromD $ acc V.! 0) e)
                (\res -> tpair (dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ])
                             (dmkHVector
                         $ V.fromList
                             [ DynamicShaped @rn @sh @f res ]))
        in \x y -> g (dunHVector x) (dunHVector y))
       (dmkHVector $ V.singleton $ DynamicShaped acc0)
       (dmkHVector es)))
    (\res -> sappend @_ @_ @1 (sfromList [acc0]) (sfromD $ dunHVector res V.! 1))

testSin0ScanD0 :: Assertion
testSin0ScanD0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 1)
               f x0 = rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZSR])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD0SC :: Assertion
testSin0rmapAccumRD0SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                  -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD0S :: Assertion
testSin0rmapAccumRD0S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                  -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD00SC :: Assertion
testSin0rmapAccumRD00SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00S0 :: Assertion
testSin0rmapAccumRD00S0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S :: Assertion
_testSin0rmapAccumRD00S = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                  in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD00S7 :: Assertion
_testSin0rmapAccumRD00S7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 1)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[7])
              f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                                          (dmkHVector
                                      $ V.fromList
                                          [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [])
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc0 :: Assertion
testSin0rmapAccumRD00SCacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCacc :: Assertion
testSin0rmapAccumRD00SCacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc0 :: Assertion
testSin0rmapAccumRD00Sacc0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[0] (srepl 0))))
                       $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sacc :: Assertion
testSin0rmapAccumRD00Sacc = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[7]
                           $ sreplicate @_ @7 x0)))
                       $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall0 :: Assertion
testSin0rmapAccumRD00SCall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> sscalar 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00SCall :: Assertion
testSin0rmapAccumRD00SCall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall0 :: Assertion
testSin0rmapAccumRD00Sall0 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD00Sall :: Assertion
testSin0rmapAccumRD00Sall = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0)
    (rev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
              f _x0 = tlet @_ @TKUntyped (
                      (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @7)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList []))) $ \_ -> srepl 3
           in f) (srepl 1.1))

testSin0rmapAccumRD0RC :: Assertion
testSin0rmapAccumRD0RC = do
  assertEqualUpToEpsilon 1e-10
    (rscalar 1)
    (crev (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ dunHVector xh V.! 0
                             in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD0R :: Assertion
testSin0rmapAccumRD0R = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1)
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = (rfromD . (V.! 0))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                          (\xh _a ->
                             let x = rfromD @Double @0 $ dunHVector xh V.! 0
                             in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ])
                                 (dmkHVector
                                    $ V.fromList
                                        [ DynamicRanked $ sin x ]))
                          (dmkHVector $ V.singleton $ DynamicRanked x0)
                          (dmkHVector $ V.singleton $ DynamicRanked
                              $ rzero @f @Double (0 :$: ZSR))
           in f) (rscalar 1.1))

testSin0ScanD01 :: Assertion
testSin0ScanD01 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f x0 = flip rindex0 [1]
                      $ rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZSR])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (1 :$: ZSR))
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SC :: Assertion
testSin0rmapAccumRD01SC = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = flip (sindex0 @_ @_ @'[1]) [0] $ (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [DynamicShaped x0, DynamicShaped x0])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in f) (srepl 1.1))

testSin0rmapAccumRD01SN :: Assertion
testSin0rmapAccumRD01SN = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 1
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x
                                        , DynamicShaped $ sin x ])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[] (srepl 3)
                                      , DynamicShaped x0 ])
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN2 :: Assertion
testSin0rmapAccumRD01SN2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[1])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                        (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN3 :: Assertion
testSin0rmapAccumRD01SN3 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[1, 3])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[2]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.singleton $ DynamicShaped @Double @'[1, 2] (srepl 0))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN4 :: Assertion
testSin0rmapAccumRD01SN4 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[1, 3])
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                                           (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3)
                                        , DynamicShaped
                                          $ sreplicate @_ @3 (sin x / srepl 3) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN5 :: Assertion
testSin0rmapAccumRD01SN5 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[1, 3])
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0)
                                         , DynamicShaped @Double @'[1, 2] (srepl 0) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN51 :: Assertion
testSin0rmapAccumRD01SN51 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-69.90586521651421))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f x0 = (\res -> ssum @_ @_ @6 (sfromD (res V.! 0))
                               + ssum0 @_ @_ @'[6, 5, 4, 3]
                                   (sfromD (res V.! 2)))
                      $ dunHVector
                      $ dbuild1 @f (SNat @6) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[4, 3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                    x1 = sfromD @Double @'[3] $ xh V.! 1
                                in tpair (dmkHVector
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
                                            (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sbuild1 @_ @_ @4 $ \i ->
                                             sfromD (a V.! 1)
                                             - sin x1 / sreplicate @_ @3
                                                          (srepl 1 + sfromIndex0 i) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped $ x0 / (srepl 1 + sfromIntegral (sfromPrimal j))
                                      , DynamicShaped $ sreplicate @_ @3 x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 3]
                                           $ sreplicate0N @_ @_ @'[5, 3]
                                               (sfromIntegral (sfromPrimal j))
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ]))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN52 :: Assertion
testSin0rmapAccumRD01SN52 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.2207726343670955)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5, 3])
               f x0 = (sfromD . (V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           - smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                            (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 1)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 3)
                                         , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN53 :: Assertion
testSin0rmapAccumRD01SN53 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6.529656272211302)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5, 3])
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 2) ])
                                            (dmkHVector
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
                          in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531 :: Assertion
testSin0rmapAccumRD01SN531 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3]
       [-0.4284609293514655,0.2047077016162759,0.9242422110631052])
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[3]) -> f (TKS Double '[2, 3])
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ ingestData [0.1, 0.2, 0.3]
                                           - sin x - sfromD (a V.! 1) ])
                                            (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (ingestData
                                           [0.4, -0.01, -0.3, 0.2, 0.5, 1.3]) ])
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531a :: Assertion
testSin0rmapAccumRD01SN531a = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3]
       [1.8478609886246988,-22.194216099801963,-40.72162125038692])
    (rev' (let f :: forall f. ADReady f
                 => f (TKS Double '[3]) -> f (TKS Double '[2, 2, 2, 3])
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 2))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[6] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    x2 = sfromD @Double @'[6] $ xh V.! 1
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sfromList
                                             [srepl 0.01, ssum @_ @_ @6 x2, srepl 0.3]
                                           - sin x - sfromD (a V.! 1)
                                       , DynamicShaped
                                         $ srepl 1 - x2
                                           - sreplicate @_ @6
                                                 (ssum (sin x - sfromD (a V.! 1))) ])
                                            (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sreplicate @_ @3 (sfromIntegral (sfromPrimal j)))
                                      , DynamicShaped
                                        $ sreplicate @_ @6 (sfromIntegral (sfromPrimal i))
                                          - sflatten (sappend x0 x0) ] )
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (sfromList [srepl (-0.1), sreshape @_ @_ @'[] @'[1] $ sfromIntegral (sfromPrimal j)])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sscalar 0.4, sscalar (-0.01), sscalar (-0.3), sfromIntegral (sfromPrimal i), sscalar 0.5, sscalar 1.3]) ])))
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN531b0 :: Assertion
testSin0rmapAccumRD01SN531b0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKR Double 0) -> f (TKR Double 2)
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromR x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SN531bS :: Assertion
testSin0rmapAccumRD01SN531bS = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS Double '[]) -> f(TKS  Double '[2, 2])
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531bR :: Assertion
testSin0rmapAccumRD01SN531bR = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKR Double 0) -> f (TKR Double 2)
               f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicRanked x0 ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [1] [0] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
           in f) (rscalar 1.1))

testSin0rmapAccumRD01SN531b0PP :: Assertion
testSin0rmapAccumRD01SN531b0PP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR Double 2)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[]
                                        $ sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (sproject (tproject1 (dmapAccumLDer (SNat @0) (\\h21 -> tpair ([sproject (tproject1 h21) 0], [0])) (\\h25 -> tpair ([sproject (tproject1 (tproject1 h25)) 0], [0.0])) (\\h28 -> tpair ([sproject (tproject1 (tproject1 h28)) 0], tpair ([], tpair ([0], [0])))) [4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) (\\h31 -> tpair ([sproject (tproject1 h31) 0], tpair (tproject1 h31, []))) (\\h35 -> tpair ([sproject (tproject1 (tproject1 h35)) 0], tpair (tproject1 (tproject1 h35), []))) (\\h41 -> tpair ([sproject (tproject1 (tproject1 h41)) 0 + sproject (tproject1 (tproject2 (tproject1 h41))) 0], [0])) [1.1] [rconcrete (rfromListLinear [0] [])])), [rconcrete (rfromListLinear [0] [])]))))) 0)]"

testSin0rmapAccumRD01SN531bSPP :: Assertion
testSin0rmapAccumRD01SN531bSPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS Double '[2, 2])
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          x0
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [4.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [1.1] [sconcrete @[1] (sfromListLinear [1] [0.0])])), [sconcrete @[1] (sfromListLinear [1] [0.0])]))))) 0]"

testSin0rmapAccumRD01SN531bSPPFull :: Assertion
testSin0rmapAccumRD01SN531bSPPFull = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS Double '[2, 2])
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          x0
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet FullSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "(\\m1 -> [sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [ssum (ssum (tproject1 m1))] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sproject (tproject2 m1) 0] [sconcrete @[1] (sfromListLinear [1] [0.0])])), [sconcrete @[1] (sfromListLinear [1] [0.0])]))))) 0]) (tpair (sconcrete @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0]), [1.1]))"

testSin0rmapAccumRD01SN531bRPP :: Assertion
testSin0rmapAccumRD01SN531bRPP = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR Double 2)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          x0
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [1] [0] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstSimple
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (rproject (tproject1 (dmapAccumLDer (SNat @1) (\\h21 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h21) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (\\h25 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h25)) 0)]), dmkHVector (fromList [DynamicRanked 0.0]))) (\\h28 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h28)) 0)]), tpair (dmkHVector (fromList []), tpair (dmkHVector (fromList [DynamicRankedDummy]), dmkHVector (fromList [DynamicRankedDummy]))))) (dmkHVector (fromList [DynamicRanked 4.0])) (tpair (dmkHVector (fromList []), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) (\\h31 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 h31) 0)]), tpair (tproject1 h31, dmkHVector (fromList [])))) (\\h35 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h35)) 0)]), tpair (tproject1 (tproject1 h35), dmkHVector (fromList [])))) (\\h41 -> tpair (dmkHVector (fromList [DynamicRanked (rproject (tproject1 (tproject1 h41)) 0 + rproject (tproject1 (tproject2 (tproject1 h41))) 0)]), dmkHVector (fromList [DynamicRankedDummy]))) (dmkHVector (fromList [DynamicRanked 1.1])) (dmkHVector (fromList [DynamicRanked (rconcrete (rfromListLinear [1] [0.0]))])))), dmkHVector (fromList [DynamicRanked (rconcrete (rfromListLinear [1] [0.0]))])))))) 0)])"

testSin0rmapAccumRD01SN531b0PPj :: Assertion
testSin0rmapAccumRD01SN531b0PPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR Double 2)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @0)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sfromPrimal (i + j))
                                 + sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [0] [] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rfromS (ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @0) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconcrete @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i41, i42] -> [i41, i42])) (\\[i43] -> [i43])) (\\[i44] -> [i44])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @0) <lambda> <lambda> <lambda> [sconcrete @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sconcrete @[2,2] (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconcrete (rfromListLinear [0] []))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconcrete (rfromListLinear [0] []))))]))))) 0)))]"

testSin0rmapAccumRD01SN531bSPPj :: Assertion
testSin0rmapAccumRD01SN531bSPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKS Double '[2, 2])
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)
                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicShaped @Double @'[]
                               $ sfromIntegral (sfromPrimal (i + j))
                                 + sfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1] (srepl 0) ])))))
                        $ \ !d -> sfromD $ dunHVector d V.! 0
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g = srev f (FTKUntyped $ V.singleton (voidFromShS @Double @'[])) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "[ssum (ssum (sproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [sscatter (sscatter (sscatter (sconcrete @[2,2] (sfromListLinear [2,2] [1.0,1.0,1.0,1.0])) (\\[i42, i43] -> [i42, i43])) (\\[i44] -> [i44])) (\\[i45] -> [i45])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [sconcrete @[2,2] (sfromListLinear [2,2] [0.0,0.0,0.0,0.0]) + sreplicate (sreplicate 1.1) + sfromIntegral (sconcrete @[2,2] (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))] [stranspose (sreplicate (sreplicate (sconcrete @[1] (sfromListLinear [1] [0.0]))))])), [stranspose (sreplicate (sreplicate (sconcrete @[1] (sfromListLinear [1] [0.0]))))]))))) 0))]"

testSin0rmapAccumRD01SN531bRPPj :: Assertion
testSin0rmapAccumRD01SN531bRPPj = do
  resetVarCounter
  let f :: forall f. ADReady f
        => f TKUntyped -> f (TKR Double 2)
      f x0 = tlet @_ @TKUntyped (
                       (dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromSh @Double ZSR ])
                          (let h :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               h xh _a = tpair (dmkHVector xh)
                                            (dmkHVector V.empty)

                           in \x y -> h (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList
                             [ DynamicRanked @Double @0
                               $ rfromIntegral (rfromS $ sfromPrimal (i + j))
                                 + rfromD (dunHVector x0 V.! 0) ])
                          (dmkHVector $ V.fromList [ DynamicRanked @Double @1
                                        $ rconcrete $ Nested.rfromListPrimLinear [1] [0] ])))))
                        $ \ !d -> rfromD $ dunHVector d V.! 0
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g = rrev f (FTKUntyped (V.singleton (voidFromSh @Double ZSR))) . dmkHVector
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "[rsum (rsum (rproject (tproject1 (dmapAccumLDer (SNat @1) <lambda> <lambda> <lambda> [rconcrete (rfromListLinear [2,2] [1.0,1.0,1.0,1.0])] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @1) <lambda> <lambda> <lambda> [rfromIntegral (rfromS (sconcrete @[2,2] (sfromListLinear [2,2] [0,0,0,0]) + sreplicate siota + stranspose (sreplicate siota))) + rreplicate 2 (rreplicate 2 1.1)] [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconcrete (rfromListLinear [1] [0.0]))))])), [rtranspose [2,0,1] (rreplicate 2 (rreplicate 2 (rconcrete (rfromListLinear [1] [0.0]))))]))))) 0))]"

testSin0rmapAccumRD01SN531c :: Assertion
testSin0rmapAccumRD01SN531c = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar (-1.8866871148429984))
    (rev' (let f :: forall f. ADReady f
                 => f (TKS Double '[]) -> f (TKS Double '[2, 2, 2])
               f x0 = (\res -> srepl 2 - sreplicate @_ @2 (sfromD (res V.! 0))
                               - sfromD (res V.! 1))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @2) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                         (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (srepl 1 + sfromIntegral (sfromPrimal j)) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIntegral (sfromPrimal i)]) ])))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN531d :: Assertion
testSin0rmapAccumRD01SN531d = do
  assertEqualUpToEpsilon 1e-10
    V.empty
    ((let f :: forall f. ADReady f
            => f (TKS Double '[]) -> HVector f
          f x0 = dunHVector
                      $ dbuild1 @f (SNat @2) $ \i ->
                       (dbuild1 @f (SNat @0) $ \j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ srepl 1 - sin x / srepl 3 - sfromD (a V.! 0) ])
                            in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped
                                        $ x0 / (1 + sfromIntegral (sfromPrimal j)) ])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2]
                                         (sfromList0N
                                           [sscalar 0.4, sfromIntegral (sfromPrimal i)]) ])))
      in f . sfromR) (rscalar 1.1 :: RepN (TKR Double 0)))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN531Slice :: Assertion
_testSin0rmapAccumRD01SN531Slice = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 4)
    (rev' (let f :: forall f. ADReady f
                 => f (TKS Double '[]) -> f (TKS Double '[2, 2])
               f x0 = (sfromD . (V.! 0))
                      $ dunHVector
                      $ dbuild1 @f (SNat @2) $ \_i ->
                       (dbuild1 @f (SNat @2) $ \_j ->
                       (productToVectorOf $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in tpair (dmkHVector
                                   $ V.fromList [ DynamicShaped x ])
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [ DynamicShaped x0 ])
                          (dmkHVector $ V.fromList [])))
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN54 :: Assertion
testSin0rmapAccumRD01SN54 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 1.538239371140263)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5, 3])
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0)))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[4] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                 let x = sfromD @Double @'[3] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped
                                          $ sin x - sfromD (a V.! 2) ])
                                           (dmkHVector V.empty)
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[5, 1] (sreplicate0N $ sscalar 1)
                                      , DynamicShaped @Double @'[5, 2] (sreplicate0N $ sscalar 2)
                                      , DynamicShaped @Double @'[5, 3] (sreplicate0N $ sscalar 3)
                                      , DynamicShaped @Double @'[5, 4] (sreplicate0N $ sscalar 4) ])
           in rfromS . f . sfromR) (rscalar 1.1))

-- TODO: empty tensor/heterogeneous vector of tensors ambiguity breaks things
_testSin0rmapAccumRD01SN55 :: Assertion
_testSin0rmapAccumRD01SN55 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 6.529656272211302)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5, 3])
               f x0 = (\res -> sreplicate @_ @5 (sfromD (res V.! 0))
                               * sfromD (res V.! 1)
                               + sfromD (res V.! 2))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[3]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                let x = sfromD @Double @'[3] $ xh V.! 0
                                    a = xh
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x - sfromD (a V.! 0) ])
                                          (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped (sreplicate @_ @3 x0))
                          (dmkHVector $ V.fromList [])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN55acc :: Assertion
testSin0rmapAccumRD01SN55acc = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [3] [-21.0,-42.0,-21.0])
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[3]) -> f (TKS Double '[2, 3])
               f x0 = (\res -> srepl 2 - str (sreplicate @_ @3
                                         $ ssum @_ @_ @7
                                         $ str (sfromD (res V.! 1)))
                               - sfromD (res V.! 2))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[7]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[1]
                                      , voidFromShS @Double @'[3] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g _xh a =
                                let x = sreplicate @g @3 (sscalar 2)
                                in tpair (dmkHVector
                                   $ V.fromList
                                       [])
                                         (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.fromList [])
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[2, 1]
                                          (ingestData [-0.1, 0.23])
                                      , DynamicShaped @Double @'[2, 3]
                                         (sfromList0N
                                           [sindex0 x0 [1], sscalar (-0.01), sscalar (-0.3), ssum x0, sscalar 0.5, sscalar 1.3]) ])
           in rfromS . f . sfromR) (ringestData [3] [1.1, 2, 3.14]))

testSin0rmapAccumRD01SN56 :: Assertion
testSin0rmapAccumRD01SN56 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 0.4535961214255773)
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                            (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0rmapAccumRD01SN57 :: Assertion
testSin0rmapAccumRD01SN57 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[2] knownShS [0.4989557335681351,1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[2])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @2)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped $ sin x])
                                           (dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[2] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN58 :: Assertion
testSin0rmapAccumRD01SN58 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[5] knownShS [0,0,0,0,1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[5])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @5)
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1)])
                                           (dmkHVector
                                      [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[5] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN59 :: Assertion
testSin0rmapAccumRD01SN59 = do
  assertEqualUpToEpsilon 1e-10
    (sconcrete $ Nested.sfromListPrimLinear @_ @'[1] knownShS [1.1])
    (cfwd (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[1])
               f x0 = (sfromD . (V.! 1))
                      $ dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh _a =
                                 let x = sfromD @Double @'[] $ xh V.! 0
                                 in tpair (dmkHVector
                                    $ V.fromList
                                        [ DynamicShaped @Double @'[] (sscalar 1) ])
                                       (dmkHVector
                                        [ DynamicShaped x ])
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [DynamicShaped @Double @'[1] (srepl 0)])
           in f) (srepl 1.1) (srepl 1.1))

testSin0rmapAccumRD01SN6 :: Assertion
testSin0rmapAccumRD01SN6 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReady f => f (TKS Double '[]) -> HVector f
               f x0 = dunHVector $ productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           `atan2F` smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in dmkHVector . f) (sscalar 1.1))

testSin0rmapAccumRD01SN7 :: Assertion
testSin0rmapAccumRD01SN7 = do
  assertEqualUpToEpsilon 1e-10
    (srepl 0.4535961214255773)
    (crev @_ @TKUntyped
          (let f :: forall f. ADReady f
                 => f (TKS Double '[]) -> f TKUntyped
               f x0 = productToVectorOf
                      $ dmapAccumR (Proxy @f) (SNat @1)
                          (FTKUntyped $ V.fromList [voidFromShS @Double @'[]])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          (FTKUntyped $ V.fromList [ voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2]
                                      , voidFromShS @Double @'[2] ])
                          (let g :: forall g. ADReady g
                                 => HVector g -> HVector g
                                 -> g (TKProduct TKUntyped TKUntyped)
                               g xh a =
                                let x = sfromD @Double @'[] $ xh V.! 0
                                in
                                  tpair (dmkHVector
                                   $ V.fromList
                                       [ DynamicShaped
                                         $ sin x
                                           ** smaxIndex
                                               @_ @Double @Double @'[] @2
                                               (sfromD (a V.! 1)) ])
                                         (dmkHVector
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
                           in \x y -> g (dunHVector x) (dunHVector y))
                          (dmkHVector $ V.singleton $ DynamicShaped x0)
                          (dmkHVector $ V.fromList [ DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0)
                                         , DynamicShaped @Double @'[1, 2] (sreplicate0N $ sscalar 0) ])
           in f @(ADVal RepN)) (sscalar 1.1))

testSin0ScanD1 :: Assertion
testSin0ScanD1 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.4535961214255773] :: RepN (TKR Double 5))
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             (rrepl @Double @1 [1] 42)))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [2.2207726343670955] :: RepN (TKR Double 5))
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             (rrepl @Double @1 [5] 42)))
          (ringestData [1,1,1,1,1] [1.1]))

testSin0ScanD3 :: Assertion
testSin0ScanD3 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [1.360788364276732] :: RepN (TKR Double 5))
    (rev' (\a0 -> rscanZip (\_x a ->
                            sin $ rfromD @Double @5
                                    (a V.! 0))
                         (V.fromList [ voidFromSh @Double (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)
                                     , voidFromSh @Double (4 :$: 5 :$: 6 :$: 7 :$: 8 :$: ZSR) ])
                         (rreplicate0N [1,1,1,1,1] (rscalar 84))
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 a0
                            , DynamicRanked
                              (rrepl @Double @6
                                          [3, 4, 5, 6, 7, 8] 32) ]))
                         (ringestData [1,1,1,1,1] [1.1]))

testSin0ScanD4 :: Assertion
testSin0ScanD4 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1,1] [-0.4458209450295252] :: RepN (TKR Double 5))
    (rev' (\a0 -> rscanZip (\x a -> atan2F (sin x)
                                        (sin $ rfromD (a V.! 0)))
                         (V.fromList [voidFromSh @Double
                                        (1 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                         (rreplicate0N [1,1,1,1,1] (rscalar 2) * a0)
                         (V.singleton $ DynamicRanked
                          $ rreplicate 3 a0)) (ringestData [1,1,1,1,1] [1.1]))

testSin0ScanD5 :: Assertion
testSin0ScanD5 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [4.126141830000979] :: RepN (TKR Double 4))
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2F (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rfromD (a V.! 0)))
                         (V.fromList [ voidFromSh @Double
                                         (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR)
                                     , voidFromSh @Double
                                         (8 :$: 3 :$: 1 :$: 1 :$: 1 :$: 1 :$: ZSR) ])
                         (rreplicate0N [1,1,1,1] (rscalar 2) * a0)
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 (rreplicate 2 (rreplicate 5 a0))
                            , DynamicRanked
                              $ rreplicate 3 (rreplicate 8 (rreplicate 3 a0)) ]
                         ))
          (ringestData [1,1,1,1] [1.1]))

testSin0ScanD51 :: Assertion
testSin0ScanD51 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [319.68688158967257] :: RepN (TKR Double 4))
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
                         (rreplicate0N [1,1,1,1] (rscalar 2) * a0)
                         (V.fromList
                            [ DynamicRanked
                              $ rreplicate 3 (rreplicate 2 (rreplicate 5 a0))
                            , DynamicRanked
                              $ rreplicate 3 (rreplicate 8 (rreplicate 3 a0)) ]
                         ))
          (ringestData [1,1,1,1] [1.1]))

testSin0ScanD51S :: Assertion
testSin0ScanD51S = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1,1] [319.68688158967257] :: RepN (TKR Double 4))
    (rev' (let f :: forall f. ADReady f
                 => f (TKS Double '[1,1,1,1]) -> f (TKS Double '[4,1,1,1,1])
               f a0 =
                 sscanZip
                   (let g :: forall f2. ADReady f2
                          => f2 (TKS Double '[1,1,1,1]) -> HVector f2
                          -> f2 (TKS Double '[1,1,1,1])
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
           in rfromS . f . sfromR) (ringestData [1,1,1,1] [1.1]))

testSin0ScanD6 :: Assertion
testSin0ScanD6 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1] [12] :: RepN (TKR Double 2))
    (rev' (\a0 -> rscanZip (\x a -> rtr
                                 $ rtr x + rreplicate 1
                                             (rreplicate 2
                                                (rfromD (a V.! 0))))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZSR)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1] [310] :: RepN (TKR Double 2))
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5 $ rsum (rtr x))
                         (V.fromList [voidFromSh @Double (1 :$: 1 :$: ZSR)])
                         (rreplicate 2 (rreplicate 5 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (ringestData [1,1] [1.1]))

testSin0ScanD8 :: Assertion
testSin0ScanD8 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR Double 3))
    (rev' (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
                       (ringestData [1,1,1] [1.1]))

testSin0ScanD8MapAccum :: Assertion
testSin0ScanD8MapAccum = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [1,1,1] [9.532987357352765] :: RepN (TKR Double 3))
    (rev'
       (\a0 -> (rfromD @_ @6 . (V.! 1))
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList
                      [voidFromSh @Double (2 :$: 5 :$: 1 :$: 1 :$: 1 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (1 :$: 1 :$: 1 :$: ZSR)])
                   (let g :: forall g. ADReady g
                          => g TKUntyped -> g TKUntyped -> g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @5 $ dunHVector xh V.! 0
                         in tpair (dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector a))))
                                   (dmkHVector $ V.singleton $ DynamicRanked x)
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5
                                      (rreplicate0N [1,1,1] (rscalar 2) * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0))
       (ringestData [1,1,1] [1.1]))

testSin0ScanD8rev :: Assertion
testSin0ScanD8rev = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [9.53298735735276])
    (rrev1 @RepN @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8rev2 :: Assertion
testSin0ScanD8rev2 = do
  let h = rrev1 @(ADVal RepN) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [285.9579482947575])
    (crev h (rscalar 1.1))

testSin0ScanD8rev3 :: Assertion
testSin0ScanD8rev3 = do
  let h :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      h = rrev1 @f @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [285.95794829475744])
    (rev' h (rscalar 1.1))

testSin0ScanD8rev4 :: Assertion
testSin0ScanD8rev4 = do
  let h :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (V.fromList [ DynamicRanked $ rreplicate 3 a0
                                   , DynamicShaped
                                     $ sreplicate @_ @3
                                         (sfromR @_ @_ @'[] a0) ]))
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [285.95794829475744])
    (rev' h (rscalar 1.1))

testSin0ScanD1RevPP :: Assertion
testSin0ScanD1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v20 = rconcrete (rfromListLinear [2] [42.0,42.0]) ; v15 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (tpair ([rslice 1 2 v15], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v20])), [v20]))))) 0 + v15 ! [0]"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZSR])
                           x0 (V.singleton $ DynamicRanked
                               (rrepl @Double @1 [2] 42))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v19 = rconcrete (rfromListLinear [2] [42.0,42.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rreplicate 2 0.0], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v19])), [v19]))))) 0)"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev2 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                             $ rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v20 = rconcrete (rfromListLinear [2] [5.0,7.0]) ; v15 = rconcrete (rfromListLinear [3] [1.0,1.0,1.0]) in rproject (tproject1 (dmapAccumRDer (SNat @2) <lambda> <lambda> <lambda> [0.0] (tpair ([rslice 1 2 v15], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v20])), [v20]))))) 0 + v15 ! [0]"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZSR])
                         x0 (V.singleton $ DynamicRanked
                         $ rconcrete (Nested.rfromListPrimLinear @Double @1 [2] [5, 7]))) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v19 = rconcrete (rfromListLinear [2] [5.0,7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rreplicate 2 0.0], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v19])), [v19]))))) 0)"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (ringestData [] [2.417297824578748] :: RepN (TKR Double 0))
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconcrete (Nested.sfromListPrimLinear @Double @'[2, 2] knownShS [5, 7, 3, 4])
                      !$ (k :.$ ZIS) ))
          (rscalar 1.1))

testSin0ScanD1Rev3 :: Assertion
testSin0ScanD1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (ringestData [] [47.150000000000006] :: RepN (TKR Double 0))
    (rev' (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZSR])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * rscalar 5, x0]))) (rscalar 1.1))

testSin0ScanD1Rev3PP :: Assertion
testSin0ScanD1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [voidFromSh @Double ZSR])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * rscalar 5, x0]))) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInline a1))
    @?= 3715

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstTensor AstMethodLet PrimalSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZSR])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * rscalar 5, x0 * rscalar 7])) (rscalar 1.1)
  printAstPretty IM.empty (simplifyInline a1)
    @?= "let v22 = rfromVector (fromList [1.1 * 5.0, 1.1 * 7.0]) in rappend (rreplicate 1 1.0) (rproject (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.0] (tpair ([rfromVector (fromList [1.0 * 5.0, 1.0 * 7.0])], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) <lambda> <lambda> <lambda> [1.1] [v22])), [v22]))))) 0)"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [1] [1.0])
    (rfwd1 @RepN @Double @0 @1
    (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 1)
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [voidFromSh @Double ZSR])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$: ZSR))
     in f) (rscalar 1.1))

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [2] [1.0,0.4535961214255773])
    (rfwd1 @RepN @Double @0 @1
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
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @RepN @Double @0 @3
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) a)))
                      (V.fromList [voidFromSh @Double ZSR])
                      (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) (rscalar 1.1))

testSin0ScanD8fwdMapAccum :: Assertion
testSin0ScanD8fwdMapAccum = do
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [4,2,5] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.5864059429583657,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.24026418024701368,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445,-0.2200311410593445])
    (rfwd1 @RepN @Double @0 @3 @Double
       (\a0 -> rreverse $ (rfromD . (V.! 1))
               $ dunHVector $ productToVectorOf
               $ dmapAccumR Proxy (SNat @4)
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double (2 :$: 5 :$: ZSR)])
                   (FTKUntyped $ V.fromList [voidFromSh @Double ZSR])
                   (let g :: forall g. ADReady g
                          => g TKUntyped -> g TKUntyped -> g (TKProduct TKUntyped TKUntyped)
                        g xh a =
                         let x = rfromD @Double @2 $ dunHVector xh V.! 0
                         in tpair (dmkHVector $ V.singleton $ DynamicRanked
                               $ rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked
                                                     (rsum . rreplicate 7) (dunHVector a))))
                                   (dmkHVector $ V.singleton $ DynamicRanked x)
                    in g)
                      (dmkHVector $ V.singleton $ DynamicRanked
                       $ rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                      (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 4 a0)) (rscalar 1.1))

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal RepN) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2F (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapHVectorRanked10 rsum
                                                 $ mapHVectorRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [voidFromSh @Double ZSR])
                       (rreplicate 2 (rreplicate 5 ((rscalar 2) * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (rconcrete $ Nested.rfromListPrimLinear [] [285.95794829475744])
    (crev h (rscalar 1.1))

testSin0FoldNestedS1 :: Assertion
testSin0FoldNestedS1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1PP :: Assertion
testSin0FoldNestedS1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
      f z = sfold (\x a ->
               sfold (\x2 a2 -> x2 + tan a2)
                     a (sreplicate @_ @22 x))
                  z (sreplicate @_ @11 z)
      g :: forall g. ADReady g => HVector g -> g TKUntyped
      g x = srev (\v -> f (sfromD $ dunHVector v V.! 0))
                 (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
                 (dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicShaped @Double @'[] (sscalar 1.1)))
    @?= "let v6 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (sreplicate 1.1))), sreplicate 1.1))) in [ssum (tproject2 v6) + tproject1 v6]"

testSin0FoldNestedR1PP :: Assertion
testSin0FoldNestedR1PP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (dmkHVector x)
  printAstPretty
    IM.empty
    (g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR1SimpPP :: Assertion
testSin0FoldNestedR1SimpPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (dmkHVector x)
  printAstPretty
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) <lambda> <lambda> <lambda> 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) <lambda> <lambda> <lambda> 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR1SimpNestedPP :: Assertion
testSin0FoldNestedR1SimpNestedPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 22 x))
                  z (rreplicate 11 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                   (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                   (dmkHVector x)
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let v5 = dmapAccumRDer (SNat @11) (\\x7 -> let v14 = dmapAccumRDer (SNat @22) (\\x15 -> let x22 = cos (tproject2 (tproject2 (tproject2 x15))) in tpair (tproject1 x15, recip (x22 * x22) * tproject1 x15)) (\\x23 -> let x35 = cos (tproject2 (tproject2 (tproject2 (tproject2 x23)))) ; x36 = x35 * x35 ; x37 = tproject2 (tproject2 (tproject2 (tproject1 x23))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x23))))) in tpair (tproject1 (tproject1 x23), ((x37 * x35 + x37 * x35) * negate (recip (x36 * x36))) * tproject1 (tproject2 x23) + tproject1 (tproject1 x23) * recip x36)) (\\x38 -> let x47 = cos (tproject2 (tproject2 (tproject2 (tproject2 x38)))) ; x48 = x47 * x47 ; x49 = negate (recip (x48 * x48)) * (tproject1 (tproject2 x38) * tproject2 (tproject1 x38)) in tpair (recip x48 * tproject2 (tproject1 x38) + tproject1 (tproject1 x38), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x38))))) * (x47 * x49 + x47 * x49))))) (tproject1 x7) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x50 -> tpair (tproject1 x50 + tan (tproject2 x50), tpair (tproject1 x50, []))) (\\x56 -> let x68 = cos (tproject2 (tproject2 x56)) in tpair (tproject1 (tproject1 x56) + tproject2 (tproject1 x56) * recip (x68 * x68), tpair (tproject1 (tproject1 x56), []))) (\\x69 -> let x74 = cos (tproject2 (tproject2 x69)) in tpair (tproject1 (tproject1 x69) + tproject1 (tproject2 (tproject1 x69)), recip (x74 * x74) * tproject1 (tproject1 x69))) (tproject2 (tproject2 (tproject2 x7))) (rreplicate 22 (tproject1 (tproject2 (tproject2 x7)))))), rreplicate 22 (tproject1 (tproject2 (tproject2 x7)))))) in tpair (rsum (tproject2 v14), tproject1 v14)) (\\x75 -> let v79 = dmapAccumLDer (SNat @22) (\\x89 -> tpair (tproject1 x89 + tan (tproject2 x89), tpair (tproject1 x89, tpair (tproject1 x89, [])))) (\\x95 -> let x98 = cos (tproject2 (tproject2 x95)) in tpair (tproject1 (tproject1 x95) + tproject2 (tproject1 x95) * recip (x98 * x98), tpair (tproject1 (tproject1 x95), tpair (tproject1 (tproject1 x95), [])))) (\\x103 -> let x106 = cos (tproject2 (tproject2 x103)) in tpair (tproject1 (tproject2 (tproject1 x103)) + tproject1 (tproject1 x103) + tproject1 (tproject2 (tproject2 (tproject1 x103))), recip (x106 * x106) * tproject1 (tproject1 x103))) (tproject2 (tproject2 (tproject2 (tproject2 x75)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))) ; v86 = dmapAccumRDer (SNat @22) (\\x110 -> let x115 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x110))))) ; x116 = x115 * x115 ; x117 = tproject2 (tproject2 (tproject1 (tproject2 x110))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x110)))))) in tpair (tproject1 x110, ((x117 * x115 + x117 * x115) * negate (recip (x116 * x116))) * tproject1 (tproject2 (tproject2 x110)) + tproject1 x110 * recip x116)) (\\x118 -> let x124 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x118)))))) ; x125 = x124 * x124 ; x126 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x118))))))) ; x127 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x118)))) * x126 ; x128 = x125 * x125 ; x129 = x127 * x124 + x127 * x124 ; x130 = negate (recip x128) ; x135 = tproject2 (tproject2 (tproject1 (tproject2 (tproject1 x118)))) * x126 + ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x118))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x118))))))) * -1.0) * tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x118)))) ; x136 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x118))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x118))))))) ; x140 = x136 * x124 + x136 * x124 in tpair (tproject1 (tproject1 x118), ((x135 * x124 + x136 * x127 + x135 * x124 + x136 * x127) * x130 + (((x140 * x125 + x140 * x125) * negate (recip (x128 * x128))) * -1.0) * x129) * tproject1 (tproject2 (tproject2 (tproject2 x118))) + tproject1 (tproject2 (tproject2 (tproject1 x118))) * (x129 * x130) + tproject1 (tproject1 x118) * recip x125 + (x140 * negate (recip (x125 * x125))) * tproject1 (tproject2 x118))) (\\x149 -> let x154 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x149)))))) ; x155 = x154 * x154 ; x156 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x149))))))) ; x157 = tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x149)))) * x156 ; x158 = x155 * x155 ; x159 = x157 * x154 + x157 * x154 ; x160 = negate (recip x158) ; x164 = tproject1 (tproject2 (tproject2 (tproject2 x149))) * tproject2 (tproject1 x149) ; x165 = negate (recip (x158 * x158)) * (-1.0 * (x159 * x164)) ; x166 = x160 * x164 ; x167 = x154 * x166 + x154 * x166 ; x168 = x155 * x165 + x155 * x165 + negate (recip (x155 * x155)) * (tproject1 (tproject2 x149) * tproject2 (tproject1 x149)) in tpair (recip x155 * tproject2 (tproject1 x149) + tproject1 (tproject1 x149), tpair (tpair ([], tpair (0.0, x156 * x167)), tpair ((x159 * x160) * tproject2 (tproject1 x149), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x149))))))) * (x154 * x168 + x154 * x168 + x157 * x166 + x157 * x166) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x149)))))) * (-1.0 * (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 x149)))) * x167)))))))) (tproject1 (tproject1 x75)) (tpair (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x169 -> let x170 = cos (tproject2 (tproject2 (tproject2 x169))) in tpair (tproject1 x169 + tproject1 (tproject2 x169) * recip (x170 * x170), tpair (tproject1 x169, []))) (\\x171 -> let x175 = cos (tproject2 (tproject2 (tproject2 (tproject2 x171)))) ; x176 = x175 * x175 ; x178 = tproject2 (tproject2 (tproject2 (tproject1 x171))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x171))))) in tpair (tproject1 (tproject1 x171) + tproject1 (tproject2 (tproject1 x171)) * recip x176 + ((x178 * x175 + x178 * x175) * negate (recip (x176 * x176))) * tproject1 (tproject2 (tproject2 x171)), tpair (tproject1 (tproject1 x171), []))) (\\x183 -> let x186 = cos (tproject2 (tproject2 (tproject2 (tproject2 x183)))) ; x187 = x186 * x186 ; x190 = negate (recip (x187 * x187)) * (tproject1 (tproject2 (tproject2 x183)) * tproject1 (tproject1 x183)) in tpair (tproject1 (tproject1 x183) + tproject1 (tproject2 (tproject1 x183)), tpair (recip x187 * tproject1 (tproject1 x183), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x183))))) * (x186 * x190 + x186 * x190))))) (tproject2 (tproject2 (tproject2 (tproject1 x75)))) (tpair (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x75)))), tpair (tproject1 (tproject2 v79), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject1 x75)))))), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x191 -> let x194 = cos (tproject2 (tproject2 (tproject2 x191))) in tpair (tproject1 x191, tpair (tproject1 x191, recip (x194 * x194) * tproject1 x191))) (\\x197 -> let x201 = let x198 = cos (tproject2 (tproject2 (tproject2 (tproject2 x197)))) ; x199 = x198 * x198 ; x200 = tproject2 (tproject2 (tproject2 (tproject1 x197))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x197))))) in tpair (tproject1 (tproject1 x197), ((x200 * x198 + x200 * x198) * negate (recip (x199 * x199))) * tproject1 (tproject2 x197) + tproject1 (tproject1 x197) * recip x199) in tpair (tproject1 x201, tpair (tproject1 (tproject1 x197), tproject2 x201))) (\\x202 -> let x210 = let x207 = cos (tproject2 (tproject2 (tproject2 (tproject2 x202)))) ; x208 = x207 * x207 ; x209 = negate (recip (x208 * x208)) * (tproject1 (tproject2 x202) * tproject2 (tproject2 (tproject1 x202))) in tpair (recip x208 * tproject2 (tproject2 (tproject1 x202)) + tproject1 (tproject1 x202), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x202))))) * (x207 * x209 + x207 * x209)))) in tpair (tproject1 x210 + tproject1 (tproject2 (tproject1 x202)), tproject2 x210)) (tproject1 (tproject2 x75)) (tpair ([], tpair (tproject1 (tproject2 (tproject2 v79)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))), tpair ([], tpair (tproject1 (tproject2 (tproject2 v79)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x75))))))))) in tpair (rsum (tproject2 v86), tproject1 v86)) (\\x211 -> let v214 = dmapAccumLDer (SNat @22) (\\x227 -> tpair (tproject1 x227 + tan (tproject2 x227), tpair (tproject1 x227, tpair (tproject1 x227, [])))) (\\x233 -> let x236 = cos (tproject2 (tproject2 x233)) in tpair (tproject1 (tproject1 x233) + tproject2 (tproject1 x233) * recip (x236 * x236), tpair (tproject1 (tproject1 x233), tpair (tproject1 (tproject1 x233), [])))) (\\x241 -> let x244 = cos (tproject2 (tproject2 x241)) in tpair (tproject1 (tproject2 (tproject1 x241)) + tproject1 (tproject1 x241) + tproject1 (tproject2 (tproject2 (tproject1 x241))), recip (x244 * x244) * tproject1 (tproject1 x241))) (tproject2 (tproject2 (tproject2 (tproject2 x211)))) (rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x211))))) ; v221 = dmapAccumLDer (SNat @22) (\\x248 -> let x253 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x248))))) ; x254 = x253 * x253 ; x255 = negate (recip (x254 * x254)) * (tproject1 (tproject2 (tproject2 x248)) * tproject1 (tproject2 x248)) in tpair (recip x254 * tproject1 (tproject2 x248) + tproject1 x248, tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x248)))))) * (x253 * x255 + x253 * x255))))) (\\x256 -> let x262 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x256)))))) ; x263 = x262 * x262 ; x264 = x263 * x263 ; x265 = negate (recip x264) ; x266 = tproject1 (tproject2 (tproject2 (tproject2 x256))) * tproject1 (tproject2 (tproject2 x256)) ; x267 = x265 * x266 ; x271 = tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x256))))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x256))))))) ; x272 = x271 * x262 + x271 * x262 ; x282 = (((x272 * x263 + x272 * x263) * negate (recip (x264 * x264))) * -1.0) * x266 + (tproject1 (tproject2 (tproject2 (tproject1 x256))) * tproject1 (tproject2 (tproject2 x256)) + tproject1 (tproject2 (tproject1 x256)) * tproject1 (tproject2 (tproject2 (tproject2 x256)))) * x265 in tpair (tproject1 (tproject1 x256) + (x272 * negate (recip (x263 * x263))) * tproject1 (tproject2 (tproject2 x256)) + tproject1 (tproject2 (tproject1 x256)) * recip x263, tpair ([], tpair (0.0, ((tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 x256))))) * cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x256))))))) * -1.0) * (x262 * x267 + x262 * x267) + (x271 * x267 + x282 * x262 + x271 * x267 + x282 * x262) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x256))))))))))) (\\x287 -> let x292 = cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x287)))))) ; x293 = x292 * x292 ; x294 = x293 * x293 ; x295 = negate (recip x294) ; x296 = tproject1 (tproject2 (tproject2 (tproject2 x287))) * tproject1 (tproject2 (tproject2 x287)) ; x297 = x295 * x296 ; x302 = negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x287))))))) * tproject2 (tproject2 (tproject2 (tproject1 x287))) ; x303 = x292 * x302 + x292 * x302 ; x304 = x295 * x303 ; x305 = negate (recip (x294 * x294)) * (-1.0 * (x296 * x303)) ; x306 = x293 * x305 + x293 * x305 + negate (recip (x293 * x293)) * (tproject1 (tproject2 (tproject2 x287)) * tproject1 (tproject1 x287)) in tpair (tproject1 (tproject1 x287), tpair (tproject1 (tproject2 (tproject2 (tproject2 x287))) * x304 + recip x293 * tproject1 (tproject1 x287), tpair (tproject1 (tproject2 (tproject2 x287)) * x304, tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x287))))))) * (x292 * x306 + x292 * x306 + x297 * x302 + x297 * x302) + cos (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 x287)))))) * (-1.0 * ((x292 * x297 + x292 * x297) * tproject2 (tproject2 (tproject2 (tproject1 x287))))))))))) (0.0 + tproject2 (tproject1 x211)) (tpair (rconcrete (rfromListLinear [22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) + rreplicate 22 (tproject1 (tproject1 x211)), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @22) (\\x307 -> let x310 = cos (tproject2 (tproject2 (tproject2 x307))) in tpair (tproject1 x307, tpair (tproject1 x307, recip (x310 * x310) * tproject1 x307))) (\\x313 -> let x321 = let x318 = cos (tproject2 (tproject2 (tproject2 (tproject2 x313)))) ; x319 = x318 * x318 ; x320 = tproject2 (tproject2 (tproject2 (tproject1 x313))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x313))))) in tpair (tproject1 (tproject1 x313), ((x320 * x318 + x320 * x318) * negate (recip (x319 * x319))) * tproject1 (tproject2 x313) + tproject1 (tproject1 x313) * recip x319) in tpair (tproject1 x321, tpair (tproject1 (tproject1 x313), tproject2 x321))) (\\x322 -> let x326 = let x323 = cos (tproject2 (tproject2 (tproject2 (tproject2 x322)))) ; x324 = x323 * x323 ; x325 = negate (recip (x324 * x324)) * (tproject1 (tproject2 x322) * tproject2 (tproject2 (tproject1 x322))) in tpair (recip x324 * tproject2 (tproject2 (tproject1 x322)) + tproject1 (tproject1 x322), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x322))))) * (x323 * x325 + x323 * x325)))) in tpair (tproject1 x326 + tproject1 (tproject2 (tproject1 x322)), tproject2 x326)) (tproject1 (tproject2 x211)) (tpair ([], tpair (tproject1 (tproject2 (tproject2 v214)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x211))))))))), tpair ([], tpair (tproject1 (tproject2 (tproject2 v214)), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x211))))))))) ; v225 = dmapAccumRDer (SNat @22) (\\x327 -> let x328 = cos (tproject2 (tproject2 (tproject2 x327))) in tpair (tproject1 x327 + tproject1 (tproject1 (tproject2 x327)), recip (x328 * x328) * tproject1 x327)) (\\x329 -> let x333 = cos (tproject2 (tproject2 (tproject2 (tproject2 x329)))) ; x334 = x333 * x333 ; x337 = tproject2 (tproject2 (tproject2 (tproject1 x329))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x329))))) in tpair (tproject1 (tproject1 x329) + tproject1 (tproject1 (tproject2 (tproject1 x329))), ((x337 * x333 + x337 * x333) * negate (recip (x334 * x334))) * tproject1 (tproject2 x329) + tproject1 (tproject1 x329) * recip x334)) (\\x341 -> let x344 = cos (tproject2 (tproject2 (tproject2 (tproject2 x341)))) ; x345 = x344 * x344 ; x348 = negate (recip (x345 * x345)) * (tproject1 (tproject2 x341) * tproject2 (tproject1 x341)) in tpair (tproject1 (tproject1 x341) + recip x345 * tproject2 (tproject1 x341), tpair (tpair (tproject1 (tproject1 x341), []), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x341))))) * (x344 * x348 + x344 * x348))))) 0.0 (tpair (tpair (tproject1 (tproject2 (tproject2 v221)), []), tpair (tproject1 (tproject2 v214), rreplicate 22 (tproject1 (tproject2 (tproject2 (tproject2 x211))))))) in tpair (tproject1 v221, tpair ([], tpair (rsum (tproject2 v225) + rsum (tproject2 (tproject2 (tproject2 v221))), tproject1 v225)))) 1.0 (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @11) (\\x349 -> tpair (tproject1 (dmapAccumLDer (SNat @22) (\\x354 -> tpair (tproject1 x354 + tan (tproject2 x354), [])) (\\x356 -> let x363 = cos (tproject2 (tproject2 x356)) in tpair (tproject1 (tproject1 x356) + tproject2 (tproject1 x356) * recip (x363 * x363), [])) (\\x364 -> let x369 = cos (tproject2 (tproject2 x364)) in tpair (tproject1 (tproject1 x364), recip (x369 * x369) * tproject1 (tproject1 x364))) (tproject2 x349) (rreplicate 22 (tproject1 x349))), tpair (tproject1 x349, []))) (\\x370 -> tpair (tproject1 (dmapAccumLDer (SNat @22) (\\x380 -> let x389 = cos (tproject2 (tproject2 (tproject2 x380))) in tpair (tproject1 x380 + tproject1 (tproject2 x380) * recip (x389 * x389), [])) (\\x390 -> let x403 = cos (tproject2 (tproject2 (tproject2 (tproject2 x390)))) ; x404 = x403 * x403 ; x405 = tproject2 (tproject2 (tproject2 (tproject1 x390))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x390))))) in tpair (tproject1 (tproject1 x390) + tproject1 (tproject2 (tproject1 x390)) * recip x404 + ((x405 * x403 + x405 * x403) * negate (recip (x404 * x404))) * tproject1 (tproject2 (tproject2 x390)), [])) (\\x406 -> let x415 = cos (tproject2 (tproject2 (tproject2 (tproject2 x406)))) ; x416 = x415 * x415 ; x417 = negate (recip (x416 * x416)) * (tproject1 (tproject2 (tproject2 x406)) * tproject1 (tproject1 x406)) in tpair (tproject1 (tproject1 x406), tpair (recip x416 * tproject1 (tproject1 x406), tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x406))))) * (x415 * x417 + x415 * x417))))) (tproject2 (tproject1 x370)) (tpair (rreplicate 22 (tproject1 (tproject1 x370)), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x418 -> tpair (tproject1 x418 + tan (tproject2 x418), tpair (tproject1 x418, []))) (\\x424 -> let x430 = cos (tproject2 (tproject2 x424)) in tpair (tproject1 (tproject1 x424) + tproject2 (tproject1 x424) * recip (x430 * x430), tpair (tproject1 (tproject1 x424), []))) (\\x431 -> let x440 = cos (tproject2 (tproject2 x431)) in tpair (tproject1 (tproject1 x431) + tproject1 (tproject2 (tproject1 x431)), recip (x440 * x440) * tproject1 (tproject1 x431))) (tproject2 (tproject2 x370)) (rreplicate 22 (tproject1 (tproject2 x370))))), rreplicate 22 (tproject1 (tproject2 x370)))))), tpair (tproject1 (tproject1 x370), []))) (\\x441 -> let v442 = dmapAccumRDer (SNat @22) (\\x445 -> let x446 = cos (tproject2 (tproject2 (tproject2 x445))) in tpair (tproject1 x445, recip (x446 * x446) * tproject1 x445)) (\\x447 -> let x448 = cos (tproject2 (tproject2 (tproject2 (tproject2 x447)))) ; x449 = x448 * x448 ; x450 = tproject2 (tproject2 (tproject2 (tproject1 x447))) * negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x447))))) in tpair (tproject1 (tproject1 x447), ((x450 * x448 + x450 * x448) * negate (recip (x449 * x449))) * tproject1 (tproject2 x447) + tproject1 (tproject1 x447) * recip x449)) (\\x451 -> let x452 = cos (tproject2 (tproject2 (tproject2 (tproject2 x451)))) ; x453 = x452 * x452 ; x454 = negate (recip (x453 * x453)) * (tproject1 (tproject2 x451) * tproject2 (tproject1 x451)) in tpair (recip x453 * tproject2 (tproject1 x451) + tproject1 (tproject1 x451), tpair ([], tpair (0.0, negate (sin (tproject2 (tproject2 (tproject2 (tproject2 x451))))) * (x452 * x454 + x452 * x454))))) (tproject1 (tproject1 x441)) (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @22) (\\x455 -> tpair (tproject1 x455 + tan (tproject2 x455), tpair (tproject1 x455, []))) (\\x456 -> let x457 = cos (tproject2 (tproject2 x456)) in tpair (tproject1 (tproject1 x456) + tproject2 (tproject1 x456) * recip (x457 * x457), tpair (tproject1 (tproject1 x456), []))) (\\x458 -> let x459 = cos (tproject2 (tproject2 x458)) in tpair (tproject1 (tproject1 x458) + tproject1 (tproject2 (tproject1 x458)), recip (x459 * x459) * tproject1 (tproject1 x458))) (tproject2 (tproject2 x441)) (rreplicate 22 (tproject1 (tproject2 x441))))), rreplicate 22 (tproject1 (tproject2 x441))))) in tpair (rsum (tproject2 v442) + tproject1 (tproject2 (tproject1 x441)), tproject1 v442)) 1.1 (rreplicate 11 1.1))), rreplicate 11 1.1))) in [rsum (tproject2 v5) + tproject1 v5]"

testSin0FoldNestedR0LengthPPs :: Assertion
testSin0FoldNestedR0LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInline
       $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 1687

testSin0FoldNestedR1LengthPPs :: Assertion
testSin0FoldNestedR1LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 -> x2 + tan a2)
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
      IM.empty
      (simplifyInline
       $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 21119

testSin0FoldNestedR2LengthPPs :: Assertion
testSin0FoldNestedR2LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 -> x3 + tan a3)
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 288599

testSin0FoldNestedR3LengthPPs :: Assertion
testSin0FoldNestedR3LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 ->
                   rfold (\x4 a4 -> x4 + tan a4)
                         a3 (rreplicate 2 x3))
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 4512219

-- Takes 100s, probably due to some of the pipelines forcing all derivs.
_testSin0FoldNestedR4LengthPPs :: Assertion
_testSin0FoldNestedR4LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

_testSin0FoldNestedR5LengthPPs :: Assertion
_testSin0FoldNestedR5LengthPPs = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 0

testSin0FoldNestedR2LengthPPsDummy7 :: Assertion
testSin0FoldNestedR2LengthPPsDummy7 = do
  resetVarCounter
  let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\_x3 _a3 -> rscalar 7)
                   -- the 7 causes Dummy RepM values
                   -- with the more precise typing of folds
                       a2 (rreplicate 2 x2))
                     a (rreplicate 2 x))
                  z (rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 81081

testSin0FoldNestedR2Dummy7 :: Assertion
testSin0FoldNestedR2Dummy7 = do
 resetVarCounter
 assertEqualUpToEpsilon' 1e-10
  (rscalar 0 :: RepN (TKR Double 0))
  (rev'
   (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
  (rscalar 25.000016360009603 :: RepN (TKR Double 0))
  (rev'
   (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
        f z = rfold (\x a ->
                 rfold (\x2 a2 ->
                   rfold (\x3 a3 -> x3 + tan a3)
                         a2 (rreplicate 2 x2))
                       a (rreplicate 2 x))
                    z (rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR1PP :: Assertion
testSin0MapAccumNestedR1PP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 -> let y = rfromD @Double @0 $ dunHVector x2 V.! 0
                                    w = rfromD @Double @0 $ dunHVector a2 V.! 0
                                in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (dmkHVector V.empty))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  printAstPrettyButNested
    IM.empty
    (simplifyInline
     $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "let h12 = dmapAccumRDer (SNat @2) (\\h16 -> let h25 = dmapAccumRDer (SNat @2) (\\h26 -> let x33 = cos (rproject (tproject2 (tproject2 (tproject2 h26))) 0) in tpair ([rproject (tproject1 h26) 0], [recip (x33 * x33) * rproject (tproject1 h26) 0])) (\\h34 -> let x46 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h34)))) 0) ; x47 = x46 * x46 ; x48 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h34)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h34)))) 0)) in tpair ([rproject (tproject1 (tproject1 h34)) 0], [((x48 * x46 + x48 * x46) * negate (recip (x47 * x47))) * rproject (tproject1 (tproject2 h34)) 0 + rproject (tproject1 (tproject1 h34)) 0 * recip x47])) (\\h49 -> let x58 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h49)))) 0) ; x59 = x58 * x58 ; x60 = negate (recip (x59 * x59)) * (rproject (tproject1 (tproject2 h49)) 0 * rproject (tproject2 (tproject1 h49)) 0) in tpair ([recip x59 * rproject (tproject2 (tproject1 h49)) 0 + rproject (tproject1 (tproject1 h49)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h49)))) 0)) * (x58 * x60 + x58 * x60)])))) (tproject1 h16) (tpair (tproject1 (tproject2 h16), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h61 -> tpair ([rproject (tproject1 h61) 0 + tan (rproject (tproject2 h61) 0)], tpair (tproject1 h61, []))) (\\h68 -> let x81 = cos (rproject (tproject2 (tproject2 h68)) 0) in tpair ([rproject (tproject1 (tproject1 h68)) 0 + rproject (tproject2 (tproject1 h68)) 0 * recip (x81 * x81)], tpair (tproject1 (tproject1 h68), []))) (\\h82 -> let x88 = cos (rproject (tproject2 (tproject2 h82)) 0) in tpair ([rproject (tproject1 (tproject1 h82)) 0 + rproject (tproject1 (tproject2 (tproject1 h82))) 0], [recip (x88 * x88) * rproject (tproject1 (tproject1 h82)) 0])) (tproject2 (tproject2 (tproject2 h16))) [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h16))) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 h16))) 0)]))) in tpair ([rsum (rproject (tproject2 h25) 0)], [rproject (tproject1 h25) 0])) (\\h89 -> let h93 = dmapAccumLDer (SNat @2) (\\h106 -> tpair ([rproject (tproject1 h106) 0 + tan (rproject (tproject2 h106) 0)], tpair (tproject1 h106, tpair (tproject1 h106, [])))) (\\h113 -> let x116 = cos (rproject (tproject2 (tproject2 h113)) 0) in tpair ([rproject (tproject1 (tproject1 h113)) 0 + rproject (tproject2 (tproject1 h113)) 0 * recip (x116 * x116)], tpair (tproject1 (tproject1 h113), tpair (tproject1 (tproject1 h113), [])))) (\\h122 -> let x125 = cos (rproject (tproject2 (tproject2 h122)) 0) in tpair ([rproject (tproject1 (tproject2 (tproject1 h122))) 0 + rproject (tproject1 (tproject1 h122)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h122)))) 0], [recip (x125 * x125) * rproject (tproject1 (tproject1 h122)) 0])) (tproject2 (tproject2 (tproject2 (tproject2 h89)))) [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h89)))) 0)] ; h102 = dmapAccumRDer (SNat @2) (\\h131 -> let x136 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h131))))) 0) ; x137 = x136 * x136 ; x138 = rproject (tproject2 (tproject2 (tproject1 (tproject2 h131)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h131))))) 0)) in tpair ([rproject (tproject1 h131) 0], [((x138 * x136 + x138 * x136) * negate (recip (x137 * x137))) * rproject (tproject1 (tproject2 (tproject2 h131))) 0 + rproject (tproject1 h131) 0 * recip x137])) (\\h139 -> let x145 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h139)))))) 0) ; x146 = x145 * x145 ; x147 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h139)))))) 0)) ; x148 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h139))))) 0 * x147 ; x149 = x146 * x146 ; x150 = x148 * x145 + x148 * x145 ; x151 = negate (recip x149) ; x156 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject1 h139))))) 0 * x147 + ((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h139)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h139)))))) 0)) * -1.0) * rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h139))))) 0 ; x157 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h139)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h139)))))) 0)) ; x161 = x157 * x145 + x157 * x145 in tpair ([rproject (tproject1 (tproject1 h139)) 0], [((x156 * x145 + x157 * x148 + x156 * x145 + x157 * x148) * x151 + (((x161 * x146 + x161 * x146) * negate (recip (x149 * x149))) * -1.0) * x150) * rproject (tproject1 (tproject2 (tproject2 (tproject2 h139)))) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h139)))) 0 * (x150 * x151) + rproject (tproject1 (tproject1 h139)) 0 * recip x146 + (x161 * negate (recip (x146 * x146))) * rproject (tproject1 (tproject2 h139)) 0])) (\\h170 -> let x175 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h170)))))) 0) ; x176 = x175 * x175 ; x177 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h170)))))) 0)) ; x178 = rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h170))))) 0 * x177 ; x179 = x176 * x176 ; x180 = x178 * x175 + x178 * x175 ; x181 = negate (recip x179) ; x185 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h170)))) 0 * rproject (tproject2 (tproject1 h170)) 0 ; x186 = negate (recip (x179 * x179)) * (-1.0 * (x180 * x185)) ; x187 = x181 * x185 ; x188 = x175 * x187 + x175 * x187 ; x189 = x176 * x186 + x176 * x186 + negate (recip (x176 * x176)) * (rproject (tproject1 (tproject2 h170)) 0 * rproject (tproject2 (tproject1 h170)) 0) in tpair ([recip x176 * rproject (tproject2 (tproject1 h170)) 0 + rproject (tproject1 (tproject1 h170)) 0], tpair (tpair ([], tpair ([0], [x177 * x188])), tpair ([(x180 * x181) * rproject (tproject2 (tproject1 h170)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h170)))))) 0)) * (x175 * x189 + x175 * x189 + x178 * x187 + x178 * x187) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h170)))))) 0) * (-1.0 * (rproject (tproject2 (tproject2 (tproject1 (tproject2 (tproject2 h170))))) 0 * x188))])))))) [rproject (tproject1 (tproject1 h89)) 0] (tpair (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h190 -> let x191 = cos (rproject (tproject2 (tproject2 (tproject2 h190))) 0) in tpair ([rproject (tproject1 h190) 0 + rproject (tproject1 (tproject2 h190)) 0 * recip (x191 * x191)], tpair (tproject1 h190, []))) (\\h192 -> let x196 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h192)))) 0) ; x197 = x196 * x196 ; x199 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h192)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h192)))) 0)) in tpair ([rproject (tproject1 (tproject1 h192)) 0 + rproject (tproject1 (tproject2 (tproject1 h192))) 0 * recip x197 + ((x199 * x196 + x199 * x196) * negate (recip (x197 * x197))) * rproject (tproject1 (tproject2 (tproject2 h192))) 0], tpair ([rproject (tproject1 (tproject1 h192)) 0], []))) (\\h204 -> let x207 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h204)))) 0) ; x208 = x207 * x207 ; x211 = negate (recip (x208 * x208)) * (rproject (tproject1 (tproject2 (tproject2 h204))) 0 * rproject (tproject1 (tproject1 h204)) 0) in tpair ([rproject (tproject1 (tproject1 h204)) 0 + rproject (tproject1 (tproject2 (tproject1 h204))) 0], tpair ([recip x208 * rproject (tproject1 (tproject1 h204)) 0], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h204)))) 0)) * (x207 * x211 + x207 * x211)])))) [rproject (tproject2 (tproject2 (tproject2 (tproject1 h89)))) 0] (tpair ([rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h89)))) 0)], tpair (tproject1 (tproject2 h93), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h89)))) 0)]))))), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject1 h89)))) 0)])), tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h212 -> let x215 = cos (rproject (tproject2 (tproject2 (tproject2 h212))) 0) in tpair ([rproject (tproject1 h212) 0], tpair (tproject1 h212, [recip (x215 * x215) * rproject (tproject1 h212) 0]))) (\\h219 -> let h223 = let x220 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h219)))) 0) ; x221 = x220 * x220 ; x222 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h219)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h219)))) 0)) in tpair ([rproject (tproject1 (tproject1 h219)) 0], [((x222 * x220 + x222 * x220) * negate (recip (x221 * x221))) * rproject (tproject1 (tproject2 h219)) 0 + rproject (tproject1 (tproject1 h219)) 0 * recip x221]) in tpair (tproject1 h223, tpair (tproject1 (tproject1 h219), tproject2 h223))) (\\h224 -> let h232 = let x229 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h224)))) 0) ; x230 = x229 * x229 ; x231 = negate (recip (x230 * x230)) * (rproject (tproject1 (tproject2 h224)) 0 * rproject (tproject2 (tproject2 (tproject1 h224))) 0) in tpair ([recip x230 * rproject (tproject2 (tproject2 (tproject1 h224))) 0 + rproject (tproject1 (tproject1 h224)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h224)))) 0)) * (x229 * x231 + x229 * x231)]))) in tpair ([rproject (tproject1 h232) 0 + rproject (tproject1 (tproject2 (tproject1 h224))) 0], tproject2 h232)) (tproject1 (tproject2 h89)) (tpair (tproject1 (tproject2 (tproject2 h89)), tpair (tproject1 (tproject2 (tproject2 h93)), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h89)))) 0)]))))), tpair (tproject1 (tproject2 (tproject2 h89)), tpair (tproject1 (tproject2 (tproject2 h93)), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h89)))) 0)]))))) in tpair ([rsum (rproject (tproject2 h102) 0)], [rproject (tproject1 h102) 0])) (\\h233 -> let h236 = dmapAccumLDer (SNat @2) (\\h254 -> tpair ([rproject (tproject1 h254) 0 + tan (rproject (tproject2 h254) 0)], tpair (tproject1 h254, tpair (tproject1 h254, [])))) (\\h261 -> let x264 = cos (rproject (tproject2 (tproject2 h261)) 0) in tpair ([rproject (tproject1 (tproject1 h261)) 0 + rproject (tproject2 (tproject1 h261)) 0 * recip (x264 * x264)], tpair (tproject1 (tproject1 h261), tpair (tproject1 (tproject1 h261), [])))) (\\h270 -> let x273 = cos (rproject (tproject2 (tproject2 h270)) 0) in tpair ([rproject (tproject1 (tproject2 (tproject1 h270))) 0 + rproject (tproject1 (tproject1 h270)) 0 + rproject (tproject1 (tproject2 (tproject2 (tproject1 h270)))) 0], [recip (x273 * x273) * rproject (tproject1 (tproject1 h270)) 0])) (tproject2 (tproject2 (tproject2 (tproject2 h233)))) [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h233)))) 0)] ; h245 = dmapAccumLDer (SNat @2) (\\h279 -> let x284 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h279))))) 0) ; x285 = x284 * x284 ; x286 = negate (recip (x285 * x285)) * (rproject (tproject1 (tproject2 (tproject2 h279))) 0 * rproject (tproject1 (tproject2 h279)) 0) in tpair ([recip x285 * rproject (tproject1 (tproject2 h279)) 0 + rproject (tproject1 h279) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h279))))) 0)) * (x284 * x286 + x284 * x286)])))) (\\h287 -> let x293 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h287)))))) 0) ; x294 = x293 * x293 ; x295 = x294 * x294 ; x296 = negate (recip x295) ; x297 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h287)))) 0 * rproject (tproject1 (tproject2 (tproject2 h287))) 0 ; x298 = x296 * x297 ; x302 = rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h287)))))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h287)))))) 0)) ; x303 = x302 * x293 + x302 * x293 ; x313 = (((x303 * x294 + x303 * x294) * negate (recip (x295 * x295))) * -1.0) * x297 + (rproject (tproject1 (tproject2 (tproject2 (tproject1 h287)))) 0 * rproject (tproject1 (tproject2 (tproject2 h287))) 0 + rproject (tproject1 (tproject2 (tproject1 h287))) 0 * rproject (tproject1 (tproject2 (tproject2 (tproject2 h287)))) 0) * x296 in tpair ([rproject (tproject1 (tproject1 h287)) 0 + (x303 * negate (recip (x294 * x294))) * rproject (tproject1 (tproject2 (tproject2 h287))) 0 + rproject (tproject1 (tproject2 (tproject1 h287))) 0 * recip x294], tpair ([], tpair ([0.0], [((rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject1 h287)))))) 0 * cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h287)))))) 0)) * -1.0) * (x293 * x298 + x293 * x298) + (x302 * x298 + x313 * x293 + x302 * x298 + x313 * x293) * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h287)))))) 0))])))) (\\h318 -> let x323 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h318)))))) 0) ; x324 = x323 * x323 ; x325 = x324 * x324 ; x326 = negate (recip x325) ; x327 = rproject (tproject1 (tproject2 (tproject2 (tproject2 h318)))) 0 * rproject (tproject1 (tproject2 (tproject2 h318))) 0 ; x328 = x326 * x327 ; x333 = negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h318)))))) 0)) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h318)))) 0 ; x334 = x323 * x333 + x323 * x333 ; x335 = x326 * x334 ; x336 = negate (recip (x325 * x325)) * (-1.0 * (x327 * x334)) ; x337 = x324 * x336 + x324 * x336 + negate (recip (x324 * x324)) * (rproject (tproject1 (tproject2 (tproject2 h318))) 0 * rproject (tproject1 (tproject1 h318)) 0) in tpair ([rproject (tproject1 (tproject1 h318)) 0], tpair ([rproject (tproject1 (tproject2 (tproject2 (tproject2 h318)))) 0 * x335 + recip x324 * rproject (tproject1 (tproject1 h318)) 0], tpair ([rproject (tproject1 (tproject2 (tproject2 h318))) 0 * x335], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h318)))))) 0)) * (x323 * x337 + x323 * x337 + x328 * x333 + x328 * x333) + cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 (tproject2 h318)))))) 0) * (-1.0 * ((x323 * x328 + x323 * x328) * rproject (tproject2 (tproject2 (tproject2 (tproject1 h318)))) 0))])))))) [0.0 + rproject (tproject2 (tproject1 h233)) 0] (tpair ([rconcrete (rfromListLinear [2] [0.0,0.0]) + rreplicate 2 (rproject (tproject1 (tproject1 h233)) 0)], tpair (tproject1 (tproject2 (dmapAccumRDer (SNat @2) (\\h338 -> let x341 = cos (rproject (tproject2 (tproject2 (tproject2 h338))) 0) in tpair ([rproject (tproject1 h338) 0], tpair (tproject1 h338, [recip (x341 * x341) * rproject (tproject1 h338) 0]))) (\\h345 -> let h353 = let x350 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h345)))) 0) ; x351 = x350 * x350 ; x352 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h345)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h345)))) 0)) in tpair ([rproject (tproject1 (tproject1 h345)) 0], [((x352 * x350 + x352 * x350) * negate (recip (x351 * x351))) * rproject (tproject1 (tproject2 h345)) 0 + rproject (tproject1 (tproject1 h345)) 0 * recip x351]) in tpair (tproject1 h353, tpair (tproject1 (tproject1 h345), tproject2 h353))) (\\h354 -> let h358 = let x355 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h354)))) 0) ; x356 = x355 * x355 ; x357 = negate (recip (x356 * x356)) * (rproject (tproject1 (tproject2 h354)) 0 * rproject (tproject2 (tproject2 (tproject1 h354))) 0) in tpair ([recip x356 * rproject (tproject2 (tproject2 (tproject1 h354))) 0 + rproject (tproject1 (tproject1 h354)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h354)))) 0)) * (x355 * x357 + x355 * x357)]))) in tpair ([rproject (tproject1 h358) 0 + rproject (tproject1 (tproject2 (tproject1 h354))) 0], tproject2 h358)) (tproject1 (tproject2 h233)) (tpair (tproject1 (tproject2 (tproject2 h233)), tpair (tproject1 (tproject2 (tproject2 h236)), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h233)))) 0)]))))), tpair (tproject1 (tproject2 (tproject2 h233)), tpair (tproject1 (tproject2 (tproject2 h236)), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h233)))) 0)]))))) ; h251 = dmapAccumRDer (SNat @2) (\\h359 -> let x360 = cos (rproject (tproject2 (tproject2 (tproject2 h359))) 0) in tpair ([rproject (tproject1 h359) 0 + rproject (tproject1 (tproject1 (tproject2 h359))) 0], [recip (x360 * x360) * rproject (tproject1 h359) 0])) (\\h361 -> let x365 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h361)))) 0) ; x366 = x365 * x365 ; x369 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h361)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h361)))) 0)) in tpair ([rproject (tproject1 (tproject1 h361)) 0 + rproject (tproject1 (tproject1 (tproject2 (tproject1 h361)))) 0], [((x369 * x365 + x369 * x365) * negate (recip (x366 * x366))) * rproject (tproject1 (tproject2 h361)) 0 + rproject (tproject1 (tproject1 h361)) 0 * recip x366])) (\\h373 -> let x376 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h373)))) 0) ; x377 = x376 * x376 ; x380 = negate (recip (x377 * x377)) * (rproject (tproject1 (tproject2 h373)) 0 * rproject (tproject2 (tproject1 h373)) 0) in tpair ([rproject (tproject1 (tproject1 h373)) 0 + recip x377 * rproject (tproject2 (tproject1 h373)) 0], tpair (tpair ([rproject (tproject1 (tproject1 h373)) 0], []), tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h373)))) 0)) * (x376 * x380 + x376 * x380)])))) [0.0] (tpair (tpair (tproject1 (tproject2 (tproject2 h245)), []), tpair (tproject1 (tproject2 h236), [rreplicate 2 (rproject (tproject1 (tproject2 (tproject2 (tproject2 h233)))) 0)]))) in tpair ([rproject (tproject1 h245) 0], tpair ([], tpair ([rsum (rproject (tproject2 h251) 0) + rsum (rproject (tproject2 (tproject2 (tproject2 h245))) 0)], [rproject (tproject1 h251) 0])))) [1.0] (tpair ([], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h381 -> let h383 = dmapAccumLDer (SNat @2) (\\h384 -> tpair ([rproject (tproject1 h384) 0 + tan (rproject (tproject2 h384) 0)], [])) (\\h386 -> let x393 = cos (rproject (tproject2 (tproject2 h386)) 0) in tpair ([rproject (tproject1 (tproject1 h386)) 0 + rproject (tproject2 (tproject1 h386)) 0 * recip (x393 * x393)], [])) (\\h394 -> let x399 = cos (rproject (tproject2 (tproject2 h394)) 0) in tpair ([rproject (tproject1 (tproject1 h394)) 0], [recip (x399 * x399) * rproject (tproject1 (tproject1 h394)) 0])) (tproject2 h381) [rreplicate 2 (rproject (tproject1 h381) 0)] in tpair (tproject1 h383, tpair (tproject1 h381, tproject2 h383))) (\\h400 -> let h407 = dmapAccumLDer (SNat @2) (\\h408 -> let x417 = cos (rproject (tproject2 (tproject2 (tproject2 h408))) 0) in tpair ([rproject (tproject1 h408) 0 + rproject (tproject1 (tproject2 h408)) 0 * recip (x417 * x417)], [])) (\\h418 -> let x431 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h418)))) 0) ; x432 = x431 * x431 ; x433 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h418)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h418)))) 0)) in tpair ([rproject (tproject1 (tproject1 h418)) 0 + rproject (tproject1 (tproject2 (tproject1 h418))) 0 * recip x432 + ((x433 * x431 + x433 * x431) * negate (recip (x432 * x432))) * rproject (tproject1 (tproject2 (tproject2 h418))) 0], [])) (\\h434 -> let x443 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h434)))) 0) ; x444 = x443 * x443 ; x445 = negate (recip (x444 * x444)) * (rproject (tproject1 (tproject2 (tproject2 h434))) 0 * rproject (tproject1 (tproject1 h434)) 0) in tpair ([rproject (tproject1 (tproject1 h434)) 0], tpair ([recip x444 * rproject (tproject1 (tproject1 h434)) 0], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h434)))) 0)) * (x443 * x445 + x443 * x445)])))) [rproject (tproject2 (tproject1 h400)) 0] (tpair ([rreplicate 2 (rproject (tproject1 (tproject1 h400)) 0)], tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h446 -> tpair ([rproject (tproject1 h446) 0 + tan (rproject (tproject2 h446) 0)], tpair (tproject1 h446, []))) (\\h453 -> let x460 = cos (rproject (tproject2 (tproject2 h453)) 0) in tpair ([rproject (tproject1 (tproject1 h453)) 0 + rproject (tproject2 (tproject1 h453)) 0 * recip (x460 * x460)], tpair (tproject1 (tproject1 h453), []))) (\\h461 -> let x471 = cos (rproject (tproject2 (tproject2 h461)) 0) in tpair ([rproject (tproject1 (tproject1 h461)) 0 + rproject (tproject1 (tproject2 (tproject1 h461))) 0], [recip (x471 * x471) * rproject (tproject1 (tproject1 h461)) 0])) (tproject2 (tproject2 h400)) [rreplicate 2 (rproject (tproject1 (tproject2 h400)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h400)) 0)]))) in tpair (tproject1 h407, tpair (tproject1 (tproject1 h400), tproject2 h407))) (\\h472 -> let h473 = dmapAccumRDer (SNat @2) (\\h477 -> let x478 = cos (rproject (tproject2 (tproject2 (tproject2 h477))) 0) in tpair ([rproject (tproject1 h477) 0], [recip (x478 * x478) * rproject (tproject1 h477) 0])) (\\h479 -> let x480 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h479)))) 0) ; x481 = x480 * x480 ; x482 = rproject (tproject2 (tproject2 (tproject2 (tproject1 h479)))) 0 * negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h479)))) 0)) in tpair ([rproject (tproject1 (tproject1 h479)) 0], [((x482 * x480 + x482 * x480) * negate (recip (x481 * x481))) * rproject (tproject1 (tproject2 h479)) 0 + rproject (tproject1 (tproject1 h479)) 0 * recip x481])) (\\h483 -> let x484 = cos (rproject (tproject2 (tproject2 (tproject2 (tproject2 h483)))) 0) ; x485 = x484 * x484 ; x486 = negate (recip (x485 * x485)) * (rproject (tproject1 (tproject2 h483)) 0 * rproject (tproject2 (tproject1 h483)) 0) in tpair ([recip x485 * rproject (tproject2 (tproject1 h483)) 0 + rproject (tproject1 (tproject1 h483)) 0], tpair ([], tpair ([0], [negate (sin (rproject (tproject2 (tproject2 (tproject2 (tproject2 h483)))) 0)) * (x484 * x486 + x484 * x486)])))) (tproject1 (tproject1 h472)) (tpair (tproject2 (tproject2 (tproject1 h472)), tpair (tproject1 (tproject2 (dmapAccumLDer (SNat @2) (\\h487 -> tpair ([rproject (tproject1 h487) 0 + tan (rproject (tproject2 h487) 0)], tpair (tproject1 h487, []))) (\\h488 -> let x489 = cos (rproject (tproject2 (tproject2 h488)) 0) in tpair ([rproject (tproject1 (tproject1 h488)) 0 + rproject (tproject2 (tproject1 h488)) 0 * recip (x489 * x489)], tpair (tproject1 (tproject1 h488), []))) (\\h490 -> let x491 = cos (rproject (tproject2 (tproject2 h490)) 0) in tpair ([rproject (tproject1 (tproject1 h490)) 0 + rproject (tproject1 (tproject2 (tproject1 h490))) 0], [recip (x491 * x491) * rproject (tproject1 (tproject1 h490)) 0])) (tproject2 (tproject2 h472)) [rreplicate 2 (rproject (tproject1 (tproject2 h472)) 0)])), [rreplicate 2 (rproject (tproject1 (tproject2 h472)) 0)]))) in tpair ([rsum (rproject (tproject2 h473) 0) + rproject (tproject1 (tproject2 (tproject1 h472))) 0], [rproject (tproject1 h473) 0])) [1.1] [rreplicate 2 1.1])), [rreplicate 2 1.1]))) in [rsum (rproject (tproject2 h12) 0) + rproject (tproject1 h12) 0]"

testSin0MapAccumNestedR3LengthPP :: Assertion
testSin0MapAccumNestedR3LengthPP = do
  resetVarCounter
  let sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
      f z = rfromD $ (V.! 0) $ dunHVector
            $ productToVectorOf $ dmapAccumL (Proxy @f) (SNat @2) shs1 she shs1
                   (\x a ->
               dmapAccumL Proxy (SNat @2) shs1 she shs1
                     (\x2 a2 ->
                 dmapAccumL Proxy (SNat @2) shs1 she shs1
                       (\x3 a3 ->
                   dmapAccumL Proxy (SNat @2) shs1 she shs1
                         (\x4 a4 -> let y = rfromD @Double @0 $ dunHVector x4 V.! 0
                                        w = rfromD @Double @0 $ dunHVector a4 V.! 0
                                    in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ y + tan w)
                                                    (dmkHVector V.empty))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      g :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      g x = rrev (\v -> f (rfromD $ dunHVector v V.! 0))
                 (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
                 (dmkHVector x)
  length
    (printAstSimple
       IM.empty
       (simplifyInline
        $ g @(AstTensor AstMethodLet PrimalSpan) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1))))
    @?= 5834585

testSin0MapAccumNestedR4 :: Assertion
testSin0MapAccumNestedR4 = do
 assertEqualUpToEpsilon' 1e-10
  (rscalar 1.0410225027528066 :: RepN (TKR Double 0))
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                           (\x5 a5 -> let y = rfromD @Double @0 $ dunHVector x5 V.! 0
                                          w = rfromD @Double @0 $ dunHVector a5 V.! 0
                                      in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR5 :: Assertion
testSin0MapAccumNestedR5 = do
 assertEqualUpToEpsilon' 1e-10
  (rscalar 6.308416949436515e-16 :: RepN (TKR Double 0))
  (rev'
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector x6 V.! 0
                                            w = rfromD @Double @0 $ dunHVector a6 V.! 0
                                        in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * (y + tan w))
                                                    (dmkHVector V.empty))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 1.1))

testSin0MapAccumNestedR5r :: Assertion
testSin0MapAccumNestedR5r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.0837278549794862 :: RepN (TKR Double 0))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                             (\x6 a6 -> let y = rfromD @Double @0 $ dunHVector x6 V.! 0
                                            w = rfromD @Double @0 $ dunHVector a6 V.! 0
                                        in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10r :: Assertion
testSin0MapAccumNestedR10r = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781 :: RepN (TKR Double 0))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001))

testSin0MapAccumNestedR10f :: Assertion
testSin0MapAccumNestedR10f = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.379370673816781e-4 :: RepN (TKR Double 0))
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10fN :: Assertion
testSin0MapAccumNestedR10fN = do
 assertEqualUpToEpsilon 1e-10
  (tpair (srepl 1.379370673816781e-4 :: RepN (TKS Float '[1]))
         (rscalar 1.379370673816781e-4 :: RepN (TKR Double 0)))
  (fwd
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      g :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
      f :: forall f. ADReady f => f (TKR Double 0)
        -> f (TKProduct (TKS Float '[1]) (TKR Double 0))
      f x = tpair (sfromList [scast $ sfromR $ g x]) (g x + rscalar 0.2)
    in f) (rscalar 0.0001) (rscalar 0.0001))

testSin0MapAccumNestedR10rf :: Assertion
testSin0MapAccumNestedR10rf = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: RepN (TKR Double 0))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rfwd1 f) (rscalar 0.0001))

testSin0MapAccumNestedR10rr :: Assertion
testSin0MapAccumNestedR10rr = do
 assertEqualUpToEpsilon 1e-10
  (rscalar 1.2264611684496617e-2 :: RepN (TKR Double 0))
  (rev
   (let
      sh1 = voidFromSh @Double ZSR
      shs1 = FTKUntyped $ V.singleton sh1
      she = FTKUntyped V.empty
      f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
                                          let y = rfromD @Double @0 $ dunHVector x11 V.! 0
                                              w = rfromD @Double @0 $ dunHVector a11 V.! 0
                                          in tpair (dmkHVector $ V.singleton
                                                     $ DynamicRanked
                                                     $ rscalar 0.01 * y + tan w)
                                                    (dmkHVector V.empty))
                                       a10 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x10))
                                     a9 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x9))
                                   a8 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x8))
                                 a7 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x7))
                               a6 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x6))
                             a5 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x5))
                           a4 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x4))
                         a3 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x3))
                       a2 (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x2))
                     a (dmkHVector $ replicate1HVector (SNat @2) $ dunHVector x))
                   (dmkHVector $ V.singleton $ DynamicRanked z)
                   (dmkHVector $ V.singleton $ DynamicRanked $ rreplicate 2 z)
    in rrev1 f) (rscalar 0.0001))

productToVectorOf
  :: ADReady f
  => f (TKProduct TKUntyped TKUntyped)
  -> f TKUntyped
productToVectorOf p = tlet @_ @_ @TKUntyped (tproject1 p) $ \p1 ->
                          tlet (tproject2 p) $ \p2 ->
                            dmkHVector $ dunHVector p1 V.++ dunHVector p2

testSin0FoldNestedS1FwdFwd0 :: Assertion
testSin0FoldNestedS1FwdFwd0 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 -> srepl 0.7 * x2 * a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfromS . sfwd1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1FwdFwd :: Assertion
testSin0FoldNestedS1FwdFwd = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * sfwd1 (sfwd1 (\b2 -> srepl 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rfwd1 $ rfromS . sfwd1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS1RevRev :: Assertion
testSin0FoldNestedS1RevRev = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
               f a0 = sfold (\x a ->
                        sfold (\x2 a2 ->
                                 x2 * srev1 (srev1 (\b2 -> srepl 0.7 * b2)) a2)
                              a (sreplicate @_ @7 x))
                            a0 (sreplicate @_ @3 a0)
           in rrev1 $ rfromS . srev1 f . sfromR) (rscalar 1.1))

testSin0FoldNestedS2 :: Assertion
testSin0FoldNestedS2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
    (rscalar 7.320500000000004e-4 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
    (rscalar 1.2400927000000009e-5 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
    (rscalar 0.22000000000000003 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
  let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
  let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[])
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
    (rscalar  (-0.20775612781643243) :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKS Double '[]) -> f (TKS Double '[3])
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
           in rfromS . f . sfromR) (rscalar 1.1))

testSin0FoldNestedR1 :: Assertion
testSin0FoldNestedR1 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 2.0504979297616553e-43 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 -> rscalar 0.7 * x2 * a2)
                              a (rreplicate 7 x))
                            a0 (rreplicate 3 a0)
           in f) (rscalar 1.1))

testSin0FoldNestedR1RevFwd :: Assertion
testSin0FoldNestedR1RevFwd = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f a0 = rfold (\x a ->
                        rfold (\x2 a2 ->
                                 x2 * rfwd1 (rrev1 (\b2 -> rscalar 0.7 * b2)) a2)
                              a (rreplicate 4 x))
                            a0 (rreplicate 2 a0)
           in rrev1 $ rfwd1 f) (rscalar 1.1))

testSin0FoldNestedR2 :: Assertion
testSin0FoldNestedR2 = do
  assertEqualUpToEpsilon' 1e-10
    (rscalar 3.175389686661287e-207 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 3.175389686661287e-207 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 7.320500000000004e-4 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 1.2400927000000009e-5 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 0.22000000000000003 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 1.0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 1.0 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar (-0.20775612781643243) :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 1)
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
    (rscalar 2.877421010384167e-5 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
    (rscalar 7.667553331540788e-3 :: RepN (TKR Double 0))
    (rev' (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
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
          (let f :: forall f. ADReady f => f (TKR Double 0) -> f (TKR Double 0)
               f a0 = rfold (\x a -> tlet (x + a) $ \xpa ->
                          rfold (\x3 a3 -> rscalar 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) xpa
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) xpa
                                       (rreplicate 2 xpa)))
                            a0 (rreplicate 2 a0)
           in f) (rscalar 1.1)
  length (printAstSimple IM.empty (simplifyInline a1))
    @?= 43113

testSin0revhV :: Assertion
testSin0revhV = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
  assertEqualUpToEpsilon 1e-10
    (dmkHVector $ V.singleton $ DynamicRanked @Double @0 (rscalar 0.4535961214255773))
    (f @RepN (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

testSin0revhVPP :: Assertion
testSin0revhVPP = do
  resetVarCounter
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
  printAstSimple IM.empty (f @(AstTensor AstMethodLet PrimalSpan)
                                    (V.singleton
                                     $ DynamicRanked @Double @0 (rscalar 1.1)))
    @?= "dmkHVector (fromList [DynamicRanked (cos 1.1 * 1.0)])"

testSin0revhV2 :: Assertion
testSin0revhV2 = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ dunHVector v V.! 0))
             (FTKUntyped (V.singleton (voidFromSh @Double ZSR)))
             (dmkHVector x)
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (rscalar (-0.8912073600614354)))
    (crev (h @RepN) (V.singleton $ DynamicRanked @Double @0 (rscalar 1.1)))

testSin0revhV3 :: Assertion
testSin0revhV3 = do
  let f :: forall g. ADReady g
        => HVector g -> g TKUntyped
      f x =
        srev @g @_ @Double @'[] (\v -> sin (sfromD $ dunHVector v V.! 0))
             (FTKUntyped $ V.singleton (voidFromShS @Double @'[]))
             (dmkHVector x)
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[] (sscalar $ -0.8912073600614354))
    (crev (h @RepN) (V.singleton $ DynamicShaped @Double @'[] (srepl 1.1)))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (BaseTensor g)
        => HVector g -> g TKUntyped
      f x =
        rrevDt @g @_ @Double @1 (rscanZip const doms 5 . dunHVector)
               (FTKUntyped doms3) (dmkHVector x) (ringestData [4] [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0])
    (crev (h @RepN)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (BaseTensor g)
        => HVector g -> g TKUntyped
      f x =
        srevDt @g @_ @Double @'[4] (sscanZip const doms (srepl 5) . dunHVector)
               (FTKUntyped doms3) (dmkHVector x) (ingestData [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0])
    (crev (h @RepN)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let doms = V.singleton (voidFromSh @Double ZSR)
      doms3 = V.singleton (voidFromSh @Double (3 :$: ZSR))
      f :: forall g. (BaseTensor g)
        => HVector g -> g TKUntyped
      f x =
        rrevDt @g @_ @Double @1
               (\v -> rscanZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 (dunHVector v))
                (FTKUntyped doms3) (dmkHVector x) (ringestData [4] [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ ringestData [3] [4.0,6.0,8.0])
    (crev (h @RepN)
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f :: forall g. (BaseTensor g)
        => HVector g -> g TKUntyped
      f x =
        srevDt @g @_ @Double @'[4]
               (\v -> sscanZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms (srepl 5) (dunHVector v))
               (FTKUntyped doms3) (dmkHVector x) (ingestData [1, 2, 3, 4])
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [4.0,6.0,8.0])
    (crev (h @RepN)
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 (sscalar 1.1)))

testSin0revhV8 :: Assertion
testSin0revhV8 = do
  let f :: forall g. BaseTensor g
        => HVector g -> g TKUntyped
      f = dmkHVector
      h :: forall g.
           (ADReady g, ShareTensor g, ShareTensor (PrimalOf g))
        => HVector (ADVal g)
        -> ADVal g TKUntyped
      h = f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ ingestData [1, 1, 1])
    (crev @_ @TKUntyped
          (h @RepN)
          (V.singleton $ DynamicShaped @Double @'[3]
           $ sreplicate @RepN @3 (sscalar 1.1)))

fFoldZipR
  :: forall n r target.
     (KnownNat n, GoodScalar r, ADReady target)
  => VoidHVector
  -> target (TKR r (1 + n))
  -> HVector target
  -> (forall f. ADReady f
      => f (TKR r n) -> f (TKR r n) -> HVector f
      -> f TKUntyped)
  -> IShR n
  -> target (TKR r n)
  -> target TKUntyped
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
                 => HVector f -> (f (TKR r n), HVector f)
      domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
      domsTo3 :: ADReady f
              => HVector f -> (f (TKR r n), f (TKR r n), HVector f)
      domsTo3 doms = ( rfromD $ doms V.! 0
                     , rfromD $ doms V.! 1
                     , V.drop 2 doms )
      lp = rreverse $ rslice 0 width p
      las :: HVector target
      las = mapHVectorRanked11 rreverse as
      crsr :: target (TKR r (1 + n))
      crsr =
        rscanZip
          (\cr doms ->
              let (x, a) = domsToPair doms
              in tlet @_ @TKUntyped ((rf cr x a)) $ \ !rfRes ->
                   fst (domsToPair (dunHVector (rfRes))))
          domsF
          cShared
          (V.cons (DynamicRanked lp) las)
      crs = rreverse crsr
      rg :: target (TKR r (1 + n)) -> target (TKR r (1 + n))
         -> HVector target
         -> target TKUntyped
      rg cr2 x2 a2 = withSNat width $ \k ->
        dzipWith1 k
                  (\doms ->
                     let (cr, x, a) = domsTo3 doms
                     in tlet @_ @TKUntyped @TKUntyped
                               ((rf cr x a))
                               $ \ !rfRes ->
                                   dmkHVector $ snd $ domsToPair (dunHVector (rfRes)))
                  (V.cons (DynamicRanked cr2)
                   $ V.cons (DynamicRanked x2) a2)
      cas = rg (rslice 1 width crs)
               (rslice 0 width p)
               as
  in cas

fFoldZipRX :: forall target. ADReady target
  => HVector target
  -> target TKUntyped
fFoldZipRX as =
  let f :: forall f. ADReady f => f (TKR Double 0) -> f TKUntyped -> f (TKR Double 0)
      f _t v = sin (rfromD (dunHVector v V.! 1)) * rfromD (dunHVector v V.! 1)
      doms = V.fromList [ voidFromSh @Double ZSR
                        , voidFromSh @Double ZSR ]
      p :: target (TKR Double 1)
      p = rscanZip (\x y -> f x (dmkHVector y)) doms 7 as
      rf :: forall f. ADReady f
         => f (TKR Double 0) -> f (TKR Double 0) -> HVector f -> f TKUntyped
      rf _x _y = rrev @f (f 42) (FTKUntyped doms) . dmkHVector  -- not exactly the rev of f
  in fFoldZipR doms p as rf ZSR 26

testSin0revhFoldZipR :: Assertion
testSin0revhFoldZipR = do
  let h :: target ~ RepN
        => HVector (ADVal target)
        -> ADVal target TKUntyped
      h = fFoldZipRX @(ADVal RepN)
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (rscalar (-7.313585321642452e-2)) ])
    (crev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)
                        , DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1) ]))

{-
testSin0revhFoldZip4R :: Assertion
testSin0revhFoldZip4R = do
  let g :: ADReady target
        => HVector target
        -> HVectorPseudoTensor target Float '()
      g = HVectorPseudoTensor . fFoldZipRX
      h :: HVector (AstGeneric AstMethodLet FullSpan)
        -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
      h = g @(AstTensor AstMethodLet FullSpan) . rankedHVector
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [rscalar 0, rscalar 0, rscalar 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (rscalar (-7.313585321642452e-2)) ])
    (rev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1)
                       , DynamicRanked @Double @1 $ rreplicate 3 (rscalar 1.1) ]))
-}

fFoldS
  :: forall m k rm shm r sh target.
     ( KnownNat k, GoodScalar rm, KnownShS shm, GoodScalar r, KnownShS sh
     , ADReady target, KnownNat m, Rank shm ~ m)
  => target (TKS r (1 + k ': sh))
  -> target (TKS rm (k ': shm))
  -> (forall f. ADReady f
      => f (TKS r sh) -> f (TKS r sh) -> f (TKS rm shm) -> f TKUntyped)
  -> target (TKS r sh)
  -> target (TKS rm (k ': shm))
fFoldS p as rf cShared =
  let domsF = V.fromList [voidFromShS @r @sh, voidFromShS @rm @shm]
      domsToPair :: ADReady f
                 => HVector f -> (f (TKS r sh), f (TKS rm shm))
      domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
      crsr :: target (TKS r (1 + k ': sh))
      crsr =
        sscanZip (\cr doms ->
                    let (x, a) = domsToPair doms
                    in tlet @_ @TKUntyped (
                         (rf cr x a)) $ \ !rfRes ->
                           fst (domsToPair (dunHVector (rfRes))))
               domsF
               cShared
               (V.fromList
                  [ DynamicShaped $ sreverse
                    $ sslice @_ @_ @_ @_ @1
                             (Proxy @0) (Proxy @k) p
                  , DynamicRanked $ rfromS $ sreverse as ])
      crs = sreverse crsr
      rg :: target (TKS r (k ': sh)) -> target (TKS r (k ': sh))
         -> target (TKS rm (k ': shm))
         -> target (TKS rm (k ': shm))
      rg = szipWith31 (\cr x a ->
                         tlet @_ @TKUntyped ((rf cr x a)) $ \ !rfRes ->
                           snd $ domsToPair (dunHVector (rfRes)))
      cas = rg (sslice @_ @_ @_ @_ @0
                       (Proxy @1) (Proxy @k) crs)
               (sslice @_ @_ @_ @_ @1
                       (Proxy @0) (Proxy @k) p)
               as
  in cas

fFoldSX
  :: forall target. ADReady target
  => target (TKS Double '[3]) -> target (TKS Double '[3])
fFoldSX as =
  let f :: forall f. ADReady f
        => f (TKS Double '[]) -> f (TKS Double '[]) -> f (TKS Double '[])
      f _t v = sin v * v
      doms = V.fromList [ voidFromShS @Double @'[]
                        , voidFromShS @Double @'[] ]
      p :: target (TKS Double '[4])
      p = sscan f (srepl 7) as
      rf :: forall f. ADReady f
         => f (TKS Double '[]) -> f (TKS Double '[]) -> f (TKS Double '[])
         -> f TKUntyped
      rf _x _y z = srev @f (\v -> f (sscalar 42) (sfromD (dunHVector v V.! 1)))
                        (FTKUntyped doms)
                        (dmkHVector $ V.fromList [ DynamicShaped @Double @'[] z
                                    , DynamicShaped @Double @'[] z ])
                     -- not exactly the rev of f
  in fFoldS @0 p as rf (srepl 26)

testSin0revhFoldS :: Assertion
testSin0revhFoldS = do
  assertEqualUpToEpsilon 1e-10
    (sreplicate @_ @3 (sscalar $ -7.313585321642452e-2))
    (rev (fFoldSX @(AstTensor AstMethodLet FullSpan))
         (sreplicate @_ @3 (sscalar 1.1)))

testSin0revhFold2S :: Assertion
testSin0revhFold2S = do
  assertEqualUpToEpsilon' 1e-10
    (rreplicate 3 (rscalar (-7.313585321642452e-2)))
    (rev' (rfromS . fFoldSX . sfromR)
          (rreplicate 3 (rscalar 1.1)))

testSin0revhFold3S :: Assertion
testSin0revhFold3S = do
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicShaped @Double @'[3] $ ingestData [0, 0, 0]
                , DynamicShaped @Double @'[3]
                  $ sreplicate @_ @3 (sscalar (-7.313585321642452e-2)) ])
    (crev (\(asD :: HVector (ADVal RepN)) ->
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
