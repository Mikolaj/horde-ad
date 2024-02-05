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
import HordeAd.Core.DualClass
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
  , testCase "4Sin0Rfwd3" testSin0Rfwd3
  , testCase "4Sin0Rfwd4" testSin0Rfwd4
  , testCase "4Sin0RfwdPP4" testSin0RfwdPP4
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
  , testCase "4Sin0Scan1RevPP" testSin0Scan1RevPP
  , testCase "4Sin0Scan1RevPPForComparison" testSin0Scan1RevPPForComparison
  , testCase "4Sin0ScanFwdPP" testSin0ScanFwdPP
  , testCase "4Sin0Scan1Rev2PP" testSin0Scan1Rev2PP
  , testCase "4Sin0Scan1Rev2PPForComparison" testSin0Scan1Rev2PPForComparison
  , testCase "4Sin0ScanFwd2PP" testSin0ScanFwd2PP
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
  , testCase "4Sin0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4Sin0FoldNestedS1" testSin0FoldNestedS1
  , testCase "4Sin0FoldNestedS1PP" testSin0FoldNestedS1PP
  , testCase "4Sin0FoldNestedR1PP" testSin0FoldNestedR1PP
  , testCase "4Sin0FoldNestedR1SimpPP" testSin0FoldNestedR1SimpPP
  , testCase "4Sin0FoldNestedR1SimpNestedPP" testSin0FoldNestedR1SimpNestedPP
  , testCase "4Sin0FoldNestedR1SimpSimpPP" testSin0FoldNestedR1SimpSimpPP
  , testCase "4Sin0FoldNestedR0LengthPP" testSin0FoldNestedR0LengthPP
  , testCase "4Sin0FoldNestedR1LengthPP" testSin0FoldNestedR1LengthPP
  , testCase "4Sin0FoldNestedR2LengthPP" testSin0FoldNestedR2LengthPP
  , testCase "4Sin0FoldNestedR3LengthPP" testSin0FoldNestedR3LengthPP
  , testCase "4Sin0FoldNestedR4LengthPP" testSin0FoldNestedR4LengthPP
--  , testCase "4Sin0FoldNestedR5LengthPP" testSin0FoldNestedR5LengthPP
  , testCase "4Sin0FoldNestedS1FwdFwd" testSin0FoldNestedS1FwdFwd
  , testCase "4Sin0FoldNestedS1RevRev" testSin0FoldNestedS1RevRev
  , testCase "4Sin0FoldNestedS2" testSin0FoldNestedS2
  , testCase "4Sin0FoldNestedS3" testSin0FoldNestedS3
--  , testCase "4Sin0FoldNestedS4" testSin0FoldNestedS4
  , testCase "4Sin0FoldNestedS5rev" testSin0FoldNestedS5rev
  , testCase "4Sin0FoldNestedS5fwd" testSin0FoldNestedS5fwd
  , testCase "4Sin0FoldNestedSi" testSin0FoldNestedSi
  , testCase "4Sin0FoldNestedR1" testSin0FoldNestedR1
  , testCase "4Sin0FoldNestedR1RevFwd" testSin0FoldNestedR1RevFwd
  , testCase "4Sin0FoldNestedR2" testSin0FoldNestedR2
  , testCase "4Sin0FoldNestedR3" testSin0FoldNestedR3
--  , testCase "4Sin0FoldNestedR4" testSin0FoldNestedR4
--  , testCase "4Sin0FoldNestedR41" testSin0FoldNestedR41
--  , testCase "4Sin0FoldNestedR40" testSin0FoldNestedR40
--  , testCase "4Sin0FoldNestedR400" testSin0FoldNestedR400
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
--  , testCase "4Sin0revhFoldZip4R" testSin0revhFoldZip4R
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
                     $ [ DynamicRanked $ rconst @g $ OR.scalar x
                       , DynamicRanked $ rconst @g $ OR.scalar y
                       , DynamicRanked $ rconst @g $ OR.scalar z ])
  in ( rletHVectorIn shapes domsOf (\v -> rfromD $ v V.! 0)
     , rletHVectorIn shapes domsOf (\v -> rfromD $ v V.! 1)
     , rletHVectorIn shapes domsOf (\v -> rfromD $ v V.! 2) )

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
    @?= "let x16 = sin (rconst 2.2) ; x17 = rconst 1.1 * x16 ; x18 = recip (rconst 3.3 * rconst 3.3 + x17 * x17) ; x19 = sin (rconst 2.2) ; x20 = rconst 1.1 * x19 ; x21 = rreshape [] (rreplicate 1 (rconst 1.0)) ; x22 = rconst 3.3 * x21 ; x23 = negate (rconst 3.3 * x18) * x21 in x16 * x23 + x19 * x22"

_testFooRrevPP2 :: Assertion
_testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rlet (sin (rconst 2.2)) (\\x27 -> rlet (rconst 1.1 * x27) (\\x28 -> rlet (recip (rconst 3.3 * rconst 3.3 + x28 * x28)) (\\x29 -> rlet (sin (rconst 2.2)) (\\x30 -> rlet (rconst 1.1 * x30) (\\x31 -> rlet (rreshape [] (rreplicate 1 (rconst 1.0))) (\\x32 -> rlet (rconst 3.3 * x32) (\\x33 -> rlet (negate (rconst 3.3 * x29) * x32) (\\x34 -> x27 * x34 + x30 * x33))))))))"

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
    @?= "cos (rconst 1.1) * rreshape [] (rreplicate 1 (rconst 1.0))"

testSin0RrevPP2 :: Assertion
testSin0RrevPP2 = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstSimple IM.empty a1
    @?= "cos (rconst 1.1) * rreshape [] (rreplicate 1 (rconst 1.0))"

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
    @?= "cos (cos (rconst 1.1) * rconst 1.0) * rconst 1.0"

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
    @?= "negate (sin (rconst 1.1)) * (rconst 1.0 * rconst 1.0)"

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
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin 1.1
  printAstPretty IM.empty a1
    @?= "rconst 1.1 * cos (rconst 1.1)"

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
  let a1 = (rfwd1 sin . rfwd1 @(AstRanked FullSpan) @Double @0 @0 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "(rconst 1.1 * cos (rconst 1.1)) * cos (rconst 1.1 * cos (rconst 1.1))"

testSin0Rfwd5 :: Assertion
testSin0Rfwd5 = do
  assertEqualUpToEpsilon 1e-10
    (-0.5794051721062019)
    (rfwd1 @(Flip OR.Array) @Double @0 @0 (rfwd1 sin) 1.1)

testSin0RfwdPP5 :: Assertion
testSin0RfwdPP5 = do
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @0 (rfwd1 sin) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rconst 1.1 * cos (rconst 1.1) + (rconst 1.1 * negate (sin (rconst 1.1))) * rconst 1.1"

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
  let a1 = srev1 @(AstShaped FullSpan) @Double @'[] @'[] (srev1 sin) 1.1
  printAstPrettyS IM.empty (simplifyAst6S a1)
    @?= "negate (sin (sconst @[] 1.1)) * sconst @[] 1.0"

testSin0Fold0 :: Assertion
testSin0Fold0 = do
  assertEqualUpToEpsilon' 1e-10
    (1.0 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f x0 = rfold (\x _a -> sin x)
                            x0 (rzero @f @Double (0 :$ ZS))
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
    (rev' (\a0 -> rfold (\x _a -> rtr $ rreplicate 5
                                  $ (rsum (rtr x)))
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
                        (\x _a -> str $ sreplicate @_ @5
                                  $ (ssum (str x)))
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
    7.76565749259337e-2
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
    @?= "let m105 = sscanDer f df rf (sreplicate (sconstant (rconst 1.1))) (sreplicate (sconstant (rconst 1.1))) ; m122 = sreverse (sscanZipDer f df rf (rreplicate 5 (rconst 1.0)) [sreverse (sslice m105), sreverse (sreplicate (sconstant (rconst 1.1)))]) in ssum (m122 !$ [0]) + ssum (let v124 = ssum (stranspose (stranspose (sreplicate (sgather (sreplicate (sconstant (rconst 1.1))) (\\[i123] -> [i123]))))) ; m126 = stranspose (sreplicate (sin (sgather v124 (\\[i125] -> [i125])))) ; m129 = recip (sreplicate (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) + sreplicate (sreplicate (sconstant (rconst 1.1)) * sreplicate (sconstant (rconst 1.1))) + sgather m126 (\\[i127] -> [i127]) * sgather m126 (\\[i128] -> [i128]) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0]) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0])) ; m130 = sreplicate (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) in sreplicate (sconst @[] 0.0) + ssum (stranspose ((sgather m126 (\\[i134] -> [i134]) * sgather m129 (\\[i135] -> [i135])) * sgather m122 (\\[i136] -> [1 + i136]))) + ssum (stranspose (stranspose (sreplicate (cos (sgather v124 (\\[i131] -> [i131])) * ssum (stranspose (negate (sreplicate (sreplicate (sconstant (rconst 1.1))) * sgather m129 (\\[i132] -> [i132])) * sgather m122 (\\[i133] -> [1 + i133]))))))) + sconst @[1] (fromList @[1] [0.0]) + sconst @[1] (fromList @[1] [0.0]))"

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
                            x0 (rzero @f @Double (0 :$ ZS))
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
    (rev' (\a0 -> rscan (\x _a -> rtr $ rreplicate 5
                                  $ (rsum (rtr x)))
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

testSin0Scan1RevPP :: Assertion
testSin0Scan1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v62 = rconst (fromList [2] [42.0,42.0]) in rscanZipDer f df rf (rconst 0.0) [rconstant (rreplicate 2 (rconst 1.0)), rreverse (rslice 0 2 (rscanDer f df rf (rconst 1.1) v62)), rreverse v62] ! [2] + rconst 1.0"

testSin0Scan1RevPPForComparison :: Assertion
testSin0Scan1RevPPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0), sin x0, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "cos (rconst 1.1) * (cos (sin (rconst 1.1)) * rconst 1.0) + cos (rconst 1.1) * rconst 1.0 + rconst 1.0"

testSin0ScanFwdPP :: Assertion
testSin0ScanFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x _a -> sin x) x0
                           (rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v49 = rconst (fromList [2] [42.0,42.0]) in rscanZipDer f df rf (rconst 1.1) [rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDer f df rf (rconst 1.1) v49), v49]"

testSin0Scan1Rev2PP :: Assertion
testSin0Scan1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v64 = rconst (fromList [2] [5.0,7.0]) in rscanZipDer f df rf (rconst 0.0) [rconstant (rreplicate 2 (rconst 1.0)), rreverse (rslice 0 2 (rscanDer f df rf (rconst 1.1) v64)), rreverse v64] ! [2] + rconst 1.0"

testSin0Scan1Rev2PPForComparison :: Assertion
testSin0Scan1Rev2PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - 5) - 7, sin x0 - 5, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "cos (rconst 1.1) * (cos (sin (rconst 1.1) - rconst 5.0) * rconst 1.0) + cos (rconst 1.1) * rconst 1.0 + rconst 1.0"

testSin0ScanFwd2PP :: Assertion
testSin0ScanFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstSimple IM.empty (simplifyAst6 a1)
    @?= "rlet (rconst (fromList [2] [5.0,7.0])) (\\v58 -> rscanZipDer (\\x70 [x71 @Natural @Double @[], x72 @Natural @Double @[], x73 @Natural @Double @[]] -> x70 * cos x72 + x71 * rconst -1.0) (\\x75 [x76 @Natural @Double @[], x77 @Natural @Double @[], x78 @Natural @Double @[]] x79 [x80 @Natural @Double @[], x81 @Natural @Double @[], x82 @Natural @Double @[]] -> x76 * rconst -1.0 + x75 * cos x81 + (x77 * negate (sin x81)) * x79) (\\x89 x90 [x91 @Natural @Double @[], x92 @Natural @Double @[], x93 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked (cos x92 * x89), DynamicRanked (rconst -1.0 * x89), DynamicRanked (negate (sin x92) * (x90 * x89)), DynamicRankedDummy])) (rconst 1.1) (fromList [DynamicRanked (rconstant (rreplicate 2 (rconst 0.0))), DynamicRanked (rslice 0 2 (rscanDer (\\x59 x60 -> sin x59 - x60) (\\x61 x62 x63 x64 -> x61 * cos x63 + x62 * rconst -1.0) (\\x66 x67 x68 -> dmkHVector (fromList [DynamicRanked (cos x67 * x66), DynamicRanked (rconst -1.0 * x66)])) (rconst 1.1) v58)), DynamicRanked v58]))"

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
    @?= "let v65 = rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0] ; v102 = rreverse (rscanZipDer f df rf (rconst 0.0) [rconstant (rreplicate 2 (rconst 1.0)), rreverse (rslice 0 2 (rscanDer f df rf (rconst 1.1) v65)), rreverse v65]) ; v105 = rconstant (rreplicate 2 (rconst -1.0)) * (rconstant (rreplicate 2 (rconst 1.0)) + rgather [2] v102 (\\[i104] -> [1 + i104])) in rconst 5.0 * v105 ! [0] + rconst 7.0 * v105 ! [1] + v102 ! [0] + rconst 1.0"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let x11 = cos (sin (rconst 1.1) - rconst 1.1 * rconst 5.0) * rconst 1.0 in cos (rconst 1.1) * x11 + rconst 5.0 * (rconst -1.0 * x11) + rconst 7.0 * (rconst -1.0 * rconst 1.0) + cos (rconst 1.1) * rconst 1.0 + rconst 5.0 * (rconst -1.0 * rconst 1.0) + rconst 1.0"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v61 = rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0] in rscanZipDer f df rf (rconst 1.1) [rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanDer f df rf (rconst 1.1) v61), v61]"

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
                      x0 (rzero @f @Double (0 :$ ZS))
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
    @?= "rconstant (rgather [1000000,1000000] (rconst (fromList [2] [0.0,1.0])) (\\[i3, i2] -> [ifF (i3 <=. i2) 0 1]))"

unitriangular1 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> ShapeInt k -> ranked rk (2 + k)
unitriangular1 k sh =
  rbuild1 k $ \i ->
    rbuild1 k $ \j ->
      ifF (i <=. j) (rreplicate0N sh 0) (rreplicate0N sh 1)

testUnitriangular1PP :: Assertion
testUnitriangular1PP = do
  resetVarCounter
  let sh = 200 :$ 300 :$ 600 :$ ZS
      k = 1000000
      a1 = unitriangular1 @3 @Double @(AstRanked FullSpan) k sh
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rconstant (rgather [1000000,1000000,200,300,600] (rfromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 (rconst 0.0))))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 (rconst 1.0)))))]) (\\[i5, i6] -> [ifF (i5 <=. i6) 0 1, i5, i6]))"

unitriangular2 :: (KnownNat k, GoodScalar rk, ADReady ranked)
               => Int -> ShapeInt k -> ranked rk (2 + k)
unitriangular2 k sh =
  rgather @_ @_ @_ @_ @1 (k :$ k :$ sh)
          (rfromList [ rreplicate0N sh 0
                     , rreplicate0N sh 1 ])
          (\(i :. j :. ZI) -> (ifF (i <. j) 0 1) :. ZI)

testUnitriangular2PP :: Assertion
testUnitriangular2PP = do
  resetVarCounter
  let sh = 200 :$ 300 :$ 600 :$ ZS
      k = 1000000
      a1 = unitriangular2 @3 @Double @(AstRanked FullSpan) k sh
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rconstant (rgather [1000000,1000000,200,300,600] (rfromList [rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 (rconst 0.0))))), rreplicate 1000000 (rreplicate 1000000 (rreplicate 200 (rreplicate 300 (rreplicate 600 (rconst 1.0)))))]) (\\[i9, i10] -> [ifF (i9 <. i10) 0 1, i9, i10]))"

testSin0ScanD0 :: Assertion
testSin0ScanD0 = do
  assertEqualUpToEpsilon' 1e-10
    1
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 1
               f x0 = rscanZip (\x _a -> sin x)
                             (V.fromList [voidFromSh @Double ZS])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$ ZS))
           in f) 1.1)

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
                         (V.fromList [ voidFromSh @Double (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , voidFromSh @Double (4 :$ 5 :$ 6 :$ 7 :$ 8 :$ ZS) ])
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
                                        (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)])
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
                                         (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , voidFromSh @Double
                                         (8 :$ 3 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS) ])
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
                                         (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , voidFromSh @Double
                                         (8 :$ 3 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS) ])
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
                                                                             (8 :$ 3 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS) ])
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
                         (V.fromList [voidFromSh @Double (1 :$ 1 :$ ZS)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5
                                   $ (rsum (rtr x)))
                         (V.fromList [voidFromSh @Double (1 :$ 1 :$ ZS)])
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
                       (V.fromList [voidFromSh @Double (1 :$ 1 :$ 1 :$ ZS)])
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] 2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
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
      h = rrev1 @f @Double @0 @2
        (\a0 -> rfoldZip (\x a -> rtr $ rreplicate 5
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
    (OR.fromList [] [98.72666469795736])
    (rev' h 1.1)

testSin0ScanD8rev4 :: Assertion
testSin0ScanD8rev4 = do
  let h :: forall f. ADReady f => f Double 0 -> f Double 0
      h = rrev1 @f @Double @0 @2
        (\a0 -> rfoldZip (\x a -> rtr $ rreplicate 5
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
    (OR.fromList [] [98.72666469795736])
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
    @?= "let v63 = rconst (fromList [2] [42.0,42.0]) in rscanZipDer f df rf (rconst 0.0) [rconstant (rreplicate 2 (rconst 1.0)), rreverse (rslice 0 2 (rscanZipDer f df rf (rconst 1.1) [v63])), rreverse v63] ! [2] + rconst 1.0"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [voidFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v49 = rconst (fromList [2] [42.0,42.0]) in rscanZipDer f df rf (rconst 1.1) [rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanZipDer f df rf (rconst 1.1) [v49]), v49]"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v66 = rconst (fromList [2] [5.0,7.0]) in rscanZipDer f df rf (rconst 0.0) [rconstant (rreplicate 2 (rconst 1.0)), rreverse (rslice 0 2 (rscanZipDer f df rf (rconst 1.1) [v66])), rreverse v66] ! [2] + rconst 1.0"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v58 = rconst (fromList [2] [5.0,7.0]) in rscanZipDer f df rf (rconst 1.1) [rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanZipDer f df rf (rconst 1.1) [v58]), v58]"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [2.417297824578748] :: OR.Array 0 Double)
    (rev' (\x0 -> rbuild1 2 $ \k ->
       rscanZip (\x a -> sin x - rfromD (a V.! 0))
                (V.fromList [voidFromShS @Double @'[]])
                x0 (V.singleton $ DynamicShaped
                    $ sconst (OS.fromList @'[2, 2] @Double [5, 7, 3, 4])
                      !$ (k :$: ZSH) ))
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
    @?= 2394

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [voidFromSh @Double ZS])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v61 = rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0] in rscanZipDer f df rf (rconst 1.1) [rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanZipDer f df rf (rconst 1.1) [v61]), v61]"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.1])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [voidFromSh @Double ZS])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$ ZS))
     in f) 1.1)

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (V.fromList [ voidFromSh @Double ZS
                               , voidFromSh @Double (3 :$ 4 :$ ZS)])
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
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = srev (\v -> f (sfromD $ v V.! 0))
                 (V.singleton (voidFromShS @Double @'[]))
                 x
  length  -- unstable PP, so only length
    (printAstHVectorPretty
       IM.empty
       (g @(AstRanked FullSpan) (V.singleton $ DynamicShaped @Double @'[] 1.1)))
    @?= 1308

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
    @?= "let v725 = rscanDer f df rf (rconst 1.1) (rreplicate 11 (rconst 1.1)) ; x726 = rreshape [] (rreplicate 1 (rconst 1.0)) ; v965 = rreverse (rscanZipDer f df rf x726 [rreverse (rslice 0 11 v725), rreverse (rreplicate 11 (rconst 1.1))]) in [(let m984 = rtranspose [1,0] (rscanDer f df rf (rreplicate 11 (rconst 1.1)) (rreplicate 22 (rslice 0 11 v725))) ; m1003 = rtranspose [1,0] (rreverse (rscanZipDer f df rf (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rtranspose [1,0] m984)), rreplicate 22 (rgather [11] v725 (\\[i985] -> [i985]))])) ; v1011 = let m1005 = cos (rtranspose [1,0] (rreplicate 22 (rgather [11] v725 (\\[i1004] -> [i1004])))) ; m1008 = rgather [11,22] m1003 (\\[i1006, i1007] -> [i1006, 1 + i1007]) in rsum (rtranspose [1,0] (recip (m1005 * m1005) * rgather [11,22] m1003 (\\[i1009, i1010] -> [i1009, 1 + i1010]))) in rsum (rgather [11] m1003 (\\[i1012] -> [i1012, 0]))) + v965 ! [0]]"

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
    @?= "let v725 = rscanDer f df rf (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1))) ; v965 = rreverse (rscanZipDer f df rf (rconst 1.0) [rreverse (rslice 0 11 v725), rconstant (rreplicate 11 (rconst 1.1))]) in [rsum (rscanZipDer f df rf (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rscanDer f df rf (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v725)))), rreplicate 22 (rgather [11] v725 (\\[i985] -> [i985]))] ! [22]) + v965 ! [0]]"

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
    @?= "let v725 = rscanDer (\\x628 x629 -> rfoldDer (\\x630 x631 -> x630 + tan x631) (\\x632 x633 x634 x635 -> let x636 = cos x635 in x632 + x633 * recip (x636 * x636)) (\\x638 x639 x640 -> let x641 = cos x640 in [x638, recip (x641 * x641) * x638]) x629 (rreplicate 22 x628)) (\\x642 x643 x644 x645 -> rfoldZipDer (\\x659 [x660, x661, x662] -> let x663 = cos x662 in x659 + x660 * recip (x663 * x663)) (\\x665 [x666, x667, x668] x669 [x670, x671, x672] -> let x673 = cos x672 ; x674 = x673 * x673 ; x677 = x668 * negate (sin x672) in x665 + x666 * recip x674 + ((x677 * x673 + x677 * x673) * negate (recip (x674 * x674))) * x670) (\\x681 x682 [x683, x684, x685] -> let x686 = cos x685 ; x687 = x686 * x686 ; x690 = negate (recip (x687 * x687)) * (x683 * x681) in [x681, recip x687 * x681, 0, negate (sin x685) * (x686 * x690 + x686 * x690)]) x643 [rreplicate 22 x642, rslice 0 22 (rscanDer (\\x646 x647 -> x646 + tan x647) (\\x648 x649 x650 x651 -> let x652 = cos x651 in x648 + x649 * recip (x652 * x652)) (\\x654 x655 x656 -> let x657 = cos x656 in [x654, recip (x657 * x657) * x654]) x645 (rreplicate 22 x644)), rreplicate 22 x644]) (\\x691 x692 x693 -> let v720 = rreverse (rscanZipDer (\\x707 [x708, x709] -> x707) (\\x710 [x711, x712] x713 [x714, x715] -> x710) (\\x716 x717 [x718, x719] -> [x716, 0, 0]) x691 [rreverse (rslice 0 22 (rscanDer (\\x694 x695 -> x694 + tan x695) (\\x696 x697 x698 x699 -> let x700 = cos x699 in x696 + x697 * recip (x700 * x700)) (\\x702 x703 x704 -> let x705 = cos x704 in [x702, recip (x705 * x705) * x702]) x693 (rreplicate 22 x692))), rreplicate 22 x692]) in [let v721 = cos (rreplicate 22 x692) in rsum (recip (v721 * v721) * rgather [22] v720 (\\[i724] -> [1 + i724])), v720 ! [0]]) (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1))) ; v965 = rreverse (rscanZipDer (\\x727 [x728, x729] -> let v757 = cos (rreplicate 22 x728) in rsum (recip (v757 * v757) * rgather [22] (rscanZipDer (\\x743 [x744, x745] -> x743) (\\x746 [x747, x748] x749 [x750, x751] -> x746) (\\x752 x753 [x754, x755] -> [x752, 0, 0]) x727 [rreverse (rslice 0 22 (rscanDer (\\x730 x731 -> x730 + tan x731) (\\x732 x733 x734 x735 -> let x736 = cos x735 in x732 + x733 * recip (x736 * x736)) (\\x738 x739 x740 -> let x741 = cos x740 in [x738, recip (x741 * x741) * x738]) x729 (rreplicate 22 x728))), rreplicate 22 x728]) (\\[i760] -> [21 + negate i760]))) (\\x761 [x762, x763] x764 [x765, x766] -> let v779 = rscanDer (\\x767 x768 -> x767 + tan x768) (\\x769 x770 x771 x772 -> let x773 = cos x772 in x769 + x770 * recip (x773 * x773)) (\\x775 x776 x777 -> let x778 = cos x777 in [x775, recip (x778 * x778) * x775]) x766 (rreplicate 22 x765) ; v780 = rreverse (rslice 0 22 v779) ; v795 = rscanZipDer (\\x782 [x783, x784] -> x782) (\\x785 [x786, x787] x788 [x789, x790] -> x785) (\\x791 x792 [x793, x794] -> [x791, 0, 0]) x764 [v780, rreplicate 22 x765] ; v797 = cos (rreplicate 22 x765) ; v798 = v797 * v797 ; v802 = rreplicate 22 x762 * negate (sin (rreplicate 22 x765)) in rsum (rgather [22] v795 (\\[i800] -> [21 + negate i800]) * ((v802 * v797 + v802 * v797) * negate (recip (v798 * v798)))) + rsum (recip v798 * rgather [22] (rscanZipDer (\\x841 [x842, x843, x844, x845, x846] -> x841) (\\x847 [x848, x849, x850, x851, x852] x853 [x854, x855, x856, x857, x858] -> x847) (\\x859 x860 [x861, x862, x863, x864, x865] -> [x859, 0, 0, 0, 0, 0]) x761 [rreverse (rslice 0 22 (rscanZipDer (\\x805 [x806, x807, x808] -> let x809 = cos x808 in x805 + x806 * recip (x809 * x809)) (\\x811 [x812, x813, x814] x815 [x816, x817, x818] -> let x819 = cos x818 ; x820 = x819 * x819 ; x823 = x814 * negate (sin x818) in x811 + x812 * recip x820 + ((x823 * x819 + x823 * x819) * negate (recip (x820 * x820))) * x816) (\\x828 x829 [x830, x831, x832] -> let x833 = cos x832 ; x834 = x833 * x833 ; x837 = negate (recip (x834 * x834)) * (x830 * x828) in [x828, recip x834 * x828, 0, negate (sin x832) * (x833 * x837 + x833 * x837)]) x763 [rreplicate 22 x762, rslice 0 22 v779, rreplicate 22 x765])), rreplicate 22 x762, rslice 0 22 v795, v780, rreplicate 22 x765]) (\\[i867] -> [21 + negate i867]))) (\\x870 x871 [x872, x873] -> let v886 = rscanDer (\\x874 x875 -> x874 + tan x875) (\\x876 x877 x878 x879 -> let x880 = cos x879 in x876 + x877 * recip (x880 * x880)) (\\x882 x883 x884 -> let x885 = cos x884 in [x882, recip (x885 * x885) * x882]) x873 (rreplicate 22 x872) ; v887 = rreverse (rslice 0 22 v886) ; v902 = rscanZipDer (\\x889 [x890, x891] -> x889) (\\x892 [x893, x894] x895 [x896, x897] -> x892) (\\x898 x899 [x900, x901] -> [x898, 0, 0]) x871 [v887, rreplicate 22 x872] ; v904 = cos (rreplicate 22 x872) ; v905 = v904 * v904 ; v909 = negate (recip (v905 * v905)) * (rgather [22] v902 (\\[i907] -> [21 + negate i907]) * rreplicate 22 x870) ; v911 = rreverse (rscatter [23] (recip v905 * rreplicate 22 x870) (\\[i910] -> [1 + i910])) ; v938 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 22 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v958 = rreverse (rscanZipDer (\\x939 [x940, x941, x942] -> x939 + x940) (\\x944 [x945, x946, x947] x948 [x949, x950, x951] -> x944 + x945) (\\x953 x954 [x955, x956, x957] -> [x953, x953, 0, 0]) (rconst 0.0) [rreverse (rslice 1 22 v938), rreverse (rslice 0 22 v886), rreplicate 22 x872]) in [rscanZipDer (\\x912 [x913, x914, x915, x916] -> x912 + x913) (\\x917 [x918, x919, x920, x921] x922 [x923, x924, x925, x926] -> x917 + x918) (\\x928 x929 [x930, x931, x932, x933] -> [x928, x928, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 22 v911), rreverse (rslice 0 22 v902), rreverse v887, rreplicate 22 x872] ! [22] + v911 ! [0], (let v959 = cos (rreplicate 22 x872) in rsum (recip (v959 * v959) * (rgather [22] v958 (\\[i963] -> [1 + i963]) + rgather [22] v938 (\\[i964] -> [1 + i964])))) + rsum (rreplicate 22 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 22 x872)) * (v904 * v909 + v904 * v909)), v958 ! [0] + v938 ! [0]]) (rconst 1.0) [rreverse (rslice 0 11 v725), rconstant (rreplicate 11 (rconst 1.1))]) in [rsum (rscanZipDer (\\v986 [v987, v988] -> v986) (\\v991 [v992, v993] v994 [v995, v996] -> v991) (\\v998 v999 [v1000, v1001] -> [v998, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rscanDer (\\v966 v967 -> v966 + tan v967) (\\v969 v970 v971 v972 -> let v976 = cos v972 in v969 + v970 * recip (v976 * v976)) (\\v978 v979 v980 -> let v983 = cos v980 in [v978, recip (v983 * v983) * v978]) (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v725)))), rreplicate 22 (rgather [11] v725 (\\[i985] -> [i985]))] ! [22]) + v965 ! [0]]"

testSin0FoldNestedR1SimpSimpPP :: Assertion
testSin0FoldNestedR1SimpSimpPP = do
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
  printAstHVectorSimple
    IM.empty
    (simplifyAstHVector6
     $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1))
    @?= "rletInHVector (rscanDer (\\x628 x629 -> rfoldDer (\\x630 x631 -> x630 + tan x631) (\\x632 x633 x634 x635 -> rlet (cos x635) (\\x636 -> x632 + x633 * recip (x636 * x636))) (\\x638 x639 x640 -> rletInHVector (cos x640) (\\x641 -> dmkHVector (fromList [DynamicRanked x638, DynamicRanked (recip (x641 * x641) * x638)]))) x629 (rreplicate 22 x628)) (\\x642 x643 x644 x645 -> rfoldZipDer (\\x659 [x660 @Natural @Double @[], x661 @Natural @Double @[], x662 @Natural @Double @[]] -> rlet (cos x662) (\\x663 -> x659 + x660 * recip (x663 * x663))) (\\x665 [x666 @Natural @Double @[], x667 @Natural @Double @[], x668 @Natural @Double @[]] x669 [x670 @Natural @Double @[], x671 @Natural @Double @[], x672 @Natural @Double @[]] -> rlet (cos x672) (\\x673 -> rlet (x673 * x673) (\\x674 -> rlet (x668 * negate (sin x672)) (\\x677 -> x665 + x666 * recip x674 + ((x677 * x673 + x677 * x673) * negate (recip (x674 * x674))) * x670)))) (\\x681 x682 [x683 @Natural @Double @[], x684 @Natural @Double @[], x685 @Natural @Double @[]] -> rletInHVector (cos x685) (\\x686 -> rletInHVector (x686 * x686) (\\x687 -> rletInHVector (negate (recip (x687 * x687)) * (x683 * x681)) (\\x690 -> dmkHVector (fromList [DynamicRanked x681, DynamicRanked (recip x687 * x681), DynamicRankedDummy, DynamicRanked (negate (sin x685) * (x686 * x690 + x686 * x690))]))))) x643 (fromList [DynamicRanked (rreplicate 22 x642), DynamicRanked (rslice 0 22 (rscanDer (\\x646 x647 -> x646 + tan x647) (\\x648 x649 x650 x651 -> rlet (cos x651) (\\x652 -> x648 + x649 * recip (x652 * x652))) (\\x654 x655 x656 -> rletInHVector (cos x656) (\\x657 -> dmkHVector (fromList [DynamicRanked x654, DynamicRanked (recip (x657 * x657) * x654)]))) x645 (rreplicate 22 x644))), DynamicRanked (rreplicate 22 x644)])) (\\x691 x692 x693 -> rletInHVector (rreverse (rscanZipDer (\\x707 [x708 @Natural @Double @[], x709 @Natural @Double @[]] -> x707) (\\x710 [x711 @Natural @Double @[], x712 @Natural @Double @[]] x713 [x714 @Natural @Double @[], x715 @Natural @Double @[]] -> x710) (\\x716 x717 [x718 @Natural @Double @[], x719 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x716, DynamicRankedDummy, DynamicRankedDummy])) x691 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\x694 x695 -> x694 + tan x695) (\\x696 x697 x698 x699 -> rlet (cos x699) (\\x700 -> x696 + x697 * recip (x700 * x700))) (\\x702 x703 x704 -> rletInHVector (cos x704) (\\x705 -> dmkHVector (fromList [DynamicRanked x702, DynamicRanked (recip (x705 * x705) * x702)]))) x693 (rreplicate 22 x692)))), DynamicRanked (rreplicate 22 x692)]))) (\\v720 -> dmkHVector (fromList [DynamicRanked (rlet (cos (rreplicate 22 x692)) (\\v721 -> rsum (recip (v721 * v721) * rgather [22] v720 (\\[i724] -> [1 + i724])))), DynamicRanked (v720 ! [0])]))) (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1)))) (\\v725 -> rletInHVector (rreverse (rscanZipDer (\\x727 [x728 @Natural @Double @[], x729 @Natural @Double @[]] -> rlet (cos (rreplicate 22 x728)) (\\v757 -> rsum (recip (v757 * v757) * rgather [22] (rscanZipDer (\\x743 [x744 @Natural @Double @[], x745 @Natural @Double @[]] -> x743) (\\x746 [x747 @Natural @Double @[], x748 @Natural @Double @[]] x749 [x750 @Natural @Double @[], x751 @Natural @Double @[]] -> x746) (\\x752 x753 [x754 @Natural @Double @[], x755 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x752, DynamicRankedDummy, DynamicRankedDummy])) x727 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\x730 x731 -> x730 + tan x731) (\\x732 x733 x734 x735 -> rlet (cos x735) (\\x736 -> x732 + x733 * recip (x736 * x736))) (\\x738 x739 x740 -> rletInHVector (cos x740) (\\x741 -> dmkHVector (fromList [DynamicRanked x738, DynamicRanked (recip (x741 * x741) * x738)]))) x729 (rreplicate 22 x728)))), DynamicRanked (rreplicate 22 x728)])) (\\[i760] -> [21 + negate i760])))) (\\x761 [x762 @Natural @Double @[], x763 @Natural @Double @[]] x764 [x765 @Natural @Double @[], x766 @Natural @Double @[]] -> rlet (rscanDer (\\x767 x768 -> x767 + tan x768) (\\x769 x770 x771 x772 -> rlet (cos x772) (\\x773 -> x769 + x770 * recip (x773 * x773))) (\\x775 x776 x777 -> rletInHVector (cos x777) (\\x778 -> dmkHVector (fromList [DynamicRanked x775, DynamicRanked (recip (x778 * x778) * x775)]))) x766 (rreplicate 22 x765)) (\\v779 -> rlet (rreverse (rslice 0 22 v779)) (\\v780 -> rlet (rscanZipDer (\\x782 [x783 @Natural @Double @[], x784 @Natural @Double @[]] -> x782) (\\x785 [x786 @Natural @Double @[], x787 @Natural @Double @[]] x788 [x789 @Natural @Double @[], x790 @Natural @Double @[]] -> x785) (\\x791 x792 [x793 @Natural @Double @[], x794 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x791, DynamicRankedDummy, DynamicRankedDummy])) x764 (fromList [DynamicRanked v780, DynamicRanked (rreplicate 22 x765)])) (\\v795 -> rlet (cos (rreplicate 22 x765)) (\\v797 -> rlet (v797 * v797) (\\v798 -> rlet (rreplicate 22 x762 * negate (sin (rreplicate 22 x765))) (\\v802 -> rsum (rgather [22] v795 (\\[i800] -> [21 + negate i800]) * ((v802 * v797 + v802 * v797) * negate (recip (v798 * v798)))) + rsum (recip v798 * rgather [22] (rscanZipDer (\\x841 [x842 @Natural @Double @[], x843 @Natural @Double @[], x844 @Natural @Double @[], x845 @Natural @Double @[], x846 @Natural @Double @[]] -> x841) (\\x847 [x848 @Natural @Double @[], x849 @Natural @Double @[], x850 @Natural @Double @[], x851 @Natural @Double @[], x852 @Natural @Double @[]] x853 [x854 @Natural @Double @[], x855 @Natural @Double @[], x856 @Natural @Double @[], x857 @Natural @Double @[], x858 @Natural @Double @[]] -> x847) (\\x859 x860 [x861 @Natural @Double @[], x862 @Natural @Double @[], x863 @Natural @Double @[], x864 @Natural @Double @[], x865 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x859, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy])) x761 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanZipDer (\\x805 [x806 @Natural @Double @[], x807 @Natural @Double @[], x808 @Natural @Double @[]] -> rlet (cos x808) (\\x809 -> x805 + x806 * recip (x809 * x809))) (\\x811 [x812 @Natural @Double @[], x813 @Natural @Double @[], x814 @Natural @Double @[]] x815 [x816 @Natural @Double @[], x817 @Natural @Double @[], x818 @Natural @Double @[]] -> rlet (cos x818) (\\x819 -> rlet (x819 * x819) (\\x820 -> rlet (x814 * negate (sin x818)) (\\x823 -> x811 + x812 * recip x820 + ((x823 * x819 + x823 * x819) * negate (recip (x820 * x820))) * x816)))) (\\x828 x829 [x830 @Natural @Double @[], x831 @Natural @Double @[], x832 @Natural @Double @[]] -> rletInHVector (cos x832) (\\x833 -> rletInHVector (x833 * x833) (\\x834 -> rletInHVector (negate (recip (x834 * x834)) * (x830 * x828)) (\\x837 -> dmkHVector (fromList [DynamicRanked x828, DynamicRanked (recip x834 * x828), DynamicRankedDummy, DynamicRanked (negate (sin x832) * (x833 * x837 + x833 * x837))]))))) x763 (fromList [DynamicRanked (rreplicate 22 x762), DynamicRanked (rslice 0 22 v779), DynamicRanked (rreplicate 22 x765)])))), DynamicRanked (rreplicate 22 x762), DynamicRanked (rslice 0 22 v795), DynamicRanked v780, DynamicRanked (rreplicate 22 x765)])) (\\[i867] -> [21 + negate i867]))))))))) (\\x870 x871 [x872 @Natural @Double @[], x873 @Natural @Double @[]] -> rletInHVector (rscanDer (\\x874 x875 -> x874 + tan x875) (\\x876 x877 x878 x879 -> rlet (cos x879) (\\x880 -> x876 + x877 * recip (x880 * x880))) (\\x882 x883 x884 -> rletInHVector (cos x884) (\\x885 -> dmkHVector (fromList [DynamicRanked x882, DynamicRanked (recip (x885 * x885) * x882)]))) x873 (rreplicate 22 x872)) (\\v886 -> rletInHVector (rreverse (rslice 0 22 v886)) (\\v887 -> rletInHVector (rscanZipDer (\\x889 [x890 @Natural @Double @[], x891 @Natural @Double @[]] -> x889) (\\x892 [x893 @Natural @Double @[], x894 @Natural @Double @[]] x895 [x896 @Natural @Double @[], x897 @Natural @Double @[]] -> x892) (\\x898 x899 [x900 @Natural @Double @[], x901 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x898, DynamicRankedDummy, DynamicRankedDummy])) x871 (fromList [DynamicRanked v887, DynamicRanked (rreplicate 22 x872)])) (\\v902 -> rletInHVector (cos (rreplicate 22 x872)) (\\v904 -> rletInHVector (v904 * v904) (\\v905 -> rletInHVector (negate (recip (v905 * v905)) * (rgather [22] v902 (\\[i907] -> [21 + negate i907]) * rreplicate 22 x870)) (\\v909 -> rletInHVector (rreverse (rscatter [23] (recip v905 * rreplicate 22 x870) (\\[i910] -> [1 + i910]))) (\\v911 -> rletInHVector (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 22 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)))) (\\v938 -> rletInHVector (rreverse (rscanZipDer (\\x939 [x940 @Natural @Double @[], x941 @Natural @Double @[], x942 @Natural @Double @[]] -> x939 + x940) (\\x944 [x945 @Natural @Double @[], x946 @Natural @Double @[], x947 @Natural @Double @[]] x948 [x949 @Natural @Double @[], x950 @Natural @Double @[], x951 @Natural @Double @[]] -> x944 + x945) (\\x953 x954 [x955 @Natural @Double @[], x956 @Natural @Double @[], x957 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x953, DynamicRanked x953, DynamicRankedDummy, DynamicRankedDummy])) (rconst 0.0) (fromList [DynamicRanked (rreverse (rslice 1 22 v938)), DynamicRanked (rreverse (rslice 0 22 v886)), DynamicRanked (rreplicate 22 x872)]))) (\\v958 -> dmkHVector (fromList [DynamicRanked (rscanZipDer (\\x912 [x913 @Natural @Double @[], x914 @Natural @Double @[], x915 @Natural @Double @[], x916 @Natural @Double @[]] -> x912 + x913) (\\x917 [x918 @Natural @Double @[], x919 @Natural @Double @[], x920 @Natural @Double @[], x921 @Natural @Double @[]] x922 [x923 @Natural @Double @[], x924 @Natural @Double @[], x925 @Natural @Double @[], x926 @Natural @Double @[]] -> x917 + x918) (\\x928 x929 [x930 @Natural @Double @[], x931 @Natural @Double @[], x932 @Natural @Double @[], x933 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x928, DynamicRanked x928, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy])) (rconst 0.0) (fromList [DynamicRanked (rreverse (rslice 1 22 v911)), DynamicRanked (rreverse (rslice 0 22 v902)), DynamicRanked (rreverse v887), DynamicRanked (rreplicate 22 x872)]) ! [22] + v911 ! [0]), DynamicRanked (rlet (cos (rreplicate 22 x872)) (\\v959 -> rsum (recip (v959 * v959) * (rgather [22] v958 (\\[i963] -> [1 + i963]) + rgather [22] v938 (\\[i964] -> [1 + i964])))) + rsum (rreplicate 22 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 22 x872)) * (v904 * v909 + v904 * v909))), DynamicRanked (v958 ! [0] + v938 ! [0])]))))))))))) (rconst 1.0) (fromList [DynamicRanked (rreverse (rslice 0 11 v725)), DynamicRanked (rconstant (rreplicate 11 (rconst 1.1)))]))) (\\v965 -> dmkHVector (fromList [DynamicRanked (rsum (rscanZipDer (\\v986 [v987 @Natural @Double @[11], v988 @Natural @Double @[11]] -> v986) (\\v991 [v992 @Natural @Double @[11], v993 @Natural @Double @[11]] v994 [v995 @Natural @Double @[11], v996 @Natural @Double @[11]] -> v991) (\\v998 v999 [v1000 @Natural @Double @[11], v1001 @Natural @Double @[11]] -> dmkHVector (fromList [DynamicRanked v998, DynamicRanked (sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])), DynamicRanked (sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))])) (rgather [11] v965 (\\[i990] -> [1 + i990])) (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\v966 v967 -> v966 + tan v967) (\\v969 v970 v971 v972 -> rlet (cos v972) (\\v976 -> v969 + v970 * recip (v976 * v976))) (\\v978 v979 v980 -> rletInHVector (cos v980) (\\v983 -> dmkHVector (fromList [DynamicRanked v978, DynamicRanked (recip (v983 * v983) * v978)]))) (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v725))))), DynamicRanked (rreplicate 22 (rgather [11] v725 (\\[i985] -> [i985])))]) ! [22]) + v965 ! [0])])))"

testSin0FoldNestedR0LengthPP :: Assertion
testSin0FoldNestedR0LengthPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a -> x + tan a)
                  z (rreplicate 2 z)
      g :: forall g. HVectorTensor g (ShapedOf g) => HVector g -> HVectorOf g
      g x = rrev (\v -> f (rfromD $ v V.! 0))
                 (V.singleton (voidFromSh @Double ZS))
                 x
  length
    (printAstHVectorPrettyButNested
      IM.empty
      (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 668

testSin0FoldNestedR1LengthPP :: Assertion
testSin0FoldNestedR1LengthPP = do
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
    (printAstHVectorPrettyButNested
      IM.empty
      (g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 7_904

testSin0FoldNestedR2LengthPP :: Assertion
testSin0FoldNestedR2LengthPP = do
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
    (printAstHVectorPrettyButNested
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 119_898

testSin0FoldNestedR3LengthPP :: Assertion
testSin0FoldNestedR3LengthPP = do
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
    (printAstHVectorPrettyButNested
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 2_312_298

testSin0FoldNestedR4LengthPP :: Assertion
testSin0FoldNestedR4LengthPP = do
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
    (printAstHVectorPrettyButNested
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 48_861_457

-- Uses 30G in GHC 9.8.1 with -O1 and patchy specialization.
_testSin0FoldNestedR5LengthPP :: Assertion
_testSin0FoldNestedR5LengthPP = do
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
    (printAstHVectorPrettyButNested
       IM.empty
       (simplifyAstHVector6
        $ g @(AstRanked FullSpan) (V.singleton $ DynamicRanked @Double @0 1.1)))
    @?= 1_156_198_859

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

-- TODO: re-enable when simplification of AstShaped is completed
_testSin0FoldNestedS4 :: Assertion
_testSin0FoldNestedS4 = do
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

-- TODO: re-enable when simplification of AstShaped is completed
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
    (0.22000000000000003)
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
    (0.24200000000000005)
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

-- TODO: re-enable when simplification of AstRanked is completed
_testSin0FoldNestedR2RevFwd :: Assertion
_testSin0FoldNestedR2RevFwd = do
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

-- TODO: re-enable when simplification of AstRanked is completed
_testSin0FoldNestedR4 :: Assertion
_testSin0FoldNestedR4 = do
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

-- TODO: re-enable when simplification of AstRanked is completed
_testSin0FoldNestedR41 :: Assertion
_testSin0FoldNestedR41 = do
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

-- TODO: re-enable when simplification of AstRanked is completed
_testSin0FoldNestedR40 :: Assertion
_testSin0FoldNestedR40 = do
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

-- TODO: re-enable when anything is slightly improved (200s optimized ATM)
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
    @?= 45638

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
    @?= "dmkHVector (fromList [DynamicRanked (cos (rconst 1.1) * rreshape [] (rreplicate 1 (rconst 1.0)))])"

testSin0revhV2 :: Assertion
testSin0revhV2 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        rrev @g @_ @Double @0 (\v -> sin (rfromD $ v V.! 0))
             (V.singleton (voidFromSh @Double ZS))
             x
      h :: forall g.
           ( HVectorTensor g (ShapedOf g)
           , HVectorTensor (ADVal g) (ShapedOf (ADVal g)) )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @0 (-0.8912073600614354))
    (crev (h @(Flip OR.Array)) (V.singleton $ DynamicRanked @Double @0 1.1))

testSin0revhV3 :: Assertion
testSin0revhV3 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f x =
        srev @g @_ @Double @'[] (\v -> sin (sfromD $ v V.! 0))
             (V.singleton (voidFromShS @Double @'[]))
             x
      h :: forall g.
           ( HVectorTensor g (ShapedOf g)
           , HVectorTensor (ADVal g) (ShapedOf (ADVal g)) )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[] (-0.8912073600614354))
    (crev (h @(Flip OR.Array)) (V.singleton $ DynamicShaped @Double @'[] 1.1))

testSin0revhV4 :: Assertion
testSin0revhV4 = do
  let f :: forall g. (HVectorTensor g (ShapedOf g), Fractional (g Double 0))
        => HVector g -> HVectorOf g
      doms = V.singleton (voidFromSh @Double ZS)
      doms3 = V.singleton (voidFromSh @Double (3 :$ ZS))
      f x =
        rrevDt @g @_ @Double @0 (\v -> rfoldZip const doms 5 v)
               doms3 x 22.5
      h :: forall g. ( HVectorTensor g (ShapedOf g)
                     , HVectorTensor (ADVal g) (ShapedOf (ADVal g))
                     , Fractional (g Double 0), IsPrimal g Double 0 )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [0, 0, 0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 1.1))

testSin0revhV5 :: Assertion
testSin0revhV5 = do
  let f :: forall g. ( HVectorTensor g (ShapedOf g)
                     , Fractional (ShapedOf g Double '[]) )
        => HVector g -> HVectorOf g
      doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f x =
        srevDt @g @_ @Double @'[] (\v -> sfoldZip const doms 5 v)
               doms3 x 22.5
      h :: forall g. ( HVectorTensor g (ShapedOf g)
                     , HVectorTensor (ADVal g) (ShapedOf (ADVal g))
                     , Fractional (ShapedOf  g Double '[])
                     , IsPrimal (ShapedOf g) Double '[] )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList [0, 0, 0])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1))

testSin0revhV6 :: Assertion
testSin0revhV6 = do
  let f :: forall g. (HVectorTensor g (ShapedOf g), Fractional (g Double 0))
        => HVector g -> HVectorOf g
      doms = V.singleton (voidFromSh @Double ZS)
      doms3 = V.singleton (voidFromSh @Double (3 :$ ZS))
      f x =
        rrevDt @g @_ @Double @0
               (\v -> rfoldZip (\_ w -> let z = rfromD $ w V.! 0
                                        in z * z) doms 5 v)
                doms3 x 22
      h :: forall g. ( HVectorTensor g (ShapedOf g)
                     , HVectorTensor (ADVal g) (ShapedOf (ADVal g))
                     , Fractional (g Double 0), IsPrimal g Double 0 )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicRanked @Double @1 $ rfromList [0, 0, 44])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicRanked @Double @1 $ rreplicate 3 1.1))

testSin0revhV7 :: Assertion
testSin0revhV7 = do
  let f :: forall g. ( HVectorTensor g (ShapedOf g)
                     , Fractional (ShapedOf g Double '[]) )
        => HVector g -> HVectorOf g
      doms = V.singleton (voidFromShS @Double @'[])
      doms3 = V.singleton (voidFromShS @Double @'[3])
      f x =
        srevDt @g @_ @Double @'[]
               (\v -> sfoldZip (\_ w -> let z = sfromD $ w V.! 0
                                        in z * z) doms 5 v)
               doms3 x 22
      h :: forall g. ( HVectorTensor g (ShapedOf g)
                     , HVectorTensor (ADVal g) (ShapedOf (ADVal g))
                     , Fractional (ShapedOf  g Double '[])
                     , IsPrimal (ShapedOf g) Double '[] )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList [0, 0, 44])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1))

testSin0revhV8 :: Assertion
testSin0revhV8 = do
  let f :: forall g. HVectorTensor g (ShapedOf g)
        => HVector g -> HVectorOf g
      f = dmkHVector
      h :: forall g.
           ( HVectorTensor g (ShapedOf g)
           , HVectorTensor (ADVal g) (ShapedOf (ADVal g)) )
        => HVector (ADVal g)
        -> ADVal (HVectorPseudoTensor g) Float '()
      h = hVectorADValToADVal . f
  assertEqualUpToEpsilon 1e-10
    (V.singleton $ DynamicShaped @Double @'[3] $ sfromList [1, 1, 1])
    (crev (h @(Flip OR.Array))
          (V.singleton $ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1))

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
              in rletHVectorIn domsF (rf cr x a) $ \rfRes ->
                   fst (domsToPair rfRes))
          domsF
          cShared
          (V.cons (DynamicRanked lp) las)
      crs = rreverse crsr
      rg :: ranked r (1 + n) -> ranked r (1 + n)
         -> HVector ranked
         -> HVectorOf ranked
      rg cr2 x2 a2 =
        dzipWith1 (\doms ->
                     let (cr, x, a) = domsTo3 doms
                     in dletHVectorInHVector @ranked
                          domsF (rf cr x a) $ \rfRes ->
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
      p = rscanZipDer f (\a _ _ _ -> a) rf doms 7 as
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

{- TODO: define DerivativeStages AstHVector to make this possible:
testSin0revhFoldZip4R :: Assertion
testSin0revhFoldZip4R = do
  let h :: ranked ~ Flip OR.Array
        => HVector (AstRanked FullSpan)
        -> AstHVector FullSpan
      h = fFoldZipRX @(AstRanked FullSpan)
  assertEqualUpToEpsilon 1e-10
    (V.fromList [ DynamicRanked @Double @1 $ rfromList [0, 0, 0]
                , DynamicRanked @Double @1
                  $ rreplicate 3 (-7.313585321642452e-2) ])
    (rev h (V.fromList [ DynamicRanked @Double @1 $ rreplicate 3 1.1
                       , DynamicRanked @Double @1 $ rreplicate 3 1.1 ]))
-}

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
                         domsF (rf cr x a) $ \rfRes ->
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
                         sletHVectorIn domsF (rf cr x a) $ \rfRes ->
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
      p = sscanDer f (\a _ _ _ -> a) rf 7 as
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
    (rev @_ @_ @(AstShaped FullSpan) @(HVector (Flip OR.Array))
         (\(asD :: AstHVector FullSpan) ->
            sletHVectorIn (V.fromList [ voidFromShS @Double @'[3]
                                      , voidFromShS @Double @'[3] ])
                          asD (\asV -> fFoldSX (sfromD (asV V.! 1))))
         (V.fromList [ DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1
                     , DynamicShaped @Double @'[3] $ sreplicate @_ @3 1.1 ]))
