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
  , testCase "4Sin0FoldNestedR2SimpNestedPP" testSin0FoldNestedR2SimpNestedPP
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
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [voidFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1)

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
    @?= "let v720 = rscanDer f df rf (rconst 1.1) (rreplicate 11 (rconst 1.1)) ; x721 = rreshape [] (rreplicate 1 (rconst 1.0)) ; v965 = rreverse (rscanZipDer f df rf x721 [rreverse (rslice 0 11 v720), rreverse (rreplicate 11 (rconst 1.1))]) in [(let m984 = rtranspose [1,0] (rscanDer f df rf (rreplicate 11 (rconst 1.1)) (rreplicate 22 (rslice 0 11 v720))) ; m1003 = rtranspose [1,0] (rreverse (rscanZipDer f df rf (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rtranspose [1,0] m984)), rreplicate 22 (rgather [11] v720 (\\[i985] -> [i985]))])) ; v1011 = let m1005 = cos (rtranspose [1,0] (rreplicate 22 (rgather [11] v720 (\\[i1004] -> [i1004])))) ; m1008 = rgather [11,22] m1003 (\\[i1006, i1007] -> [i1006, 1 + i1007]) in rsum (rtranspose [1,0] (recip (m1005 * m1005) * rgather [11,22] m1003 (\\[i1009, i1010] -> [i1009, 1 + i1010]))) in rsum (rgather [11] m1003 (\\[i1012] -> [i1012, 0]))) + v965 ! [0]]"

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
    @?= "let v720 = rscanDer f df rf (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1))) ; v965 = rreverse (rscanZipDer f df rf (rconst 1.0) [rreverse (rslice 0 11 v720), rconstant (rreplicate 11 (rconst 1.1))]) in [rsum (rscanZipDer f df rf (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rscanDer f df rf (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v720)))), rreplicate 22 (rgather [11] v720 (\\[i985] -> [i985]))] ! [22]) + v965 ! [0]]"

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
    @?= "let v720 = rscanDer (\\x623 x624 -> rfoldDer (\\x625 x626 -> x625 + tan x626) (\\x627 x628 x629 x630 -> let x631 = cos x630 in x627 + x628 * recip (x631 * x631)) (\\x633 x634 x635 -> let x636 = cos x635 in [x633, recip (x636 * x636) * x633]) x624 (rreplicate 22 x623)) (\\x637 x638 x639 x640 -> rfoldZipDer (\\x654 [x655, x656, x657] -> let x658 = cos x657 in x654 + x655 * recip (x658 * x658)) (\\x660 [x661, x662, x663] x664 [x665, x666, x667] -> let x668 = cos x667 ; x669 = x668 * x668 ; x672 = x663 * negate (sin x667) in x660 + x661 * recip x669 + ((x672 * x668 + x672 * x668) * negate (recip (x669 * x669))) * x665) (\\x676 x677 [x678, x679, x680] -> let x681 = cos x680 ; x682 = x681 * x681 ; x685 = negate (recip (x682 * x682)) * (x678 * x676) in [x676, recip x682 * x676, 0, negate (sin x680) * (x681 * x685 + x681 * x685)]) x638 [rreplicate 22 x637, rslice 0 22 (rscanDer (\\x641 x642 -> x641 + tan x642) (\\x643 x644 x645 x646 -> let x647 = cos x646 in x643 + x644 * recip (x647 * x647)) (\\x649 x650 x651 -> let x652 = cos x651 in [x649, recip (x652 * x652) * x649]) x640 (rreplicate 22 x639)), rreplicate 22 x639]) (\\x686 x687 x688 -> let v715 = rreverse (rscanZipDer (\\x702 [x703, x704] -> x702) (\\x705 [x706, x707] x708 [x709, x710] -> x705) (\\x711 x712 [x713, x714] -> [x711, 0, 0]) x686 [rreverse (rslice 0 22 (rscanDer (\\x689 x690 -> x689 + tan x690) (\\x691 x692 x693 x694 -> let x695 = cos x694 in x691 + x692 * recip (x695 * x695)) (\\x697 x698 x699 -> let x700 = cos x699 in [x697, recip (x700 * x700) * x697]) x688 (rreplicate 22 x687))), rreplicate 22 x687]) in [let v716 = cos (rreplicate 22 x687) in rsum (recip (v716 * v716) * rgather [22] v715 (\\[i719] -> [1 + i719])), v715 ! [0]]) (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1))) ; v965 = rreverse (rscanZipDer (\\x722 [x723, x724] -> let v752 = cos (rreplicate 22 x723) in rsum (recip (v752 * v752) * rgather [22] (rscanZipDer (\\x738 [x739, x740] -> x738) (\\x741 [x742, x743] x744 [x745, x746] -> x741) (\\x747 x748 [x749, x750] -> [x747, 0, 0]) x722 [rreverse (rslice 0 22 (rscanDer (\\x725 x726 -> x725 + tan x726) (\\x727 x728 x729 x730 -> let x731 = cos x730 in x727 + x728 * recip (x731 * x731)) (\\x733 x734 x735 -> let x736 = cos x735 in [x733, recip (x736 * x736) * x733]) x724 (rreplicate 22 x723))), rreplicate 22 x723]) (\\[i755] -> [21 + negate i755]))) (\\x756 [x757, x758] x759 [x760, x761] -> let v774 = rscanDer (\\x762 x763 -> x762 + tan x763) (\\x764 x765 x766 x767 -> let x768 = cos x767 in x764 + x765 * recip (x768 * x768)) (\\x770 x771 x772 -> let x773 = cos x772 in [x770, recip (x773 * x773) * x770]) x761 (rreplicate 22 x760) ; v775 = rreverse (rslice 0 22 v774) ; v790 = rscanZipDer (\\x777 [x778, x779] -> x777) (\\x780 [x781, x782] x783 [x784, x785] -> x780) (\\x786 x787 [x788, x789] -> [x786, 0, 0]) x759 [v775, rreplicate 22 x760] ; v792 = cos (rreplicate 22 x760) ; v793 = v792 * v792 ; v797 = rreplicate 22 x757 * negate (sin (rreplicate 22 x760)) in rsum (rgather [22] v790 (\\[i795] -> [21 + negate i795]) * ((v797 * v792 + v797 * v792) * negate (recip (v793 * v793)))) + rsum (recip v793 * rgather [22] (rscanZipDer (\\x836 [x837, x838, x839, x840, x841] -> x836) (\\x842 [x843, x844, x845, x846, x847] x848 [x849, x850, x851, x852, x853] -> x842) (\\x854 x855 [x856, x857, x858, x859, x860] -> [x854, 0, 0, 0, 0, 0]) x756 [rreverse (rslice 0 22 (rscanZipDer (\\x800 [x801, x802, x803] -> let x804 = cos x803 in x800 + x801 * recip (x804 * x804)) (\\x806 [x807, x808, x809] x810 [x811, x812, x813] -> let x814 = cos x813 ; x815 = x814 * x814 ; x818 = x809 * negate (sin x813) in x806 + x807 * recip x815 + ((x818 * x814 + x818 * x814) * negate (recip (x815 * x815))) * x811) (\\x823 x824 [x825, x826, x827] -> let x828 = cos x827 ; x829 = x828 * x828 ; x832 = negate (recip (x829 * x829)) * (x825 * x823) in [x823, recip x829 * x823, 0, negate (sin x827) * (x828 * x832 + x828 * x832)]) x758 [rreplicate 22 x757, rslice 0 22 v774, rreplicate 22 x760])), rreplicate 22 x757, rslice 0 22 v790, v775, rreplicate 22 x760]) (\\[i862] -> [21 + negate i862]))) (\\x865 x866 [x867, x868] -> let v886 = rscanDer (\\x874 x875 -> x874 + tan x875) (\\x876 x877 x878 x879 -> let x880 = cos x879 in x876 + x877 * recip (x880 * x880)) (\\x882 x883 x884 -> let x885 = cos x884 in [x882, recip (x885 * x885) * x882]) x868 (rreplicate 22 x867) ; v887 = rreverse (rslice 0 22 v886) ; v902 = rscanZipDer (\\x889 [x890, x891] -> x889) (\\x892 [x893, x894] x895 [x896, x897] -> x892) (\\x898 x899 [x900, x901] -> [x898, 0, 0]) x866 [v887, rreplicate 22 x867] ; v904 = cos (rreplicate 22 x867) ; v905 = v904 * v904 ; v909 = negate (recip (v905 * v905)) * (rgather [22] v902 (\\[i907] -> [21 + negate i907]) * rreplicate 22 x865) ; v911 = rreverse (rscatter [23] (recip v905 * rreplicate 22 x865) (\\[i910] -> [1 + i910])) ; v938 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 22 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v958 = rreverse (rscanZipDer (\\x939 [x940, x941, x942] -> x939 + x940) (\\x944 [x945, x946, x947] x948 [x949, x950, x951] -> x944 + x945) (\\x953 x954 [x955, x956, x957] -> [x953, x953, 0, 0]) (rconst 0.0) [rreverse (rslice 1 22 v938), rreverse (rslice 0 22 v886), rreplicate 22 x867]) in [rscanZipDer (\\x912 [x913, x914, x915, x916] -> x912 + x913) (\\x917 [x918, x919, x920, x921] x922 [x923, x924, x925, x926] -> x917 + x918) (\\x928 x929 [x930, x931, x932, x933] -> [x928, x928, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 22 v911), rreverse (rslice 0 22 v902), rreverse v887, rreplicate 22 x867] ! [22] + v911 ! [0], (let v959 = cos (rreplicate 22 x867) in rsum (recip (v959 * v959) * (rgather [22] v958 (\\[i963] -> [1 + i963]) + rgather [22] v938 (\\[i964] -> [1 + i964])))) + rsum (rreplicate 22 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 22 x867)) * (v904 * v909 + v904 * v909)), v958 ! [0] + v938 ! [0]]) (rconst 1.0) [rreverse (rslice 0 11 v720), rconstant (rreplicate 11 (rconst 1.1))]) in [rsum (rscanZipDer (\\v986 [v987, v988] -> v986) (\\v991 [v992, v993] v994 [v995, v996] -> v991) (\\v998 v999 [v1000, v1001] -> [v998, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [11] v965 (\\[i990] -> [1 + i990])) [rreverse (rslice 0 22 (rscanDer (\\v966 v967 -> v966 + tan v967) (\\v969 v970 v971 v972 -> let v976 = cos v972 in v969 + v970 * recip (v976 * v976)) (\\v978 v979 v980 -> let v983 = cos v980 in [v978, recip (v983 * v983) * v978]) (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v720)))), rreplicate 22 (rgather [11] v720 (\\[i985] -> [i985]))] ! [22]) + v965 ! [0]]"

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
    @?= "rletInHVector (rscanDer (\\x623 x624 -> rfoldDer (\\x625 x626 -> x625 + tan x626) (\\x627 x628 x629 x630 -> rlet (cos x630) (\\x631 -> x627 + x628 * recip (x631 * x631))) (\\x633 x634 x635 -> rletInHVector (cos x635) (\\x636 -> dmkHVector (fromList [DynamicRanked x633, DynamicRanked (recip (x636 * x636) * x633)]))) x624 (rreplicate 22 x623)) (\\x637 x638 x639 x640 -> rfoldZipDer (\\x654 [x655 @Natural @Double @[], x656 @Natural @Double @[], x657 @Natural @Double @[]] -> rlet (cos x657) (\\x658 -> x654 + x655 * recip (x658 * x658))) (\\x660 [x661 @Natural @Double @[], x662 @Natural @Double @[], x663 @Natural @Double @[]] x664 [x665 @Natural @Double @[], x666 @Natural @Double @[], x667 @Natural @Double @[]] -> rlet (cos x667) (\\x668 -> rlet (x668 * x668) (\\x669 -> rlet (x663 * negate (sin x667)) (\\x672 -> x660 + x661 * recip x669 + ((x672 * x668 + x672 * x668) * negate (recip (x669 * x669))) * x665)))) (\\x676 x677 [x678 @Natural @Double @[], x679 @Natural @Double @[], x680 @Natural @Double @[]] -> rletInHVector (cos x680) (\\x681 -> rletInHVector (x681 * x681) (\\x682 -> rletInHVector (negate (recip (x682 * x682)) * (x678 * x676)) (\\x685 -> dmkHVector (fromList [DynamicRanked x676, DynamicRanked (recip x682 * x676), DynamicRankedDummy, DynamicRanked (negate (sin x680) * (x681 * x685 + x681 * x685))]))))) x638 (fromList [DynamicRanked (rreplicate 22 x637), DynamicRanked (rslice 0 22 (rscanDer (\\x641 x642 -> x641 + tan x642) (\\x643 x644 x645 x646 -> rlet (cos x646) (\\x647 -> x643 + x644 * recip (x647 * x647))) (\\x649 x650 x651 -> rletInHVector (cos x651) (\\x652 -> dmkHVector (fromList [DynamicRanked x649, DynamicRanked (recip (x652 * x652) * x649)]))) x640 (rreplicate 22 x639))), DynamicRanked (rreplicate 22 x639)])) (\\x686 x687 x688 -> rletInHVector (rreverse (rscanZipDer (\\x702 [x703 @Natural @Double @[], x704 @Natural @Double @[]] -> x702) (\\x705 [x706 @Natural @Double @[], x707 @Natural @Double @[]] x708 [x709 @Natural @Double @[], x710 @Natural @Double @[]] -> x705) (\\x711 x712 [x713 @Natural @Double @[], x714 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x711, DynamicRankedDummy, DynamicRankedDummy])) x686 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\x689 x690 -> x689 + tan x690) (\\x691 x692 x693 x694 -> rlet (cos x694) (\\x695 -> x691 + x692 * recip (x695 * x695))) (\\x697 x698 x699 -> rletInHVector (cos x699) (\\x700 -> dmkHVector (fromList [DynamicRanked x697, DynamicRanked (recip (x700 * x700) * x697)]))) x688 (rreplicate 22 x687)))), DynamicRanked (rreplicate 22 x687)]))) (\\v715 -> dmkHVector (fromList [DynamicRanked (rlet (cos (rreplicate 22 x687)) (\\v716 -> rsum (recip (v716 * v716) * rgather [22] v715 (\\[i719] -> [1 + i719])))), DynamicRanked (v715 ! [0])]))) (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1)))) (\\v720 -> rletInHVector (rreverse (rscanZipDer (\\x722 [x723 @Natural @Double @[], x724 @Natural @Double @[]] -> rlet (cos (rreplicate 22 x723)) (\\v752 -> rsum (recip (v752 * v752) * rgather [22] (rscanZipDer (\\x738 [x739 @Natural @Double @[], x740 @Natural @Double @[]] -> x738) (\\x741 [x742 @Natural @Double @[], x743 @Natural @Double @[]] x744 [x745 @Natural @Double @[], x746 @Natural @Double @[]] -> x741) (\\x747 x748 [x749 @Natural @Double @[], x750 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x747, DynamicRankedDummy, DynamicRankedDummy])) x722 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\x725 x726 -> x725 + tan x726) (\\x727 x728 x729 x730 -> rlet (cos x730) (\\x731 -> x727 + x728 * recip (x731 * x731))) (\\x733 x734 x735 -> rletInHVector (cos x735) (\\x736 -> dmkHVector (fromList [DynamicRanked x733, DynamicRanked (recip (x736 * x736) * x733)]))) x724 (rreplicate 22 x723)))), DynamicRanked (rreplicate 22 x723)])) (\\[i755] -> [21 + negate i755])))) (\\x756 [x757 @Natural @Double @[], x758 @Natural @Double @[]] x759 [x760 @Natural @Double @[], x761 @Natural @Double @[]] -> rlet (rscanDer (\\x762 x763 -> x762 + tan x763) (\\x764 x765 x766 x767 -> rlet (cos x767) (\\x768 -> x764 + x765 * recip (x768 * x768))) (\\x770 x771 x772 -> rletInHVector (cos x772) (\\x773 -> dmkHVector (fromList [DynamicRanked x770, DynamicRanked (recip (x773 * x773) * x770)]))) x761 (rreplicate 22 x760)) (\\v774 -> rlet (rreverse (rslice 0 22 v774)) (\\v775 -> rlet (rscanZipDer (\\x777 [x778 @Natural @Double @[], x779 @Natural @Double @[]] -> x777) (\\x780 [x781 @Natural @Double @[], x782 @Natural @Double @[]] x783 [x784 @Natural @Double @[], x785 @Natural @Double @[]] -> x780) (\\x786 x787 [x788 @Natural @Double @[], x789 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x786, DynamicRankedDummy, DynamicRankedDummy])) x759 (fromList [DynamicRanked v775, DynamicRanked (rreplicate 22 x760)])) (\\v790 -> rlet (cos (rreplicate 22 x760)) (\\v792 -> rlet (v792 * v792) (\\v793 -> rlet (rreplicate 22 x757 * negate (sin (rreplicate 22 x760))) (\\v797 -> rsum (rgather [22] v790 (\\[i795] -> [21 + negate i795]) * ((v797 * v792 + v797 * v792) * negate (recip (v793 * v793)))) + rsum (recip v793 * rgather [22] (rscanZipDer (\\x836 [x837 @Natural @Double @[], x838 @Natural @Double @[], x839 @Natural @Double @[], x840 @Natural @Double @[], x841 @Natural @Double @[]] -> x836) (\\x842 [x843 @Natural @Double @[], x844 @Natural @Double @[], x845 @Natural @Double @[], x846 @Natural @Double @[], x847 @Natural @Double @[]] x848 [x849 @Natural @Double @[], x850 @Natural @Double @[], x851 @Natural @Double @[], x852 @Natural @Double @[], x853 @Natural @Double @[]] -> x842) (\\x854 x855 [x856 @Natural @Double @[], x857 @Natural @Double @[], x858 @Natural @Double @[], x859 @Natural @Double @[], x860 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x854, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy])) x756 (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanZipDer (\\x800 [x801 @Natural @Double @[], x802 @Natural @Double @[], x803 @Natural @Double @[]] -> rlet (cos x803) (\\x804 -> x800 + x801 * recip (x804 * x804))) (\\x806 [x807 @Natural @Double @[], x808 @Natural @Double @[], x809 @Natural @Double @[]] x810 [x811 @Natural @Double @[], x812 @Natural @Double @[], x813 @Natural @Double @[]] -> rlet (cos x813) (\\x814 -> rlet (x814 * x814) (\\x815 -> rlet (x809 * negate (sin x813)) (\\x818 -> x806 + x807 * recip x815 + ((x818 * x814 + x818 * x814) * negate (recip (x815 * x815))) * x811)))) (\\x823 x824 [x825 @Natural @Double @[], x826 @Natural @Double @[], x827 @Natural @Double @[]] -> rletInHVector (cos x827) (\\x828 -> rletInHVector (x828 * x828) (\\x829 -> rletInHVector (negate (recip (x829 * x829)) * (x825 * x823)) (\\x832 -> dmkHVector (fromList [DynamicRanked x823, DynamicRanked (recip x829 * x823), DynamicRankedDummy, DynamicRanked (negate (sin x827) * (x828 * x832 + x828 * x832))]))))) x758 (fromList [DynamicRanked (rreplicate 22 x757), DynamicRanked (rslice 0 22 v774), DynamicRanked (rreplicate 22 x760)])))), DynamicRanked (rreplicate 22 x757), DynamicRanked (rslice 0 22 v790), DynamicRanked v775, DynamicRanked (rreplicate 22 x760)])) (\\[i862] -> [21 + negate i862]))))))))) (\\x865 x866 [x867 @Natural @Double @[], x868 @Natural @Double @[]] -> rletInHVector (rscanDer (\\x874 x875 -> x874 + tan x875) (\\x876 x877 x878 x879 -> rlet (cos x879) (\\x880 -> x876 + x877 * recip (x880 * x880))) (\\x882 x883 x884 -> rletInHVector (cos x884) (\\x885 -> dmkHVector (fromList [DynamicRanked x882, DynamicRanked (recip (x885 * x885) * x882)]))) x868 (rreplicate 22 x867)) (\\v886 -> rletInHVector (rreverse (rslice 0 22 v886)) (\\v887 -> rletInHVector (rscanZipDer (\\x889 [x890 @Natural @Double @[], x891 @Natural @Double @[]] -> x889) (\\x892 [x893 @Natural @Double @[], x894 @Natural @Double @[]] x895 [x896 @Natural @Double @[], x897 @Natural @Double @[]] -> x892) (\\x898 x899 [x900 @Natural @Double @[], x901 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x898, DynamicRankedDummy, DynamicRankedDummy])) x866 (fromList [DynamicRanked v887, DynamicRanked (rreplicate 22 x867)])) (\\v902 -> rletInHVector (cos (rreplicate 22 x867)) (\\v904 -> rletInHVector (v904 * v904) (\\v905 -> rletInHVector (negate (recip (v905 * v905)) * (rgather [22] v902 (\\[i907] -> [21 + negate i907]) * rreplicate 22 x865)) (\\v909 -> rletInHVector (rreverse (rscatter [23] (recip v905 * rreplicate 22 x865) (\\[i910] -> [1 + i910]))) (\\v911 -> rletInHVector (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 22 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)))) (\\v938 -> rletInHVector (rreverse (rscanZipDer (\\x939 [x940 @Natural @Double @[], x941 @Natural @Double @[], x942 @Natural @Double @[]] -> x939 + x940) (\\x944 [x945 @Natural @Double @[], x946 @Natural @Double @[], x947 @Natural @Double @[]] x948 [x949 @Natural @Double @[], x950 @Natural @Double @[], x951 @Natural @Double @[]] -> x944 + x945) (\\x953 x954 [x955 @Natural @Double @[], x956 @Natural @Double @[], x957 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x953, DynamicRanked x953, DynamicRankedDummy, DynamicRankedDummy])) (rconst 0.0) (fromList [DynamicRanked (rreverse (rslice 1 22 v938)), DynamicRanked (rreverse (rslice 0 22 v886)), DynamicRanked (rreplicate 22 x867)]))) (\\v958 -> dmkHVector (fromList [DynamicRanked (rscanZipDer (\\x912 [x913 @Natural @Double @[], x914 @Natural @Double @[], x915 @Natural @Double @[], x916 @Natural @Double @[]] -> x912 + x913) (\\x917 [x918 @Natural @Double @[], x919 @Natural @Double @[], x920 @Natural @Double @[], x921 @Natural @Double @[]] x922 [x923 @Natural @Double @[], x924 @Natural @Double @[], x925 @Natural @Double @[], x926 @Natural @Double @[]] -> x917 + x918) (\\x928 x929 [x930 @Natural @Double @[], x931 @Natural @Double @[], x932 @Natural @Double @[], x933 @Natural @Double @[]] -> dmkHVector (fromList [DynamicRanked x928, DynamicRanked x928, DynamicRankedDummy, DynamicRankedDummy, DynamicRankedDummy])) (rconst 0.0) (fromList [DynamicRanked (rreverse (rslice 1 22 v911)), DynamicRanked (rreverse (rslice 0 22 v902)), DynamicRanked (rreverse v887), DynamicRanked (rreplicate 22 x867)]) ! [22] + v911 ! [0]), DynamicRanked (rlet (cos (rreplicate 22 x867)) (\\v959 -> rsum (recip (v959 * v959) * (rgather [22] v958 (\\[i963] -> [1 + i963]) + rgather [22] v938 (\\[i964] -> [1 + i964])))) + rsum (rreplicate 22 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 22 x867)) * (v904 * v909 + v904 * v909))), DynamicRanked (v958 ! [0] + v938 ! [0])]))))))))))) (rconst 1.0) (fromList [DynamicRanked (rreverse (rslice 0 11 v720)), DynamicRanked (rconstant (rreplicate 11 (rconst 1.1)))]))) (\\v965 -> dmkHVector (fromList [DynamicRanked (rsum (rscanZipDer (\\v986 [v987 @Natural @Double @[11], v988 @Natural @Double @[11]] -> v986) (\\v991 [v992 @Natural @Double @[11], v993 @Natural @Double @[11]] v994 [v995 @Natural @Double @[11], v996 @Natural @Double @[11]] -> v991) (\\v998 v999 [v1000 @Natural @Double @[11], v1001 @Natural @Double @[11]] -> dmkHVector (fromList [DynamicRanked v998, DynamicRanked (sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])), DynamicRanked (sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))])) (rgather [11] v965 (\\[i990] -> [1 + i990])) (fromList [DynamicRanked (rreverse (rslice 0 22 (rscanDer (\\v966 v967 -> v966 + tan v967) (\\v969 v970 v971 v972 -> rlet (cos v972) (\\v976 -> v969 + v970 * recip (v976 * v976))) (\\v978 v979 v980 -> rletInHVector (cos v980) (\\v983 -> dmkHVector (fromList [DynamicRanked v978, DynamicRanked (recip (v983 * v983) * v978)]))) (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v720))))), DynamicRanked (rreplicate 22 (rgather [11] v720 (\\[i985] -> [i985])))]) ! [22]) + v965 ! [0])])))"

testSin0FoldNestedR2SimpNestedPP :: Assertion
testSin0FoldNestedR2SimpNestedPP = do
  resetVarCounter
  let f :: forall f. ADReady f => f Double 0 -> f Double 0
      f z = rfold (\x a ->
               rfold (\x2 a2 ->
                 rfold (\x3 a3 -> x3 + tan a3)
                       a2 (rreplicate 33 x2))
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
    @?= "let v10272 = rscanDer (\\x9371 x9372 -> rfoldDer (\\x9373 x9374 -> rfoldDer (\\x9375 x9376 -> x9375 + tan x9376) (\\x9377 x9378 x9379 x9380 -> let x9381 = cos x9380 in x9377 + x9378 * recip (x9381 * x9381)) (\\x9383 x9384 x9385 -> let x9386 = cos x9385 in [x9383, recip (x9386 * x9386) * x9383]) x9374 (rreplicate 33 x9373)) (\\x9387 x9388 x9389 x9390 -> rfoldZipDer (\\x9404 [x9405, x9406, x9407] -> let x9408 = cos x9407 in x9404 + x9405 * recip (x9408 * x9408)) (\\x9410 [x9411, x9412, x9413] x9414 [x9415, x9416, x9417] -> let x9418 = cos x9417 ; x9419 = x9418 * x9418 ; x9422 = x9413 * negate (sin x9417) in x9410 + x9411 * recip x9419 + ((x9422 * x9418 + x9422 * x9418) * negate (recip (x9419 * x9419))) * x9415) (\\x9426 x9427 [x9428, x9429, x9430] -> let x9431 = cos x9430 ; x9432 = x9431 * x9431 ; x9435 = negate (recip (x9432 * x9432)) * (x9428 * x9426) in [x9426, recip x9432 * x9426, 0, negate (sin x9430) * (x9431 * x9435 + x9431 * x9435)]) x9388 [rreplicate 33 x9387, rslice 0 33 (rscanDer (\\x9391 x9392 -> x9391 + tan x9392) (\\x9393 x9394 x9395 x9396 -> let x9397 = cos x9396 in x9393 + x9394 * recip (x9397 * x9397)) (\\x9399 x9400 x9401 -> let x9402 = cos x9401 in [x9399, recip (x9402 * x9402) * x9399]) x9390 (rreplicate 33 x9389)), rreplicate 33 x9389]) (\\x9436 x9437 x9438 -> let v9465 = rreverse (rscanZipDer (\\x9452 [x9453, x9454] -> x9452) (\\x9455 [x9456, x9457] x9458 [x9459, x9460] -> x9455) (\\x9461 x9462 [x9463, x9464] -> [x9461, 0, 0]) x9436 [rreverse (rslice 0 33 (rscanDer (\\x9439 x9440 -> x9439 + tan x9440) (\\x9441 x9442 x9443 x9444 -> let x9445 = cos x9444 in x9441 + x9442 * recip (x9445 * x9445)) (\\x9447 x9448 x9449 -> let x9450 = cos x9449 in [x9447, recip (x9450 * x9450) * x9447]) x9438 (rreplicate 33 x9437))), rreplicate 33 x9437]) in [let v9466 = cos (rreplicate 33 x9437) in rsum (recip (v9466 * v9466) * rgather [33] v9465 (\\[i9469] -> [1 + i9469])), v9465 ! [0]]) x9372 (rreplicate 22 x9371)) (\\x9470 x9471 x9472 x9473 -> rfoldZipDer (\\x9572 [x9573, x9574, x9575] -> rfoldZipDer (\\x9589 [x9590, x9591, x9592] -> let x9593 = cos x9592 in x9589 + x9590 * recip (x9593 * x9593)) (\\x9595 [x9596, x9597, x9598] x9599 [x9600, x9601, x9602] -> let x9603 = cos x9602 ; x9604 = x9603 * x9603 ; x9607 = x9598 * negate (sin x9602) in x9595 + x9596 * recip x9604 + ((x9607 * x9603 + x9607 * x9603) * negate (recip (x9604 * x9604))) * x9600) (\\x9611 x9612 [x9613, x9614, x9615] -> let x9616 = cos x9615 ; x9617 = x9616 * x9616 ; x9620 = negate (recip (x9617 * x9617)) * (x9613 * x9611) in [x9611, recip x9617 * x9611, 0, negate (sin x9615) * (x9616 * x9620 + x9616 * x9620)]) x9573 [rreplicate 33 x9572, rslice 0 33 (rscanDer (\\x9576 x9577 -> x9576 + tan x9577) (\\x9578 x9579 x9580 x9581 -> let x9582 = cos x9581 in x9578 + x9579 * recip (x9582 * x9582)) (\\x9584 x9585 x9586 -> let x9587 = cos x9586 in [x9584, recip (x9587 * x9587) * x9584]) x9575 (rreplicate 33 x9574)), rreplicate 33 x9574]) (\\x9621 [x9622, x9623, x9624] x9625 [x9626, x9627, x9628] -> let v9641 = rscanDer (\\x9629 x9630 -> x9629 + tan x9630) (\\x9631 x9632 x9633 x9634 -> let x9635 = cos x9634 in x9631 + x9632 * recip (x9635 * x9635)) (\\x9637 x9638 x9639 -> let x9640 = cos x9639 in [x9637, recip (x9640 * x9640) * x9637]) x9628 (rreplicate 33 x9627) in rfoldZipDer (\\x9708 [x9709, x9710, x9711, x9712, x9713, x9714, x9715] -> let x9716 = cos x9715 ; x9717 = x9716 * x9716 ; x9720 = x9711 * negate (sin x9715) in x9708 + x9709 * recip x9717 + ((x9720 * x9716 + x9720 * x9716) * negate (recip (x9717 * x9717))) * x9713) (\\x9724 [x9725, x9726, x9727, x9728, x9729, x9730, x9731] x9732 [x9733, x9734, x9735, x9736, x9737, x9738, x9739] -> let x9740 = cos x9739 ; x9741 = x9740 * x9740 ; x9743 = negate (sin x9739) ; x9744 = x9735 * x9743 ; x9745 = x9744 * x9740 + x9744 * x9740 ; x9746 = x9741 * x9741 ; x9747 = negate (recip x9746) ; x9750 = x9731 * negate (sin x9739) ; x9751 = x9750 * x9740 + x9750 * x9740 ; x9756 = x9727 * x9743 + ((x9731 * cos x9739) * rconst -1.0) * x9735 in x9724 + x9725 * recip x9741 + (x9751 * negate (recip (x9741 * x9741))) * x9733 + ((x9756 * x9740 + x9750 * x9744 + x9756 * x9740 + x9750 * x9744) * x9747 + (((x9751 * x9741 + x9751 * x9741) * negate (recip (x9746 * x9746))) * rconst -1.0) * x9745) * x9737 + x9729 * (x9745 * x9747)) (\\x9766 x9767 [x9768, x9769, x9770, x9771, x9772, x9773, x9774] -> let x9775 = cos x9774 ; x9776 = x9775 * x9775 ; x9778 = negate (sin x9774) ; x9779 = x9770 * x9778 ; x9780 = x9779 * x9775 + x9779 * x9775 ; x9781 = x9776 * x9776 ; x9782 = negate (recip x9781) ; x9785 = x9772 * x9766 ; x9786 = negate (recip (x9781 * x9781)) * (rconst -1.0 * (x9780 * x9785)) ; x9787 = x9782 * x9785 ; x9788 = x9775 * x9787 + x9775 * x9787 ; x9789 = negate (recip (x9776 * x9776)) * (x9768 * x9766) + x9776 * x9786 + x9776 * x9786 in [x9766, recip x9776 * x9766, 0, x9778 * x9788, 0, (x9780 * x9782) * x9766, 0, negate (sin x9774) * (x9775 * x9789 + x9775 * x9789 + x9779 * x9787 + x9779 * x9787) + cos x9774 * (rconst -1.0 * (x9770 * x9788))]) x9622 [rreplicate 33 x9621, rslice 0 33 (rscanZipDer (\\x9675 [x9676, x9677, x9678] -> let x9679 = cos x9678 in x9675 + x9676 * recip (x9679 * x9679)) (\\x9681 [x9682, x9683, x9684] x9685 [x9686, x9687, x9688] -> let x9689 = cos x9688 ; x9690 = x9689 * x9689 ; x9693 = x9684 * negate (sin x9688) in x9681 + x9682 * recip x9690 + ((x9693 * x9689 + x9693 * x9689) * negate (recip (x9690 * x9690))) * x9686) (\\x9697 x9698 [x9699, x9700, x9701] -> let x9702 = cos x9701 ; x9703 = x9702 * x9702 ; x9706 = negate (recip (x9703 * x9703)) * (x9699 * x9697) in [x9697, recip x9703 * x9697, 0, negate (sin x9701) * (x9702 * x9706 + x9702 * x9706)]) x9624 [rreplicate 33 x9623, rslice 0 33 v9641, rreplicate 33 x9627]), rreplicate 33 x9623, rslice 0 33 (rscanZipDer (\\x9642 [x9643, x9644, x9645] -> let x9646 = cos x9645 in x9642 + x9643 * recip (x9646 * x9646)) (\\x9648 [x9649, x9650, x9651] x9652 [x9653, x9654, x9655] -> let x9656 = cos x9655 ; x9657 = x9656 * x9656 ; x9660 = x9651 * negate (sin x9655) in x9648 + x9649 * recip x9657 + ((x9660 * x9656 + x9660 * x9656) * negate (recip (x9657 * x9657))) * x9653) (\\x9664 x9665 [x9666, x9667, x9668] -> let x9669 = cos x9668 ; x9670 = x9669 * x9669 ; x9673 = negate (recip (x9670 * x9670)) * (x9666 * x9664) in [x9664, recip x9670 * x9664, 0, negate (sin x9668) * (x9669 * x9673 + x9669 * x9673)]) x9626 [rreplicate 33 x9625, rslice 0 33 v9641, rreplicate 33 x9627]), rreplicate 33 x9625, rslice 0 33 v9641, rreplicate 33 x9627]) (\\x9790 x9791 [x9792, x9793, x9794] -> let v9807 = rscanDer (\\x9795 x9796 -> x9795 + tan x9796) (\\x9797 x9798 x9799 x9800 -> let x9801 = cos x9800 in x9797 + x9798 * recip (x9801 * x9801)) (\\x9803 x9804 x9805 -> let x9806 = cos x9805 in [x9803, recip (x9806 * x9806) * x9803]) x9794 (rreplicate 33 x9793) ; v9862 = rreverse (rscanZipDer (\\x9841 [x9842, x9843, x9844, x9845] -> x9841) (\\x9846 [x9847, x9848, x9849, x9850] x9851 [x9852, x9853, x9854, x9855] -> x9846) (\\x9856 x9857 [x9858, x9859, x9860, x9861] -> [x9856, 0, 0, 0, 0]) x9790 [rreverse (rslice 0 33 (rscanZipDer (\\x9808 [x9809, x9810, x9811] -> let x9812 = cos x9811 in x9808 + x9809 * recip (x9812 * x9812)) (\\x9814 [x9815, x9816, x9817] x9818 [x9819, x9820, x9821] -> let x9822 = cos x9821 ; x9823 = x9822 * x9822 ; x9826 = x9817 * negate (sin x9821) in x9814 + x9815 * recip x9823 + ((x9826 * x9822 + x9826 * x9822) * negate (recip (x9823 * x9823))) * x9819) (\\x9830 x9831 [x9832, x9833, x9834] -> let x9835 = cos x9834 ; x9836 = x9835 * x9835 ; x9839 = negate (recip (x9836 * x9836)) * (x9832 * x9830) in [x9830, recip x9836 * x9830, 0, negate (sin x9834) * (x9835 * x9839 + x9835 * x9839)]) x9792 [rreplicate 33 x9791, rslice 0 33 v9807, rreplicate 33 x9793])), rreplicate 33 x9791, rreverse (rslice 0 33 v9807), rreplicate 33 x9793]) ; v9863 = cos (rreplicate 33 x9793) ; v9864 = v9863 * v9863 ; v9868 = negate (recip (v9864 * v9864)) * (rreplicate 33 x9791 * rgather [33] v9862 (\\[i9867] -> [1 + i9867])) ; v9874 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v9893 = rreverse (rscanZipDer (\\x9875 [x9876, x9877, x9878] -> x9875 + x9876) (\\x9880 [x9881, x9882, x9883] x9884 [x9885, x9886, x9887] -> x9880 + x9881) (\\x9888 x9889 [x9890, x9891, x9892] -> [x9888, x9888, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v9874), rreverse (rslice 0 33 v9807), rreplicate 33 x9793]) in [rsum (recip v9864 * rgather [33] v9862 (\\[i9871] -> [1 + i9871])), v9862 ! [0], (let v9894 = cos (rreplicate 33 x9793) in rsum (recip (v9894 * v9894) * (rgather [33] v9893 (\\[i9898] -> [1 + i9898]) + rgather [33] v9874 (\\[i9899] -> [1 + i9899])))) + rsum (negate (sin (rreplicate 33 x9793)) * (v9863 * v9868 + v9863 * v9868)), v9893 ! [0] + v9874 ! [0]]) x9471 [rreplicate 22 x9470, rslice 0 22 (rscanDer (\\x9474 x9475 -> rfoldDer (\\x9476 x9477 -> x9476 + tan x9477) (\\x9478 x9479 x9480 x9481 -> let x9482 = cos x9481 in x9478 + x9479 * recip (x9482 * x9482)) (\\x9484 x9485 x9486 -> let x9487 = cos x9486 in [x9484, recip (x9487 * x9487) * x9484]) x9475 (rreplicate 33 x9474)) (\\x9488 x9489 x9490 x9491 -> rfoldZipDer (\\x9505 [x9506, x9507, x9508] -> let x9509 = cos x9508 in x9505 + x9506 * recip (x9509 * x9509)) (\\x9511 [x9512, x9513, x9514] x9515 [x9516, x9517, x9518] -> let x9519 = cos x9518 ; x9520 = x9519 * x9519 ; x9523 = x9514 * negate (sin x9518) in x9511 + x9512 * recip x9520 + ((x9523 * x9519 + x9523 * x9519) * negate (recip (x9520 * x9520))) * x9516) (\\x9527 x9528 [x9529, x9530, x9531] -> let x9532 = cos x9531 ; x9533 = x9532 * x9532 ; x9536 = negate (recip (x9533 * x9533)) * (x9529 * x9527) in [x9527, recip x9533 * x9527, 0, negate (sin x9531) * (x9532 * x9536 + x9532 * x9536)]) x9489 [rreplicate 33 x9488, rslice 0 33 (rscanDer (\\x9492 x9493 -> x9492 + tan x9493) (\\x9494 x9495 x9496 x9497 -> let x9498 = cos x9497 in x9494 + x9495 * recip (x9498 * x9498)) (\\x9500 x9501 x9502 -> let x9503 = cos x9502 in [x9500, recip (x9503 * x9503) * x9500]) x9491 (rreplicate 33 x9490)), rreplicate 33 x9490]) (\\x9537 x9538 x9539 -> let v9566 = rreverse (rscanZipDer (\\x9553 [x9554, x9555] -> x9553) (\\x9556 [x9557, x9558] x9559 [x9560, x9561] -> x9556) (\\x9562 x9563 [x9564, x9565] -> [x9562, 0, 0]) x9537 [rreverse (rslice 0 33 (rscanDer (\\x9540 x9541 -> x9540 + tan x9541) (\\x9542 x9543 x9544 x9545 -> let x9546 = cos x9545 in x9542 + x9543 * recip (x9546 * x9546)) (\\x9548 x9549 x9550 -> let x9551 = cos x9550 in [x9548, recip (x9551 * x9551) * x9548]) x9539 (rreplicate 33 x9538))), rreplicate 33 x9538]) in [let v9567 = cos (rreplicate 33 x9538) in rsum (recip (v9567 * v9567) * rgather [33] v9566 (\\[i9570] -> [1 + i9570])), v9566 ! [0]]) x9473 (rreplicate 22 x9472)), rreplicate 22 x9472]) (\\x9900 x9901 x9902 -> let v10000 = rscanDer (\\x9903 x9904 -> rfoldDer (\\x9905 x9906 -> x9905 + tan x9906) (\\x9907 x9908 x9909 x9910 -> let x9911 = cos x9910 in x9907 + x9908 * recip (x9911 * x9911)) (\\x9913 x9914 x9915 -> let x9916 = cos x9915 in [x9913, recip (x9916 * x9916) * x9913]) x9904 (rreplicate 33 x9903)) (\\x9917 x9918 x9919 x9920 -> rfoldZipDer (\\x9934 [x9935, x9936, x9937] -> let x9938 = cos x9937 in x9934 + x9935 * recip (x9938 * x9938)) (\\x9940 [x9941, x9942, x9943] x9944 [x9945, x9946, x9947] -> let x9948 = cos x9947 ; x9949 = x9948 * x9948 ; x9952 = x9943 * negate (sin x9947) in x9940 + x9941 * recip x9949 + ((x9952 * x9948 + x9952 * x9948) * negate (recip (x9949 * x9949))) * x9945) (\\x9956 x9957 [x9958, x9959, x9960] -> let x9961 = cos x9960 ; x9962 = x9961 * x9961 ; x9965 = negate (recip (x9962 * x9962)) * (x9958 * x9956) in [x9956, recip x9962 * x9956, 0, negate (sin x9960) * (x9961 * x9965 + x9961 * x9965)]) x9918 [rreplicate 33 x9917, rslice 0 33 (rscanDer (\\x9921 x9922 -> x9921 + tan x9922) (\\x9923 x9924 x9925 x9926 -> let x9927 = cos x9926 in x9923 + x9924 * recip (x9927 * x9927)) (\\x9929 x9930 x9931 -> let x9932 = cos x9931 in [x9929, recip (x9932 * x9932) * x9929]) x9920 (rreplicate 33 x9919)), rreplicate 33 x9919]) (\\x9966 x9967 x9968 -> let v9995 = rreverse (rscanZipDer (\\x9982 [x9983, x9984] -> x9982) (\\x9985 [x9986, x9987] x9988 [x9989, x9990] -> x9985) (\\x9991 x9992 [x9993, x9994] -> [x9991, 0, 0]) x9966 [rreverse (rslice 0 33 (rscanDer (\\x9969 x9970 -> x9969 + tan x9970) (\\x9971 x9972 x9973 x9974 -> let x9975 = cos x9974 in x9971 + x9972 * recip (x9975 * x9975)) (\\x9977 x9978 x9979 -> let x9980 = cos x9979 in [x9977, recip (x9980 * x9980) * x9977]) x9968 (rreplicate 33 x9967))), rreplicate 33 x9967]) in [let v9996 = cos (rreplicate 33 x9967) in rsum (recip (v9996 * v9996) * rgather [33] v9995 (\\[i9999] -> [1 + i9999])), v9995 ! [0]]) x9902 (rreplicate 22 x9901) ; v10233 = rreverse (rscanZipDer (\\x10001 [x10002, x10003] -> let v10031 = cos (rreplicate 33 x10002) in rsum (recip (v10031 * v10031) * rgather [33] (rscanZipDer (\\x10017 [x10018, x10019] -> x10017) (\\x10020 [x10021, x10022] x10023 [x10024, x10025] -> x10020) (\\x10026 x10027 [x10028, x10029] -> [x10026, 0, 0]) x10001 [rreverse (rslice 0 33 (rscanDer (\\x10004 x10005 -> x10004 + tan x10005) (\\x10006 x10007 x10008 x10009 -> let x10010 = cos x10009 in x10006 + x10007 * recip (x10010 * x10010)) (\\x10012 x10013 x10014 -> let x10015 = cos x10014 in [x10012, recip (x10015 * x10015) * x10012]) x10003 (rreplicate 33 x10002))), rreplicate 33 x10002]) (\\[i10034] -> [32 + negate i10034]))) (\\x10035 [x10036, x10037] x10038 [x10039, x10040] -> let v10053 = rscanDer (\\x10041 x10042 -> x10041 + tan x10042) (\\x10043 x10044 x10045 x10046 -> let x10047 = cos x10046 in x10043 + x10044 * recip (x10047 * x10047)) (\\x10049 x10050 x10051 -> let x10052 = cos x10051 in [x10049, recip (x10052 * x10052) * x10049]) x10040 (rreplicate 33 x10039) ; v10054 = rreverse (rslice 0 33 v10053) ; v10069 = rscanZipDer (\\x10056 [x10057, x10058] -> x10056) (\\x10059 [x10060, x10061] x10062 [x10063, x10064] -> x10059) (\\x10065 x10066 [x10067, x10068] -> [x10065, 0, 0]) x10038 [v10054, rreplicate 33 x10039] ; v10071 = cos (rreplicate 33 x10039) ; v10072 = v10071 * v10071 ; v10076 = rreplicate 33 x10036 * negate (sin (rreplicate 33 x10039)) in rsum (rgather [33] v10069 (\\[i10074] -> [32 + negate i10074]) * ((v10076 * v10071 + v10076 * v10071) * negate (recip (v10072 * v10072)))) + rsum (recip v10072 * rgather [33] (rscanZipDer (\\x10114 [x10115, x10116, x10117, x10118, x10119] -> x10114) (\\x10120 [x10121, x10122, x10123, x10124, x10125] x10126 [x10127, x10128, x10129, x10130, x10131] -> x10120) (\\x10132 x10133 [x10134, x10135, x10136, x10137, x10138] -> [x10132, 0, 0, 0, 0, 0]) x10035 [rreverse (rslice 0 33 (rscanZipDer (\\x10079 [x10080, x10081, x10082] -> let x10083 = cos x10082 in x10079 + x10080 * recip (x10083 * x10083)) (\\x10085 [x10086, x10087, x10088] x10089 [x10090, x10091, x10092] -> let x10093 = cos x10092 ; x10094 = x10093 * x10093 ; x10097 = x10088 * negate (sin x10092) in x10085 + x10086 * recip x10094 + ((x10097 * x10093 + x10097 * x10093) * negate (recip (x10094 * x10094))) * x10090) (\\x10101 x10102 [x10103, x10104, x10105] -> let x10106 = cos x10105 ; x10107 = x10106 * x10106 ; x10110 = negate (recip (x10107 * x10107)) * (x10103 * x10101) in [x10101, recip x10107 * x10101, 0, negate (sin x10105) * (x10106 * x10110 + x10106 * x10110)]) x10037 [rreplicate 33 x10036, rslice 0 33 v10053, rreplicate 33 x10039])), rreplicate 33 x10036, rslice 0 33 v10069, v10054, rreplicate 33 x10039]) (\\[i10140] -> [32 + negate i10140]))) (\\x10142 x10143 [x10144, x10145] -> let v10158 = rscanDer (\\x10146 x10147 -> x10146 + tan x10147) (\\x10148 x10149 x10150 x10151 -> let x10152 = cos x10151 in x10148 + x10149 * recip (x10152 * x10152)) (\\x10154 x10155 x10156 -> let x10157 = cos x10156 in [x10154, recip (x10157 * x10157) * x10154]) x10145 (rreplicate 33 x10144) ; v10159 = rreverse (rslice 0 33 v10158) ; v10174 = rscanZipDer (\\x10161 [x10162, x10163] -> x10161) (\\x10164 [x10165, x10166] x10167 [x10168, x10169] -> x10164) (\\x10170 x10171 [x10172, x10173] -> [x10170, 0, 0]) x10143 [v10159, rreplicate 33 x10144] ; v10176 = cos (rreplicate 33 x10144) ; v10177 = v10176 * v10176 ; v10181 = negate (recip (v10177 * v10177)) * (rgather [33] v10174 (\\[i10179] -> [32 + negate i10179]) * rreplicate 33 x10142) ; v10183 = rreverse (rscatter [34] (recip v10177 * rreplicate 33 x10142) (\\[i10182] -> [1 + i10182])) ; v10207 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v10226 = rreverse (rscanZipDer (\\x10208 [x10209, x10210, x10211] -> x10208 + x10209) (\\x10213 [x10214, x10215, x10216] x10217 [x10218, x10219, x10220] -> x10213 + x10214) (\\x10221 x10222 [x10223, x10224, x10225] -> [x10221, x10221, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10207), rreverse (rslice 0 33 v10158), rreplicate 33 x10144]) in [rscanZipDer (\\x10184 [x10185, x10186, x10187, x10188] -> x10184 + x10185) (\\x10189 [x10190, x10191, x10192, x10193] x10194 [x10195, x10196, x10197, x10198] -> x10189 + x10190) (\\x10199 x10200 [x10201, x10202, x10203, x10204] -> [x10199, x10199, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10183), rreverse (rslice 0 33 v10174), rreverse v10159, rreplicate 33 x10144] ! [33] + v10183 ! [0], (let v10227 = cos (rreplicate 33 x10144) in rsum (recip (v10227 * v10227) * (rgather [33] v10226 (\\[i10231] -> [1 + i10231]) + rgather [33] v10207 (\\[i10232] -> [1 + i10232])))) + sconst @[] 0.0 * rconst 33.0 + rsum (negate (sin (rreplicate 33 x10144)) * (v10176 * v10181 + v10176 * v10181)), v10226 ! [0] + v10207 ! [0]]) x9900 [rreverse (rslice 0 22 v10000), rreplicate 22 x9901]) in [rsum (rscanZipDer (\\v10248 [v10249, v10250] -> v10248) (\\v10252 [v10253, v10254] v10255 [v10256, v10257] -> v10252) (\\v10258 v10259 [v10260, v10261] -> [v10258, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v10233 (\\[i10251] -> [1 + i10251])) [rreverse (rslice 0 33 (rscanDer (\\v10234 v10235 -> v10234 + tan v10235) (\\v10236 v10237 v10238 v10239 -> let v10240 = cos v10239 in v10236 + v10237 * recip (v10240 * v10240)) (\\v10242 v10243 v10244 -> let v10245 = cos v10244 in [v10242, recip (v10245 * v10245) * v10242]) (rreplicate 22 x9901) (rreplicate 33 (rslice 0 22 v10000)))), rreplicate 33 (rgather [22] v10000 (\\[i10247] -> [i10247]))] ! [33]), v10233 ! [0]]) (rconst 1.1) (rconstant (rreplicate 11 (rconst 1.1))) ; v15079 = rreverse (rscanZipDer (\\x10274 [x10275, x10276] -> let v10374 = rscanDer (\\x10277 x10278 -> rfoldDer (\\x10279 x10280 -> x10279 + tan x10280) (\\x10281 x10282 x10283 x10284 -> let x10285 = cos x10284 in x10281 + x10282 * recip (x10285 * x10285)) (\\x10287 x10288 x10289 -> let x10290 = cos x10289 in [x10287, recip (x10290 * x10290) * x10287]) x10278 (rreplicate 33 x10277)) (\\x10291 x10292 x10293 x10294 -> rfoldZipDer (\\x10308 [x10309, x10310, x10311] -> let x10312 = cos x10311 in x10308 + x10309 * recip (x10312 * x10312)) (\\x10314 [x10315, x10316, x10317] x10318 [x10319, x10320, x10321] -> let x10322 = cos x10321 ; x10323 = x10322 * x10322 ; x10326 = x10317 * negate (sin x10321) in x10314 + x10315 * recip x10323 + ((x10326 * x10322 + x10326 * x10322) * negate (recip (x10323 * x10323))) * x10319) (\\x10330 x10331 [x10332, x10333, x10334] -> let x10335 = cos x10334 ; x10336 = x10335 * x10335 ; x10339 = negate (recip (x10336 * x10336)) * (x10332 * x10330) in [x10330, recip x10336 * x10330, 0, negate (sin x10334) * (x10335 * x10339 + x10335 * x10339)]) x10292 [rreplicate 33 x10291, rslice 0 33 (rscanDer (\\x10295 x10296 -> x10295 + tan x10296) (\\x10297 x10298 x10299 x10300 -> let x10301 = cos x10300 in x10297 + x10298 * recip (x10301 * x10301)) (\\x10303 x10304 x10305 -> let x10306 = cos x10305 in [x10303, recip (x10306 * x10306) * x10303]) x10294 (rreplicate 33 x10293)), rreplicate 33 x10293]) (\\x10340 x10341 x10342 -> let v10369 = rreverse (rscanZipDer (\\x10356 [x10357, x10358] -> x10356) (\\x10359 [x10360, x10361] x10362 [x10363, x10364] -> x10359) (\\x10365 x10366 [x10367, x10368] -> [x10365, 0, 0]) x10340 [rreverse (rslice 0 33 (rscanDer (\\x10343 x10344 -> x10343 + tan x10344) (\\x10345 x10346 x10347 x10348 -> let x10349 = cos x10348 in x10345 + x10346 * recip (x10349 * x10349)) (\\x10351 x10352 x10353 -> let x10354 = cos x10353 in [x10351, recip (x10354 * x10354) * x10351]) x10342 (rreplicate 33 x10341))), rreplicate 33 x10341]) in [let v10370 = cos (rreplicate 33 x10341) in rsum (recip (v10370 * v10370) * rgather [33] v10369 (\\[i10373] -> [1 + i10373])), v10369 ! [0]]) x10276 (rreplicate 22 x10275) in rsum (rscanZipDer (\\v10622 [v10623, v10624] -> v10622) (\\v10626 [v10627, v10628] v10629 [v10630, v10631] -> v10626) (\\v10632 v10633 [v10634, v10635] -> [v10632, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] (rscanZipDer (\\x10375 [x10376, x10377] -> let v10405 = cos (rreplicate 33 x10376) in rsum (recip (v10405 * v10405) * rgather [33] (rscanZipDer (\\x10391 [x10392, x10393] -> x10391) (\\x10394 [x10395, x10396] x10397 [x10398, x10399] -> x10394) (\\x10400 x10401 [x10402, x10403] -> [x10400, 0, 0]) x10375 [rreverse (rslice 0 33 (rscanDer (\\x10378 x10379 -> x10378 + tan x10379) (\\x10380 x10381 x10382 x10383 -> let x10384 = cos x10383 in x10380 + x10381 * recip (x10384 * x10384)) (\\x10386 x10387 x10388 -> let x10389 = cos x10388 in [x10386, recip (x10389 * x10389) * x10386]) x10377 (rreplicate 33 x10376))), rreplicate 33 x10376]) (\\[i10408] -> [32 + negate i10408]))) (\\x10409 [x10410, x10411] x10412 [x10413, x10414] -> let v10427 = rscanDer (\\x10415 x10416 -> x10415 + tan x10416) (\\x10417 x10418 x10419 x10420 -> let x10421 = cos x10420 in x10417 + x10418 * recip (x10421 * x10421)) (\\x10423 x10424 x10425 -> let x10426 = cos x10425 in [x10423, recip (x10426 * x10426) * x10423]) x10414 (rreplicate 33 x10413) ; v10428 = rreverse (rslice 0 33 v10427) ; v10443 = rscanZipDer (\\x10430 [x10431, x10432] -> x10430) (\\x10433 [x10434, x10435] x10436 [x10437, x10438] -> x10433) (\\x10439 x10440 [x10441, x10442] -> [x10439, 0, 0]) x10412 [v10428, rreplicate 33 x10413] ; v10445 = cos (rreplicate 33 x10413) ; v10446 = v10445 * v10445 ; v10450 = rreplicate 33 x10410 * negate (sin (rreplicate 33 x10413)) in rsum (rgather [33] v10443 (\\[i10448] -> [32 + negate i10448]) * ((v10450 * v10445 + v10450 * v10445) * negate (recip (v10446 * v10446)))) + rsum (recip v10446 * rgather [33] (rscanZipDer (\\x10488 [x10489, x10490, x10491, x10492, x10493] -> x10488) (\\x10494 [x10495, x10496, x10497, x10498, x10499] x10500 [x10501, x10502, x10503, x10504, x10505] -> x10494) (\\x10506 x10507 [x10508, x10509, x10510, x10511, x10512] -> [x10506, 0, 0, 0, 0, 0]) x10409 [rreverse (rslice 0 33 (rscanZipDer (\\x10453 [x10454, x10455, x10456] -> let x10457 = cos x10456 in x10453 + x10454 * recip (x10457 * x10457)) (\\x10459 [x10460, x10461, x10462] x10463 [x10464, x10465, x10466] -> let x10467 = cos x10466 ; x10468 = x10467 * x10467 ; x10471 = x10462 * negate (sin x10466) in x10459 + x10460 * recip x10468 + ((x10471 * x10467 + x10471 * x10467) * negate (recip (x10468 * x10468))) * x10464) (\\x10475 x10476 [x10477, x10478, x10479] -> let x10480 = cos x10479 ; x10481 = x10480 * x10480 ; x10484 = negate (recip (x10481 * x10481)) * (x10477 * x10475) in [x10475, recip x10481 * x10475, 0, negate (sin x10479) * (x10480 * x10484 + x10480 * x10484)]) x10411 [rreplicate 33 x10410, rslice 0 33 v10427, rreplicate 33 x10413])), rreplicate 33 x10410, rslice 0 33 v10443, v10428, rreplicate 33 x10413]) (\\[i10514] -> [32 + negate i10514]))) (\\x10516 x10517 [x10518, x10519] -> let v10532 = rscanDer (\\x10520 x10521 -> x10520 + tan x10521) (\\x10522 x10523 x10524 x10525 -> let x10526 = cos x10525 in x10522 + x10523 * recip (x10526 * x10526)) (\\x10528 x10529 x10530 -> let x10531 = cos x10530 in [x10528, recip (x10531 * x10531) * x10528]) x10519 (rreplicate 33 x10518) ; v10533 = rreverse (rslice 0 33 v10532) ; v10548 = rscanZipDer (\\x10535 [x10536, x10537] -> x10535) (\\x10538 [x10539, x10540] x10541 [x10542, x10543] -> x10538) (\\x10544 x10545 [x10546, x10547] -> [x10544, 0, 0]) x10517 [v10533, rreplicate 33 x10518] ; v10550 = cos (rreplicate 33 x10518) ; v10551 = v10550 * v10550 ; v10555 = negate (recip (v10551 * v10551)) * (rgather [33] v10548 (\\[i10553] -> [32 + negate i10553]) * rreplicate 33 x10516) ; v10557 = rreverse (rscatter [34] (recip v10551 * rreplicate 33 x10516) (\\[i10556] -> [1 + i10556])) ; v10581 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v10600 = rreverse (rscanZipDer (\\x10582 [x10583, x10584, x10585] -> x10582 + x10583) (\\x10587 [x10588, x10589, x10590] x10591 [x10592, x10593, x10594] -> x10587 + x10588) (\\x10595 x10596 [x10597, x10598, x10599] -> [x10595, x10595, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10581), rreverse (rslice 0 33 v10532), rreplicate 33 x10518]) in [rscanZipDer (\\x10558 [x10559, x10560, x10561, x10562] -> x10558 + x10559) (\\x10563 [x10564, x10565, x10566, x10567] x10568 [x10569, x10570, x10571, x10572] -> x10563 + x10564) (\\x10573 x10574 [x10575, x10576, x10577, x10578] -> [x10573, x10573, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10557), rreverse (rslice 0 33 v10548), rreverse v10533, rreplicate 33 x10518] ! [33] + v10557 ! [0], (let v10601 = cos (rreplicate 33 x10518) in rsum (recip (v10601 * v10601) * (rgather [33] v10600 (\\[i10605] -> [1 + i10605]) + rgather [33] v10581 (\\[i10606] -> [1 + i10606])))) + sconst @[] 0.0 * rconst 33.0 + rsum (negate (sin (rreplicate 33 x10518)) * (v10550 * v10555 + v10550 * v10555)), v10600 ! [0] + v10581 ! [0]]) x10274 [rreverse (rslice 0 22 v10374), rreplicate 22 x10275]) (\\[i10625] -> [21 + negate i10625])) [rreverse (rslice 0 33 (rscanDer (\\v10608 v10609 -> v10608 + tan v10609) (\\v10610 v10611 v10612 v10613 -> let v10614 = cos v10613 in v10610 + v10611 * recip (v10614 * v10614)) (\\v10616 v10617 v10618 -> let v10619 = cos v10618 in [v10616, recip (v10619 * v10619) * v10616]) (rreplicate 22 x10275) (rreplicate 33 (rslice 0 22 v10374)))), rreplicate 33 (rgather [22] v10374 (\\[i10621] -> [i10621]))] ! [33])) (\\x10646 [x10647, x10648] x10649 [x10650, x10651] -> let v10749 = rscanDer (\\x10652 x10653 -> rfoldDer (\\x10654 x10655 -> x10654 + tan x10655) (\\x10656 x10657 x10658 x10659 -> let x10660 = cos x10659 in x10656 + x10657 * recip (x10660 * x10660)) (\\x10662 x10663 x10664 -> let x10665 = cos x10664 in [x10662, recip (x10665 * x10665) * x10662]) x10653 (rreplicate 33 x10652)) (\\x10666 x10667 x10668 x10669 -> rfoldZipDer (\\x10683 [x10684, x10685, x10686] -> let x10687 = cos x10686 in x10683 + x10684 * recip (x10687 * x10687)) (\\x10689 [x10690, x10691, x10692] x10693 [x10694, x10695, x10696] -> let x10697 = cos x10696 ; x10698 = x10697 * x10697 ; x10701 = x10692 * negate (sin x10696) in x10689 + x10690 * recip x10698 + ((x10701 * x10697 + x10701 * x10697) * negate (recip (x10698 * x10698))) * x10694) (\\x10705 x10706 [x10707, x10708, x10709] -> let x10710 = cos x10709 ; x10711 = x10710 * x10710 ; x10714 = negate (recip (x10711 * x10711)) * (x10707 * x10705) in [x10705, recip x10711 * x10705, 0, negate (sin x10709) * (x10710 * x10714 + x10710 * x10714)]) x10667 [rreplicate 33 x10666, rslice 0 33 (rscanDer (\\x10670 x10671 -> x10670 + tan x10671) (\\x10672 x10673 x10674 x10675 -> let x10676 = cos x10675 in x10672 + x10673 * recip (x10676 * x10676)) (\\x10678 x10679 x10680 -> let x10681 = cos x10680 in [x10678, recip (x10681 * x10681) * x10678]) x10669 (rreplicate 33 x10668)), rreplicate 33 x10668]) (\\x10715 x10716 x10717 -> let v10744 = rreverse (rscanZipDer (\\x10731 [x10732, x10733] -> x10731) (\\x10734 [x10735, x10736] x10737 [x10738, x10739] -> x10734) (\\x10740 x10741 [x10742, x10743] -> [x10740, 0, 0]) x10715 [rreverse (rslice 0 33 (rscanDer (\\x10718 x10719 -> x10718 + tan x10719) (\\x10720 x10721 x10722 x10723 -> let x10724 = cos x10723 in x10720 + x10721 * recip (x10724 * x10724)) (\\x10726 x10727 x10728 -> let x10729 = cos x10728 in [x10726, recip (x10729 * x10729) * x10726]) x10717 (rreplicate 33 x10716))), rreplicate 33 x10716]) in [let v10745 = cos (rreplicate 33 x10716) in rsum (recip (v10745 * v10745) * rgather [33] v10744 (\\[i10748] -> [1 + i10748])), v10744 ! [0]]) x10651 (rreplicate 22 x10650) ; v10750 = rreverse (rslice 0 22 v10749) ; v10984 = rscanZipDer (\\x10752 [x10753, x10754] -> let v10782 = cos (rreplicate 33 x10753) in rsum (recip (v10782 * v10782) * rgather [33] (rscanZipDer (\\x10768 [x10769, x10770] -> x10768) (\\x10771 [x10772, x10773] x10774 [x10775, x10776] -> x10771) (\\x10777 x10778 [x10779, x10780] -> [x10777, 0, 0]) x10752 [rreverse (rslice 0 33 (rscanDer (\\x10755 x10756 -> x10755 + tan x10756) (\\x10757 x10758 x10759 x10760 -> let x10761 = cos x10760 in x10757 + x10758 * recip (x10761 * x10761)) (\\x10763 x10764 x10765 -> let x10766 = cos x10765 in [x10763, recip (x10766 * x10766) * x10763]) x10754 (rreplicate 33 x10753))), rreplicate 33 x10753]) (\\[i10785] -> [32 + negate i10785]))) (\\x10786 [x10787, x10788] x10789 [x10790, x10791] -> let v10804 = rscanDer (\\x10792 x10793 -> x10792 + tan x10793) (\\x10794 x10795 x10796 x10797 -> let x10798 = cos x10797 in x10794 + x10795 * recip (x10798 * x10798)) (\\x10800 x10801 x10802 -> let x10803 = cos x10802 in [x10800, recip (x10803 * x10803) * x10800]) x10791 (rreplicate 33 x10790) ; v10805 = rreverse (rslice 0 33 v10804) ; v10820 = rscanZipDer (\\x10807 [x10808, x10809] -> x10807) (\\x10810 [x10811, x10812] x10813 [x10814, x10815] -> x10810) (\\x10816 x10817 [x10818, x10819] -> [x10816, 0, 0]) x10789 [v10805, rreplicate 33 x10790] ; v10822 = cos (rreplicate 33 x10790) ; v10823 = v10822 * v10822 ; v10827 = rreplicate 33 x10787 * negate (sin (rreplicate 33 x10790)) in rsum (rgather [33] v10820 (\\[i10825] -> [32 + negate i10825]) * ((v10827 * v10822 + v10827 * v10822) * negate (recip (v10823 * v10823)))) + rsum (recip v10823 * rgather [33] (rscanZipDer (\\x10865 [x10866, x10867, x10868, x10869, x10870] -> x10865) (\\x10871 [x10872, x10873, x10874, x10875, x10876] x10877 [x10878, x10879, x10880, x10881, x10882] -> x10871) (\\x10883 x10884 [x10885, x10886, x10887, x10888, x10889] -> [x10883, 0, 0, 0, 0, 0]) x10786 [rreverse (rslice 0 33 (rscanZipDer (\\x10830 [x10831, x10832, x10833] -> let x10834 = cos x10833 in x10830 + x10831 * recip (x10834 * x10834)) (\\x10836 [x10837, x10838, x10839] x10840 [x10841, x10842, x10843] -> let x10844 = cos x10843 ; x10845 = x10844 * x10844 ; x10848 = x10839 * negate (sin x10843) in x10836 + x10837 * recip x10845 + ((x10848 * x10844 + x10848 * x10844) * negate (recip (x10845 * x10845))) * x10841) (\\x10852 x10853 [x10854, x10855, x10856] -> let x10857 = cos x10856 ; x10858 = x10857 * x10857 ; x10861 = negate (recip (x10858 * x10858)) * (x10854 * x10852) in [x10852, recip x10858 * x10852, 0, negate (sin x10856) * (x10857 * x10861 + x10857 * x10861)]) x10788 [rreplicate 33 x10787, rslice 0 33 v10804, rreplicate 33 x10790])), rreplicate 33 x10787, rslice 0 33 v10820, v10805, rreplicate 33 x10790]) (\\[i10891] -> [32 + negate i10891]))) (\\x10893 x10894 [x10895, x10896] -> let v10909 = rscanDer (\\x10897 x10898 -> x10897 + tan x10898) (\\x10899 x10900 x10901 x10902 -> let x10903 = cos x10902 in x10899 + x10900 * recip (x10903 * x10903)) (\\x10905 x10906 x10907 -> let x10908 = cos x10907 in [x10905, recip (x10908 * x10908) * x10905]) x10896 (rreplicate 33 x10895) ; v10910 = rreverse (rslice 0 33 v10909) ; v10925 = rscanZipDer (\\x10912 [x10913, x10914] -> x10912) (\\x10915 [x10916, x10917] x10918 [x10919, x10920] -> x10915) (\\x10921 x10922 [x10923, x10924] -> [x10921, 0, 0]) x10894 [v10910, rreplicate 33 x10895] ; v10927 = cos (rreplicate 33 x10895) ; v10928 = v10927 * v10927 ; v10932 = negate (recip (v10928 * v10928)) * (rgather [33] v10925 (\\[i10930] -> [32 + negate i10930]) * rreplicate 33 x10893) ; v10934 = rreverse (rscatter [34] (recip v10928 * rreplicate 33 x10893) (\\[i10933] -> [1 + i10933])) ; v10958 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v10977 = rreverse (rscanZipDer (\\x10959 [x10960, x10961, x10962] -> x10959 + x10960) (\\x10964 [x10965, x10966, x10967] x10968 [x10969, x10970, x10971] -> x10964 + x10965) (\\x10972 x10973 [x10974, x10975, x10976] -> [x10972, x10972, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10958), rreverse (rslice 0 33 v10909), rreplicate 33 x10895]) in [rscanZipDer (\\x10935 [x10936, x10937, x10938, x10939] -> x10935 + x10936) (\\x10940 [x10941, x10942, x10943, x10944] x10945 [x10946, x10947, x10948, x10949] -> x10940 + x10941) (\\x10950 x10951 [x10952, x10953, x10954, x10955] -> [x10950, x10950, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v10934), rreverse (rslice 0 33 v10925), rreverse v10910, rreplicate 33 x10895] ! [33] + v10934 ! [0], (let v10978 = cos (rreplicate 33 x10895) in rsum (recip (v10978 * v10978) * (rgather [33] v10977 (\\[i10982] -> [1 + i10982]) + rgather [33] v10958 (\\[i10983] -> [1 + i10983])))) + sconst @[] 0.0 * rconst 33.0 + rsum (negate (sin (rreplicate 33 x10895)) * (v10927 * v10932 + v10927 * v10932)), v10977 ! [0] + v10958 ! [0]]) x10649 [v10750, rreplicate 22 x10650] ; m10998 = rscanDer (\\v10986 v10987 -> v10986 + tan v10987) (\\v10988 v10989 v10990 v10991 -> let v10992 = cos v10991 in v10988 + v10989 * recip (v10992 * v10992)) (\\v10994 v10995 v10996 -> let v10997 = cos v10996 in [v10994, recip (v10997 * v10997) * v10994]) (rreplicate 22 x10650) (rreplicate 33 (rslice 0 22 v10749)) ; m10999 = rreverse (rslice 0 33 m10998) ; m11000 = rreplicate 33 (rgather [22] v10749 (\\[i11001] -> [i11001])) in rsum (rscanZipDer (\\v13013 [v13014, v13015, v13016, v13017, v13018] -> v13013) (\\v13019 [v13020, v13021, v13022, v13023, v13024] v13025 [v13026, v13027, v13028, v13029, v13030] -> v13019) (\\v13031 v13032 [v13033, v13034, v13035, v13036, v13037] -> [v13031, 0, 0, 0, 0, 0]) (rgather [22] (rscanZipDer (\\x11379 [x11380, x11381, x11382, x11383, x11384] -> let v11397 = rscanDer (\\x11385 x11386 -> x11385 + tan x11386) (\\x11387 x11388 x11389 x11390 -> let x11391 = cos x11390 in x11387 + x11388 * recip (x11391 * x11391)) (\\x11393 x11394 x11395 -> let x11396 = cos x11395 in [x11393, recip (x11396 * x11396) * x11393]) x11384 (rreplicate 33 x11383) ; v11398 = rreverse (rslice 0 33 v11397) ; v11413 = rscanZipDer (\\x11400 [x11401, x11402] -> x11400) (\\x11403 [x11404, x11405] x11406 [x11407, x11408] -> x11403) (\\x11409 x11410 [x11411, x11412] -> [x11409, 0, 0]) x11382 [v11398, rreplicate 33 x11383] ; v11415 = cos (rreplicate 33 x11383) ; v11416 = v11415 * v11415 ; v11420 = rreplicate 33 x11380 * negate (sin (rreplicate 33 x11383)) in rsum (rgather [33] v11413 (\\[i11418] -> [32 + negate i11418]) * ((v11420 * v11415 + v11420 * v11415) * negate (recip (v11416 * v11416)))) + rsum (recip v11416 * rgather [33] (rscanZipDer (\\x11458 [x11459, x11460, x11461, x11462, x11463] -> x11458) (\\x11464 [x11465, x11466, x11467, x11468, x11469] x11470 [x11471, x11472, x11473, x11474, x11475] -> x11464) (\\x11476 x11477 [x11478, x11479, x11480, x11481, x11482] -> [x11476, 0, 0, 0, 0, 0]) x11379 [rreverse (rslice 0 33 (rscanZipDer (\\x11423 [x11424, x11425, x11426] -> let x11427 = cos x11426 in x11423 + x11424 * recip (x11427 * x11427)) (\\x11429 [x11430, x11431, x11432] x11433 [x11434, x11435, x11436] -> let x11437 = cos x11436 ; x11438 = x11437 * x11437 ; x11441 = x11432 * negate (sin x11436) in x11429 + x11430 * recip x11438 + ((x11441 * x11437 + x11441 * x11437) * negate (recip (x11438 * x11438))) * x11434) (\\x11445 x11446 [x11447, x11448, x11449] -> let x11450 = cos x11449 ; x11451 = x11450 * x11450 ; x11454 = negate (recip (x11451 * x11451)) * (x11447 * x11445) in [x11445, recip x11451 * x11445, 0, negate (sin x11449) * (x11450 * x11454 + x11450 * x11454)]) x11381 [rreplicate 33 x11380, rslice 0 33 v11397, rreplicate 33 x11383])), rreplicate 33 x11380, rslice 0 33 v11413, v11398, rreplicate 33 x11383]) (\\[i11484] -> [32 + negate i11484]))) (\\x11486 [x11487, x11488, x11489, x11490, x11491] x11492 [x11493, x11494, x11495, x11496, x11497] -> let v11510 = rscanDer (\\x11498 x11499 -> x11498 + tan x11499) (\\x11500 x11501 x11502 x11503 -> let x11504 = cos x11503 in x11500 + x11501 * recip (x11504 * x11504)) (\\x11506 x11507 x11508 -> let x11509 = cos x11508 in [x11506, recip (x11509 * x11509) * x11506]) x11497 (rreplicate 33 x11496) ; v11511 = rreverse (rslice 0 33 v11510) ; v11528 = rscanZipDer (\\x11515 [x11516, x11517] -> x11515) (\\x11518 [x11519, x11520] x11521 [x11522, x11523] -> x11518) (\\x11524 x11525 [x11526, x11527] -> [x11524, 0, 0]) x11495 [v11511, rreplicate 33 x11496] ; v11530 = cos (rreplicate 33 x11496) ; v11531 = v11530 * v11530 ; v11535 = negate (sin (rreplicate 33 x11496)) ; v11536 = rreplicate 33 x11493 * v11535 ; v11537 = v11536 * v11530 + v11536 * v11530 ; v11538 = v11531 * v11531 ; v11539 = negate (recip v11538) ; v11576 = rscanZipDer (\\x11544 [x11545, x11546, x11547] -> let x11548 = cos x11547 in x11544 + x11545 * recip (x11548 * x11548)) (\\x11550 [x11551, x11552, x11553] x11554 [x11555, x11556, x11557] -> let x11558 = cos x11557 ; x11559 = x11558 * x11558 ; x11562 = x11553 * negate (sin x11557) in x11550 + x11551 * recip x11559 + ((x11562 * x11558 + x11562 * x11558) * negate (recip (x11559 * x11559))) * x11555) (\\x11566 x11567 [x11568, x11569, x11570] -> let x11571 = cos x11570 ; x11572 = x11571 * x11571 ; x11575 = negate (recip (x11572 * x11572)) * (x11568 * x11566) in [x11566, recip x11572 * x11566, 0, negate (sin x11570) * (x11571 * x11575 + x11571 * x11575)]) x11494 [rreplicate 33 x11493, rslice 0 33 v11510, rreplicate 33 x11496] ; v11577 = rreverse (rslice 0 33 v11576) ; v11609 = rscanZipDer (\\x11584 [x11585, x11586, x11587, x11588, x11589] -> x11584) (\\x11590 [x11591, x11592, x11593, x11594, x11595] x11596 [x11597, x11598, x11599, x11600, x11601] -> x11590) (\\x11602 x11603 [x11604, x11605, x11606, x11607, x11608] -> [x11602, 0, 0, 0, 0, 0]) x11492 [v11577, rreplicate 33 x11493, rslice 0 33 v11528, v11511, rreplicate 33 x11496] ; v11647 = rreverse (rslice 0 33 (rscanZipDer (\\x11613 [x11614, x11615, x11616] -> let x11617 = cos x11616 in x11613 + x11614 * recip (x11617 * x11617)) (\\x11619 [x11620, x11621, x11622] x11623 [x11624, x11625, x11626] -> let x11627 = cos x11626 ; x11628 = x11627 * x11627 ; x11631 = x11622 * negate (sin x11626) in x11619 + x11620 * recip x11628 + ((x11631 * x11627 + x11631 * x11627) * negate (recip (x11628 * x11628))) * x11624) (\\x11636 x11637 [x11638, x11639, x11640] -> let x11641 = cos x11640 ; x11642 = x11641 * x11641 ; x11645 = negate (recip (x11642 * x11642)) * (x11638 * x11636) in [x11636, recip x11642 * x11636, 0, negate (sin x11640) * (x11641 * x11645 + x11641 * x11645)]) x11491 [rreplicate 33 x11490, rslice 0 33 v11510, rreplicate 33 x11496])) ; v11679 = rreplicate 33 x11487 * v11535 + ((rreplicate 33 x11490 * cos (rreplicate 33 x11496)) * rconst (fromList [33] [-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0])) * rreplicate 33 x11493 ; v11680 = rreplicate 33 x11490 * negate (sin (rreplicate 33 x11496)) ; v11684 = v11680 * v11530 + v11680 * v11530 in rsum ((v11537 * v11539) * rgather [33] (rscanZipDer (\\x11649 [x11650, x11651, x11652, x11653, x11654] -> x11649) (\\x11655 [x11656, x11657, x11658, x11659, x11660] x11661 [x11662, x11663, x11664, x11665, x11666] -> x11655) (\\x11667 x11668 [x11669, x11670, x11671, x11672, x11673] -> [x11667, 0, 0, 0, 0, 0]) x11489 [v11647, rreplicate 33 x11490, rslice 0 33 v11528, v11511, rreplicate 33 x11496]) (\\[i11675] -> [32 + negate i11675])) + rsum (rgather [33] v11528 (\\[i11533] -> [32 + negate i11533]) * ((v11679 * v11530 + v11680 * v11536 + v11679 * v11530 + v11680 * v11536) * v11539 + (((v11684 * v11531 + v11684 * v11531) * negate (recip (v11538 * v11538))) * rconst (fromList [33] [-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0])) * v11537)) + rsum (rgather [33] v11609 (\\[i11611] -> [32 + negate i11611]) * (v11684 * negate (recip (v11531 * v11531)))) + rsum (recip v11531 * rgather [33] (rscanZipDer (\\x11837 [x11838, x11839, x11840, x11841, x11842, x11843, x11844, x11845, x11846, x11847, x11848] -> x11837) (\\x11849 [x11850, x11851, x11852, x11853, x11854, x11855, x11856, x11857, x11858, x11859, x11860] x11861 [x11862, x11863, x11864, x11865, x11866, x11867, x11868, x11869, x11870, x11871, x11872] -> x11849) (\\x11873 x11874 [x11875, x11876, x11877, x11878, x11879, x11880, x11881, x11882, x11883, x11884, x11885] -> [x11873, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) x11486 [rreverse (rslice 0 33 (rscanZipDer (\\x11725 [x11726, x11727, x11728, x11729, x11730, x11731, x11732] -> let x11733 = cos x11732 ; x11734 = x11733 * x11733 ; x11737 = x11728 * negate (sin x11732) in x11725 + x11726 * recip x11734 + ((x11737 * x11733 + x11737 * x11733) * negate (recip (x11734 * x11734))) * x11730) (\\x11741 [x11742, x11743, x11744, x11745, x11746, x11747, x11748] x11749 [x11750, x11751, x11752, x11753, x11754, x11755, x11756] -> let x11757 = cos x11756 ; x11758 = x11757 * x11757 ; x11760 = negate (sin x11756) ; x11761 = x11752 * x11760 ; x11762 = x11761 * x11757 + x11761 * x11757 ; x11763 = x11758 * x11758 ; x11764 = negate (recip x11763) ; x11767 = x11748 * negate (sin x11756) ; x11768 = x11767 * x11757 + x11767 * x11757 ; x11773 = x11744 * x11760 + ((x11748 * cos x11756) * rconst -1.0) * x11752 in x11741 + x11742 * recip x11758 + (x11768 * negate (recip (x11758 * x11758))) * x11750 + ((x11773 * x11757 + x11767 * x11761 + x11773 * x11757 + x11767 * x11761) * x11764 + (((x11768 * x11758 + x11768 * x11758) * negate (recip (x11763 * x11763))) * rconst -1.0) * x11762) * x11754 + x11746 * (x11762 * x11764)) (\\x11784 x11785 [x11786, x11787, x11788, x11789, x11790, x11791, x11792] -> let x11793 = cos x11792 ; x11794 = x11793 * x11793 ; x11796 = negate (sin x11792) ; x11797 = x11788 * x11796 ; x11798 = x11797 * x11793 + x11797 * x11793 ; x11799 = x11794 * x11794 ; x11800 = negate (recip x11799) ; x11803 = x11790 * x11784 ; x11804 = negate (recip (x11799 * x11799)) * (rconst -1.0 * (x11798 * x11803)) ; x11805 = x11800 * x11803 ; x11806 = x11793 * x11805 + x11793 * x11805 ; x11807 = negate (recip (x11794 * x11794)) * (x11786 * x11784) + x11794 * x11804 + x11794 * x11804 in [x11784, recip x11794 * x11784, 0, x11796 * x11806, 0, (x11798 * x11800) * x11784, 0, negate (sin x11792) * (x11793 * x11807 + x11793 * x11807 + x11797 * x11805 + x11797 * x11805) + cos x11792 * (rconst -1.0 * (x11788 * x11806))]) x11488 [rreplicate 33 x11487, rslice 0 33 (rscanZipDer (\\x11691 [x11692, x11693, x11694] -> let x11695 = cos x11694 in x11691 + x11692 * recip (x11695 * x11695)) (\\x11697 [x11698, x11699, x11700] x11701 [x11702, x11703, x11704] -> let x11705 = cos x11704 ; x11706 = x11705 * x11705 ; x11709 = x11700 * negate (sin x11704) in x11697 + x11698 * recip x11706 + ((x11709 * x11705 + x11709 * x11705) * negate (recip (x11706 * x11706))) * x11702) (\\x11714 x11715 [x11716, x11717, x11718] -> let x11719 = cos x11718 ; x11720 = x11719 * x11719 ; x11723 = negate (recip (x11720 * x11720)) * (x11716 * x11714) in [x11714, recip x11720 * x11714, 0, negate (sin x11718) * (x11719 * x11723 + x11719 * x11723)]) x11491 [rreplicate 33 x11490, rslice 0 33 v11510, rreplicate 33 x11496]), rreplicate 33 x11490, rslice 0 33 v11576, rreplicate 33 x11493, rslice 0 33 v11510, rreplicate 33 x11496])), rreplicate 33 x11487, rslice 0 33 (rscanZipDer (\\x11811 [x11812, x11813, x11814, x11815, x11816] -> x11811) (\\x11817 [x11818, x11819, x11820, x11821, x11822] x11823 [x11824, x11825, x11826, x11827, x11828] -> x11817) (\\x11829 x11830 [x11831, x11832, x11833, x11834, x11835] -> [x11829, 0, 0, 0, 0, 0]) x11489 [v11647, rreplicate 33 x11490, rslice 0 33 v11528, v11511, rreplicate 33 x11496]), v11647, rreplicate 33 x11490, rslice 0 33 v11609, v11577, rreplicate 33 x11493, rslice 0 33 v11528, v11511, rreplicate 33 x11496]) (\\[i11887] -> [32 + negate i11887]))) (\\x11891 x11892 [x11893, x11894, x11895, x11896, x11897] -> let v11946 = rscanDer (\\x11934 x11935 -> x11934 + tan x11935) (\\x11936 x11937 x11938 x11939 -> let x11940 = cos x11939 in x11936 + x11937 * recip (x11940 * x11940)) (\\x11942 x11943 x11944 -> let x11945 = cos x11944 in [x11942, recip (x11945 * x11945) * x11942]) x11897 (rreplicate 33 x11896) ; v11947 = rreverse (rslice 0 33 v11946) ; v11964 = rscanZipDer (\\x11951 [x11952, x11953] -> x11951) (\\x11954 [x11955, x11956] x11957 [x11958, x11959] -> x11954) (\\x11960 x11961 [x11962, x11963] -> [x11960, 0, 0]) x11895 [v11947, rreplicate 33 x11896] ; v11966 = cos (rreplicate 33 x11896) ; v11967 = v11966 * v11966 ; v11971 = negate (sin (rreplicate 33 x11896)) ; v11972 = rreplicate 33 x11893 * v11971 ; v11973 = v11972 * v11966 + v11972 * v11966 ; v11974 = v11967 * v11967 ; v11975 = negate (recip v11974) ; v12012 = rscanZipDer (\\x11980 [x11981, x11982, x11983] -> let x11984 = cos x11983 in x11980 + x11981 * recip (x11984 * x11984)) (\\x11986 [x11987, x11988, x11989] x11990 [x11991, x11992, x11993] -> let x11994 = cos x11993 ; x11995 = x11994 * x11994 ; x11998 = x11989 * negate (sin x11993) in x11986 + x11987 * recip x11995 + ((x11998 * x11994 + x11998 * x11994) * negate (recip (x11995 * x11995))) * x11991) (\\x12002 x12003 [x12004, x12005, x12006] -> let x12007 = cos x12006 ; x12008 = x12007 * x12007 ; x12011 = negate (recip (x12008 * x12008)) * (x12004 * x12002) in [x12002, recip x12008 * x12002, 0, negate (sin x12006) * (x12007 * x12011 + x12007 * x12011)]) x11894 [rreplicate 33 x11893, rslice 0 33 v11946, rreplicate 33 x11896] ; v12013 = rreverse (rslice 0 33 v12012) ; v12045 = rscanZipDer (\\x12020 [x12021, x12022, x12023, x12024, x12025] -> x12020) (\\x12026 [x12027, x12028, x12029, x12030, x12031] x12032 [x12033, x12034, x12035, x12036, x12037] -> x12026) (\\x12038 x12039 [x12040, x12041, x12042, x12043, x12044] -> [x12038, 0, 0, 0, 0, 0]) x11892 [v12013, rreplicate 33 x11893, rslice 0 33 v11964, v11947, rreplicate 33 x11896] ; v12050 = rreverse (rscatter [34] (recip v11967 * rreplicate 33 x11891) (\\[i12049] -> [1 + i12049])) ; v12092 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v12119 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v12151 = rreverse (rscanZipDer (\\x12120 [x12121, x12122, x12123, x12124, x12125] -> x12120 + x12121) (\\x12131 [x12132, x12133, x12134, x12135, x12136] x12137 [x12138, x12139, x12140, x12141, x12142] -> x12131 + x12132) (\\x12144 x12145 [x12146, x12147, x12148, x12149, x12150] -> [x12144, x12144, 0, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12119), rreverse (rslice 0 33 v12012), rreplicate 33 x11893, rreverse (rslice 0 33 v11946), rreplicate 33 x11896]) ; v12155 = cos (rreplicate 33 x11896) ; v12156 = v12155 * v12155 ; v12161 = negate (recip (v12156 * v12156)) * (rreplicate 33 x11893 * (rgather [33] v12151 (\\[i12159] -> [1 + i12159]) + rgather [33] v12119 (\\[i12160] -> [1 + i12160]))) ; v12169 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v12189 = rreverse (rscanZipDer (\\x12170 [x12171, x12172, x12173] -> x12170 + x12171) (\\x12175 [x12176, x12177, x12178] x12179 [x12180, x12181, x12182] -> x12175 + x12176) (\\x12184 x12185 [x12186, x12187, x12188] -> [x12184, x12184, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12169), rreverse (rslice 0 33 v11946), rreplicate 33 x11896]) ; v12190 = rgather [33] v11964 (\\[i11969] -> [32 + negate i11969]) * rreplicate 33 x11891 ; v12191 = negate (recip (v11974 * v11974)) * (rconst (fromList [33] [-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0]) * (v11973 * v12190)) ; v12192 = v11975 * v12190 ; v12193 = v11966 * v12192 + v11966 * v12192 ; v12194 = negate (recip (v11967 * v11967)) * (rgather [33] v12045 (\\[i12047] -> [32 + negate i12047]) * rreplicate 33 x11891) + v11967 * v12191 + v11967 * v12191 ; v12196 = rreverse (rscatter [34] ((v11973 * v11975) * rreplicate 33 x11891) (\\[i12195] -> [1 + i12195])) ; v12223 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0))) (rreplicate 1 (rconst 0.0))) ; v12243 = rreverse (rscanZipDer (\\x12224 [x12225, x12226, x12227] -> x12224 + x12225) (\\x12229 [x12230, x12231, x12232] x12233 [x12234, x12235, x12236] -> x12229 + x12230) (\\x12238 x12239 [x12240, x12241, x12242] -> [x12238, x12238, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12223), rreverse (rslice 0 33 v11946), rreplicate 33 x11896]) in [rscanZipDer (\\x12051 [x12052, x12053, x12054, x12055, x12056, x12057, x12058] -> x12051 + x12052) (\\x12059 [x12060, x12061, x12062, x12063, x12064, x12065, x12066] x12067 [x12068, x12069, x12070, x12071, x12072, x12073, x12074] -> x12059 + x12060) (\\x12076 x12077 [x12078, x12079, x12080, x12081, x12082, x12083, x12084] -> [x12076, x12076, 0, 0, 0, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12050), rreverse (rslice 0 33 v12045), rreverse v12013, rreplicate 33 x11893, rreverse (rslice 0 33 v11964), rreverse v11947, rreplicate 33 x11896] ! [33] + v12050 ! [0], rsum (v11971 * v12193) + rsum (recip v12156 * (rgather [33] v12151 (\\[i12165] -> [1 + i12165]) + rgather [33] v12119 (\\[i12166] -> [1 + i12166]))) + rsum (rreplicate 33 (sconst @[] 0.0)), v12151 ! [0] + v12119 ! [0], rscanZipDer (\\x12197 [x12198, x12199, x12200, x12201] -> x12197 + x12198) (\\x12202 [x12203, x12204, x12205, x12206] x12207 [x12208, x12209, x12210, x12211] -> x12202 + x12203) (\\x12213 x12214 [x12215, x12216, x12217, x12218] -> [x12213, x12213, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12196), rreverse (rslice 0 33 v11964), rreverse v11947, rreplicate 33 x11896] ! [33] + v12196 ! [0] + rscanZipDer (\\x12093 [x12094, x12095, x12096, x12097] -> x12093 + x12094) (\\x12098 [x12099, x12100, x12101, x12102] x12103 [x12104, x12105, x12106, x12107] -> x12098 + x12099) (\\x12109 x12110 [x12111, x12112, x12113, x12114] -> [x12109, x12109, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12092), rreverse (rslice 0 33 v11964), rreverse v11947, rreplicate 33 x11896] ! [33] + v12092 ! [0], rsum ((let v12244 = cos (rreplicate 33 x11896) in recip (v12244 * v12244) * (rgather [33] v12243 (\\[i12248] -> [1 + i12248]) + rgather [33] v12223 (\\[i12249] -> [1 + i12249]))) + (let v12250 = cos (rreplicate 33 x11896) in recip (v12250 * v12250) * (rgather [33] v12189 (\\[i12254] -> [1 + i12254]) + rgather [33] v12169 (\\[i12255] -> [1 + i12255])))) + rsum (rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 33 x11896)) * (v11966 * v12194 + v11966 * v12194 + v11972 * v12192 + v11972 * v12192)) + rsum (cos (rreplicate 33 x11896) * (rconst (fromList [33] [-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0,-1.0]) * (rreplicate 33 x11893 * v12193))) + rsum (negate (sin (rreplicate 33 x11896)) * (v12155 * v12161 + v12155 * v12161)), v12243 ! [0] + v12223 ! [0] + v12189 ! [0] + v12169 ! [0]]) x10646 [rreverse (rslice 0 22 (rscanZipDer (\\x11018 [x11019, x11020, x11021] -> rfoldZipDer (\\x11035 [x11036, x11037, x11038] -> let x11039 = cos x11038 in x11035 + x11036 * recip (x11039 * x11039)) (\\x11041 [x11042, x11043, x11044] x11045 [x11046, x11047, x11048] -> let x11049 = cos x11048 ; x11050 = x11049 * x11049 ; x11053 = x11044 * negate (sin x11048) in x11041 + x11042 * recip x11050 + ((x11053 * x11049 + x11053 * x11049) * negate (recip (x11050 * x11050))) * x11046) (\\x11057 x11058 [x11059, x11060, x11061] -> let x11062 = cos x11061 ; x11063 = x11062 * x11062 ; x11066 = negate (recip (x11063 * x11063)) * (x11059 * x11057) in [x11057, recip x11063 * x11057, 0, negate (sin x11061) * (x11062 * x11066 + x11062 * x11066)]) x11019 [rreplicate 33 x11018, rslice 0 33 (rscanDer (\\x11022 x11023 -> x11022 + tan x11023) (\\x11024 x11025 x11026 x11027 -> let x11028 = cos x11027 in x11024 + x11025 * recip (x11028 * x11028)) (\\x11030 x11031 x11032 -> let x11033 = cos x11032 in [x11030, recip (x11033 * x11033) * x11030]) x11021 (rreplicate 33 x11020)), rreplicate 33 x11020]) (\\x11067 [x11068, x11069, x11070] x11071 [x11072, x11073, x11074] -> let v11087 = rscanDer (\\x11075 x11076 -> x11075 + tan x11076) (\\x11077 x11078 x11079 x11080 -> let x11081 = cos x11080 in x11077 + x11078 * recip (x11081 * x11081)) (\\x11083 x11084 x11085 -> let x11086 = cos x11085 in [x11083, recip (x11086 * x11086) * x11083]) x11074 (rreplicate 33 x11073) in rfoldZipDer (\\x11158 [x11159, x11160, x11161, x11162, x11163, x11164, x11165] -> let x11166 = cos x11165 ; x11167 = x11166 * x11166 ; x11170 = x11161 * negate (sin x11165) in x11158 + x11159 * recip x11167 + ((x11170 * x11166 + x11170 * x11166) * negate (recip (x11167 * x11167))) * x11163) (\\x11174 [x11175, x11176, x11177, x11178, x11179, x11180, x11181] x11182 [x11183, x11184, x11185, x11186, x11187, x11188, x11189] -> let x11190 = cos x11189 ; x11191 = x11190 * x11190 ; x11193 = negate (sin x11189) ; x11194 = x11185 * x11193 ; x11195 = x11194 * x11190 + x11194 * x11190 ; x11196 = x11191 * x11191 ; x11197 = negate (recip x11196) ; x11200 = x11181 * negate (sin x11189) ; x11201 = x11200 * x11190 + x11200 * x11190 ; x11206 = x11177 * x11193 + ((x11181 * cos x11189) * rconst -1.0) * x11185 in x11174 + x11175 * recip x11191 + (x11201 * negate (recip (x11191 * x11191))) * x11183 + ((x11206 * x11190 + x11200 * x11194 + x11206 * x11190 + x11200 * x11194) * x11197 + (((x11201 * x11191 + x11201 * x11191) * negate (recip (x11196 * x11196))) * rconst -1.0) * x11195) * x11187 + x11179 * (x11195 * x11197)) (\\x11217 x11218 [x11219, x11220, x11221, x11222, x11223, x11224, x11225] -> let x11226 = cos x11225 ; x11227 = x11226 * x11226 ; x11229 = negate (sin x11225) ; x11230 = x11221 * x11229 ; x11231 = x11230 * x11226 + x11230 * x11226 ; x11232 = x11227 * x11227 ; x11233 = negate (recip x11232) ; x11236 = x11223 * x11217 ; x11237 = negate (recip (x11232 * x11232)) * (rconst -1.0 * (x11231 * x11236)) ; x11238 = x11233 * x11236 ; x11239 = x11226 * x11238 + x11226 * x11238 ; x11240 = negate (recip (x11227 * x11227)) * (x11219 * x11217) + x11227 * x11237 + x11227 * x11237 in [x11217, recip x11227 * x11217, 0, x11229 * x11239, 0, (x11231 * x11233) * x11217, 0, negate (sin x11225) * (x11226 * x11240 + x11226 * x11240 + x11230 * x11238 + x11230 * x11238) + cos x11225 * (rconst -1.0 * (x11221 * x11239))]) x11068 [rreplicate 33 x11067, rslice 0 33 (rscanZipDer (\\x11124 [x11125, x11126, x11127] -> let x11128 = cos x11127 in x11124 + x11125 * recip (x11128 * x11128)) (\\x11130 [x11131, x11132, x11133] x11134 [x11135, x11136, x11137] -> let x11138 = cos x11137 ; x11139 = x11138 * x11138 ; x11142 = x11133 * negate (sin x11137) in x11130 + x11131 * recip x11139 + ((x11142 * x11138 + x11142 * x11138) * negate (recip (x11139 * x11139))) * x11135) (\\x11147 x11148 [x11149, x11150, x11151] -> let x11152 = cos x11151 ; x11153 = x11152 * x11152 ; x11156 = negate (recip (x11153 * x11153)) * (x11149 * x11147) in [x11147, recip x11153 * x11147, 0, negate (sin x11151) * (x11152 * x11156 + x11152 * x11156)]) x11070 [rreplicate 33 x11069, rslice 0 33 v11087, rreplicate 33 x11073]), rreplicate 33 x11069, rslice 0 33 (rscanZipDer (\\x11091 [x11092, x11093, x11094] -> let x11095 = cos x11094 in x11091 + x11092 * recip (x11095 * x11095)) (\\x11097 [x11098, x11099, x11100] x11101 [x11102, x11103, x11104] -> let x11105 = cos x11104 ; x11106 = x11105 * x11105 ; x11109 = x11100 * negate (sin x11104) in x11097 + x11098 * recip x11106 + ((x11109 * x11105 + x11109 * x11105) * negate (recip (x11106 * x11106))) * x11102) (\\x11113 x11114 [x11115, x11116, x11117] -> let x11118 = cos x11117 ; x11119 = x11118 * x11118 ; x11122 = negate (recip (x11119 * x11119)) * (x11115 * x11113) in [x11113, recip x11119 * x11113, 0, negate (sin x11117) * (x11118 * x11122 + x11118 * x11122)]) x11072 [rreplicate 33 x11071, rslice 0 33 v11087, rreplicate 33 x11073]), rreplicate 33 x11071, rslice 0 33 v11087, rreplicate 33 x11073]) (\\x11241 x11242 [x11243, x11244, x11245] -> let v11276 = rscanDer (\\x11264 x11265 -> x11264 + tan x11265) (\\x11266 x11267 x11268 x11269 -> let x11270 = cos x11269 in x11266 + x11267 * recip (x11270 * x11270)) (\\x11272 x11273 x11274 -> let x11275 = cos x11274 in [x11272, recip (x11275 * x11275) * x11272]) x11245 (rreplicate 33 x11244) ; v11334 = rreverse (rscanZipDer (\\x11313 [x11314, x11315, x11316, x11317] -> x11313) (\\x11318 [x11319, x11320, x11321, x11322] x11323 [x11324, x11325, x11326, x11327] -> x11318) (\\x11328 x11329 [x11330, x11331, x11332, x11333] -> [x11328, 0, 0, 0, 0]) x11241 [rreverse (rslice 0 33 (rscanZipDer (\\x11280 [x11281, x11282, x11283] -> let x11284 = cos x11283 in x11280 + x11281 * recip (x11284 * x11284)) (\\x11286 [x11287, x11288, x11289] x11290 [x11291, x11292, x11293] -> let x11294 = cos x11293 ; x11295 = x11294 * x11294 ; x11298 = x11289 * negate (sin x11293) in x11286 + x11287 * recip x11295 + ((x11298 * x11294 + x11298 * x11294) * negate (recip (x11295 * x11295))) * x11291) (\\x11302 x11303 [x11304, x11305, x11306] -> let x11307 = cos x11306 ; x11308 = x11307 * x11307 ; x11311 = negate (recip (x11308 * x11308)) * (x11304 * x11302) in [x11302, recip x11308 * x11302, 0, negate (sin x11306) * (x11307 * x11311 + x11307 * x11311)]) x11243 [rreplicate 33 x11242, rslice 0 33 v11276, rreplicate 33 x11244])), rreplicate 33 x11242, rreverse (rslice 0 33 v11276), rreplicate 33 x11244]) ; v11338 = cos (rreplicate 33 x11244) ; v11339 = v11338 * v11338 ; v11343 = negate (recip (v11339 * v11339)) * (rreplicate 33 x11242 * rgather [33] v11334 (\\[i11342] -> [1 + i11342])) ; v11349 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v11369 = rreverse (rscanZipDer (\\x11350 [x11351, x11352, x11353] -> x11350 + x11351) (\\x11355 [x11356, x11357, x11358] x11359 [x11360, x11361, x11362] -> x11355 + x11356) (\\x11364 x11365 [x11366, x11367, x11368] -> [x11364, x11364, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v11349), rreverse (rslice 0 33 v11276), rreplicate 33 x11244]) in [rsum (recip v11339 * rgather [33] v11334 (\\[i11346] -> [1 + i11346])), v11334 ! [0], (let v11370 = cos (rreplicate 33 x11244) in rsum (recip (v11370 * v11370) * (rgather [33] v11369 (\\[i11374] -> [1 + i11374]) + rgather [33] v11349 (\\[i11375] -> [1 + i11375])))) + rsum (negate (sin (rreplicate 33 x11244)) * (v11338 * v11343 + v11338 * v11343)), v11369 ! [0] + v11349 ! [0]]) x10648 [rreplicate 22 x10647, rslice 0 22 v10749, rreplicate 22 x10650])), rreplicate 22 x10647, rslice 0 22 v10984, v10750, rreplicate 22 x10650]) (\\[i12257] -> [21 + negate i12257])) [rreverse (rslice 0 33 (rscanZipDer (\\v12618 [v12619, v12620, v12621] -> let v12622 = cos v12621 in v12618 + v12619 * recip (v12622 * v12622)) (\\v12624 [v12625, v12626, v12627] v12628 [v12629, v12630, v12631] -> let v12632 = cos v12631 ; v12633 = v12632 * v12632 ; v12636 = v12627 * negate (sin v12631) in v12624 + v12625 * recip v12633 + ((v12636 * v12632 + v12636 * v12632) * negate (recip (v12633 * v12633))) * v12629) (\\v12641 v12642 [v12643, v12644, v12645] -> let v12646 = cos v12645 ; v12647 = v12646 * v12646 ; v12650 = negate (recip (v12647 * v12647)) * (v12643 * v12641) in [v12641, recip v12647 * v12641, 0, negate (sin v12645) * (v12646 * v12650 + v12646 * v12650)]) (rreplicate 22 x10647) [rreplicate 33 (rslice 0 22 (rscanZipDer (\\x12259 [x12260, x12261, x12262] -> rfoldZipDer (\\x12276 [x12277, x12278, x12279] -> let x12280 = cos x12279 in x12276 + x12277 * recip (x12280 * x12280)) (\\x12282 [x12283, x12284, x12285] x12286 [x12287, x12288, x12289] -> let x12290 = cos x12289 ; x12291 = x12290 * x12290 ; x12294 = x12285 * negate (sin x12289) in x12282 + x12283 * recip x12291 + ((x12294 * x12290 + x12294 * x12290) * negate (recip (x12291 * x12291))) * x12287) (\\x12298 x12299 [x12300, x12301, x12302] -> let x12303 = cos x12302 ; x12304 = x12303 * x12303 ; x12307 = negate (recip (x12304 * x12304)) * (x12300 * x12298) in [x12298, recip x12304 * x12298, 0, negate (sin x12302) * (x12303 * x12307 + x12303 * x12307)]) x12260 [rreplicate 33 x12259, rslice 0 33 (rscanDer (\\x12263 x12264 -> x12263 + tan x12264) (\\x12265 x12266 x12267 x12268 -> let x12269 = cos x12268 in x12265 + x12266 * recip (x12269 * x12269)) (\\x12271 x12272 x12273 -> let x12274 = cos x12273 in [x12271, recip (x12274 * x12274) * x12271]) x12262 (rreplicate 33 x12261)), rreplicate 33 x12261]) (\\x12308 [x12309, x12310, x12311] x12312 [x12313, x12314, x12315] -> let v12328 = rscanDer (\\x12316 x12317 -> x12316 + tan x12317) (\\x12318 x12319 x12320 x12321 -> let x12322 = cos x12321 in x12318 + x12319 * recip (x12322 * x12322)) (\\x12324 x12325 x12326 -> let x12327 = cos x12326 in [x12324, recip (x12327 * x12327) * x12324]) x12315 (rreplicate 33 x12314) in rfoldZipDer (\\x12399 [x12400, x12401, x12402, x12403, x12404, x12405, x12406] -> let x12407 = cos x12406 ; x12408 = x12407 * x12407 ; x12411 = x12402 * negate (sin x12406) in x12399 + x12400 * recip x12408 + ((x12411 * x12407 + x12411 * x12407) * negate (recip (x12408 * x12408))) * x12404) (\\x12415 [x12416, x12417, x12418, x12419, x12420, x12421, x12422] x12423 [x12424, x12425, x12426, x12427, x12428, x12429, x12430] -> let x12431 = cos x12430 ; x12432 = x12431 * x12431 ; x12434 = negate (sin x12430) ; x12435 = x12426 * x12434 ; x12436 = x12435 * x12431 + x12435 * x12431 ; x12437 = x12432 * x12432 ; x12438 = negate (recip x12437) ; x12441 = x12422 * negate (sin x12430) ; x12442 = x12441 * x12431 + x12441 * x12431 ; x12447 = x12418 * x12434 + ((x12422 * cos x12430) * rconst -1.0) * x12426 in x12415 + x12416 * recip x12432 + (x12442 * negate (recip (x12432 * x12432))) * x12424 + ((x12447 * x12431 + x12441 * x12435 + x12447 * x12431 + x12441 * x12435) * x12438 + (((x12442 * x12432 + x12442 * x12432) * negate (recip (x12437 * x12437))) * rconst -1.0) * x12436) * x12428 + x12420 * (x12436 * x12438)) (\\x12458 x12459 [x12460, x12461, x12462, x12463, x12464, x12465, x12466] -> let x12467 = cos x12466 ; x12468 = x12467 * x12467 ; x12470 = negate (sin x12466) ; x12471 = x12462 * x12470 ; x12472 = x12471 * x12467 + x12471 * x12467 ; x12473 = x12468 * x12468 ; x12474 = negate (recip x12473) ; x12477 = x12464 * x12458 ; x12478 = negate (recip (x12473 * x12473)) * (rconst -1.0 * (x12472 * x12477)) ; x12479 = x12474 * x12477 ; x12480 = x12467 * x12479 + x12467 * x12479 ; x12481 = negate (recip (x12468 * x12468)) * (x12460 * x12458) + x12468 * x12478 + x12468 * x12478 in [x12458, recip x12468 * x12458, 0, x12470 * x12480, 0, (x12472 * x12474) * x12458, 0, negate (sin x12466) * (x12467 * x12481 + x12467 * x12481 + x12471 * x12479 + x12471 * x12479) + cos x12466 * (rconst -1.0 * (x12462 * x12480))]) x12309 [rreplicate 33 x12308, rslice 0 33 (rscanZipDer (\\x12365 [x12366, x12367, x12368] -> let x12369 = cos x12368 in x12365 + x12366 * recip (x12369 * x12369)) (\\x12371 [x12372, x12373, x12374] x12375 [x12376, x12377, x12378] -> let x12379 = cos x12378 ; x12380 = x12379 * x12379 ; x12383 = x12374 * negate (sin x12378) in x12371 + x12372 * recip x12380 + ((x12383 * x12379 + x12383 * x12379) * negate (recip (x12380 * x12380))) * x12376) (\\x12388 x12389 [x12390, x12391, x12392] -> let x12393 = cos x12392 ; x12394 = x12393 * x12393 ; x12397 = negate (recip (x12394 * x12394)) * (x12390 * x12388) in [x12388, recip x12394 * x12388, 0, negate (sin x12392) * (x12393 * x12397 + x12393 * x12397)]) x12311 [rreplicate 33 x12310, rslice 0 33 v12328, rreplicate 33 x12314]), rreplicate 33 x12310, rslice 0 33 (rscanZipDer (\\x12332 [x12333, x12334, x12335] -> let x12336 = cos x12335 in x12332 + x12333 * recip (x12336 * x12336)) (\\x12338 [x12339, x12340, x12341] x12342 [x12343, x12344, x12345] -> let x12346 = cos x12345 ; x12347 = x12346 * x12346 ; x12350 = x12341 * negate (sin x12345) in x12338 + x12339 * recip x12347 + ((x12350 * x12346 + x12350 * x12346) * negate (recip (x12347 * x12347))) * x12343) (\\x12354 x12355 [x12356, x12357, x12358] -> let x12359 = cos x12358 ; x12360 = x12359 * x12359 ; x12363 = negate (recip (x12360 * x12360)) * (x12356 * x12354) in [x12354, recip x12360 * x12354, 0, negate (sin x12358) * (x12359 * x12363 + x12359 * x12363)]) x12313 [rreplicate 33 x12312, rslice 0 33 v12328, rreplicate 33 x12314]), rreplicate 33 x12312, rslice 0 33 v12328, rreplicate 33 x12314]) (\\x12482 x12483 [x12484, x12485, x12486] -> let v12517 = rscanDer (\\x12505 x12506 -> x12505 + tan x12506) (\\x12507 x12508 x12509 x12510 -> let x12511 = cos x12510 in x12507 + x12508 * recip (x12511 * x12511)) (\\x12513 x12514 x12515 -> let x12516 = cos x12515 in [x12513, recip (x12516 * x12516) * x12513]) x12486 (rreplicate 33 x12485) ; v12575 = rreverse (rscanZipDer (\\x12554 [x12555, x12556, x12557, x12558] -> x12554) (\\x12559 [x12560, x12561, x12562, x12563] x12564 [x12565, x12566, x12567, x12568] -> x12559) (\\x12569 x12570 [x12571, x12572, x12573, x12574] -> [x12569, 0, 0, 0, 0]) x12482 [rreverse (rslice 0 33 (rscanZipDer (\\x12521 [x12522, x12523, x12524] -> let x12525 = cos x12524 in x12521 + x12522 * recip (x12525 * x12525)) (\\x12527 [x12528, x12529, x12530] x12531 [x12532, x12533, x12534] -> let x12535 = cos x12534 ; x12536 = x12535 * x12535 ; x12539 = x12530 * negate (sin x12534) in x12527 + x12528 * recip x12536 + ((x12539 * x12535 + x12539 * x12535) * negate (recip (x12536 * x12536))) * x12532) (\\x12543 x12544 [x12545, x12546, x12547] -> let x12548 = cos x12547 ; x12549 = x12548 * x12548 ; x12552 = negate (recip (x12549 * x12549)) * (x12545 * x12543) in [x12543, recip x12549 * x12543, 0, negate (sin x12547) * (x12548 * x12552 + x12548 * x12552)]) x12484 [rreplicate 33 x12483, rslice 0 33 v12517, rreplicate 33 x12485])), rreplicate 33 x12483, rreverse (rslice 0 33 v12517), rreplicate 33 x12485]) ; v12579 = cos (rreplicate 33 x12485) ; v12580 = v12579 * v12579 ; v12584 = negate (recip (v12580 * v12580)) * (rreplicate 33 x12483 * rgather [33] v12575 (\\[i12583] -> [1 + i12583])) ; v12590 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v12610 = rreverse (rscanZipDer (\\x12591 [x12592, x12593, x12594] -> x12591 + x12592) (\\x12596 [x12597, x12598, x12599] x12600 [x12601, x12602, x12603] -> x12596 + x12597) (\\x12605 x12606 [x12607, x12608, x12609] -> [x12605, x12605, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12590), rreverse (rslice 0 33 v12517), rreplicate 33 x12485]) in [rsum (recip v12580 * rgather [33] v12575 (\\[i12587] -> [1 + i12587])), v12575 ! [0], (let v12611 = cos (rreplicate 33 x12485) in rsum (recip (v12611 * v12611) * (rgather [33] v12610 (\\[i12615] -> [1 + i12615]) + rgather [33] v12590 (\\[i12616] -> [1 + i12616])))) + rsum (negate (sin (rreplicate 33 x12485)) * (v12579 * v12584 + v12579 * v12584)), v12610 ! [0] + v12590 ! [0]]) x10648 [rreplicate 22 x10647, rslice 0 22 v10749, rreplicate 22 x10650])), rslice 0 33 m10998, rreplicate 33 (rslice 0 22 v10749)])), rreplicate 33 (rgather [22] (rscanZipDer (\\x12653 [x12654, x12655, x12656] -> rfoldZipDer (\\x12670 [x12671, x12672, x12673] -> let x12674 = cos x12673 in x12670 + x12671 * recip (x12674 * x12674)) (\\x12676 [x12677, x12678, x12679] x12680 [x12681, x12682, x12683] -> let x12684 = cos x12683 ; x12685 = x12684 * x12684 ; x12688 = x12679 * negate (sin x12683) in x12676 + x12677 * recip x12685 + ((x12688 * x12684 + x12688 * x12684) * negate (recip (x12685 * x12685))) * x12681) (\\x12692 x12693 [x12694, x12695, x12696] -> let x12697 = cos x12696 ; x12698 = x12697 * x12697 ; x12701 = negate (recip (x12698 * x12698)) * (x12694 * x12692) in [x12692, recip x12698 * x12692, 0, negate (sin x12696) * (x12697 * x12701 + x12697 * x12701)]) x12654 [rreplicate 33 x12653, rslice 0 33 (rscanDer (\\x12657 x12658 -> x12657 + tan x12658) (\\x12659 x12660 x12661 x12662 -> let x12663 = cos x12662 in x12659 + x12660 * recip (x12663 * x12663)) (\\x12665 x12666 x12667 -> let x12668 = cos x12667 in [x12665, recip (x12668 * x12668) * x12665]) x12656 (rreplicate 33 x12655)), rreplicate 33 x12655]) (\\x12702 [x12703, x12704, x12705] x12706 [x12707, x12708, x12709] -> let v12722 = rscanDer (\\x12710 x12711 -> x12710 + tan x12711) (\\x12712 x12713 x12714 x12715 -> let x12716 = cos x12715 in x12712 + x12713 * recip (x12716 * x12716)) (\\x12718 x12719 x12720 -> let x12721 = cos x12720 in [x12718, recip (x12721 * x12721) * x12718]) x12709 (rreplicate 33 x12708) in rfoldZipDer (\\x12793 [x12794, x12795, x12796, x12797, x12798, x12799, x12800] -> let x12801 = cos x12800 ; x12802 = x12801 * x12801 ; x12805 = x12796 * negate (sin x12800) in x12793 + x12794 * recip x12802 + ((x12805 * x12801 + x12805 * x12801) * negate (recip (x12802 * x12802))) * x12798) (\\x12809 [x12810, x12811, x12812, x12813, x12814, x12815, x12816] x12817 [x12818, x12819, x12820, x12821, x12822, x12823, x12824] -> let x12825 = cos x12824 ; x12826 = x12825 * x12825 ; x12828 = negate (sin x12824) ; x12829 = x12820 * x12828 ; x12830 = x12829 * x12825 + x12829 * x12825 ; x12831 = x12826 * x12826 ; x12832 = negate (recip x12831) ; x12835 = x12816 * negate (sin x12824) ; x12836 = x12835 * x12825 + x12835 * x12825 ; x12841 = x12812 * x12828 + ((x12816 * cos x12824) * rconst -1.0) * x12820 in x12809 + x12810 * recip x12826 + (x12836 * negate (recip (x12826 * x12826))) * x12818 + ((x12841 * x12825 + x12835 * x12829 + x12841 * x12825 + x12835 * x12829) * x12832 + (((x12836 * x12826 + x12836 * x12826) * negate (recip (x12831 * x12831))) * rconst -1.0) * x12830) * x12822 + x12814 * (x12830 * x12832)) (\\x12852 x12853 [x12854, x12855, x12856, x12857, x12858, x12859, x12860] -> let x12861 = cos x12860 ; x12862 = x12861 * x12861 ; x12864 = negate (sin x12860) ; x12865 = x12856 * x12864 ; x12866 = x12865 * x12861 + x12865 * x12861 ; x12867 = x12862 * x12862 ; x12868 = negate (recip x12867) ; x12871 = x12858 * x12852 ; x12872 = negate (recip (x12867 * x12867)) * (rconst -1.0 * (x12866 * x12871)) ; x12873 = x12868 * x12871 ; x12874 = x12861 * x12873 + x12861 * x12873 ; x12875 = negate (recip (x12862 * x12862)) * (x12854 * x12852) + x12862 * x12872 + x12862 * x12872 in [x12852, recip x12862 * x12852, 0, x12864 * x12874, 0, (x12866 * x12868) * x12852, 0, negate (sin x12860) * (x12861 * x12875 + x12861 * x12875 + x12865 * x12873 + x12865 * x12873) + cos x12860 * (rconst -1.0 * (x12856 * x12874))]) x12703 [rreplicate 33 x12702, rslice 0 33 (rscanZipDer (\\x12759 [x12760, x12761, x12762] -> let x12763 = cos x12762 in x12759 + x12760 * recip (x12763 * x12763)) (\\x12765 [x12766, x12767, x12768] x12769 [x12770, x12771, x12772] -> let x12773 = cos x12772 ; x12774 = x12773 * x12773 ; x12777 = x12768 * negate (sin x12772) in x12765 + x12766 * recip x12774 + ((x12777 * x12773 + x12777 * x12773) * negate (recip (x12774 * x12774))) * x12770) (\\x12782 x12783 [x12784, x12785, x12786] -> let x12787 = cos x12786 ; x12788 = x12787 * x12787 ; x12791 = negate (recip (x12788 * x12788)) * (x12784 * x12782) in [x12782, recip x12788 * x12782, 0, negate (sin x12786) * (x12787 * x12791 + x12787 * x12791)]) x12705 [rreplicate 33 x12704, rslice 0 33 v12722, rreplicate 33 x12708]), rreplicate 33 x12704, rslice 0 33 (rscanZipDer (\\x12726 [x12727, x12728, x12729] -> let x12730 = cos x12729 in x12726 + x12727 * recip (x12730 * x12730)) (\\x12732 [x12733, x12734, x12735] x12736 [x12737, x12738, x12739] -> let x12740 = cos x12739 ; x12741 = x12740 * x12740 ; x12744 = x12735 * negate (sin x12739) in x12732 + x12733 * recip x12741 + ((x12744 * x12740 + x12744 * x12740) * negate (recip (x12741 * x12741))) * x12737) (\\x12748 x12749 [x12750, x12751, x12752] -> let x12753 = cos x12752 ; x12754 = x12753 * x12753 ; x12757 = negate (recip (x12754 * x12754)) * (x12750 * x12748) in [x12748, recip x12754 * x12748, 0, negate (sin x12752) * (x12753 * x12757 + x12753 * x12757)]) x12707 [rreplicate 33 x12706, rslice 0 33 v12722, rreplicate 33 x12708]), rreplicate 33 x12706, rslice 0 33 v12722, rreplicate 33 x12708]) (\\x12876 x12877 [x12878, x12879, x12880] -> let v12911 = rscanDer (\\x12899 x12900 -> x12899 + tan x12900) (\\x12901 x12902 x12903 x12904 -> let x12905 = cos x12904 in x12901 + x12902 * recip (x12905 * x12905)) (\\x12907 x12908 x12909 -> let x12910 = cos x12909 in [x12907, recip (x12910 * x12910) * x12907]) x12880 (rreplicate 33 x12879) ; v12969 = rreverse (rscanZipDer (\\x12948 [x12949, x12950, x12951, x12952] -> x12948) (\\x12953 [x12954, x12955, x12956, x12957] x12958 [x12959, x12960, x12961, x12962] -> x12953) (\\x12963 x12964 [x12965, x12966, x12967, x12968] -> [x12963, 0, 0, 0, 0]) x12876 [rreverse (rslice 0 33 (rscanZipDer (\\x12915 [x12916, x12917, x12918] -> let x12919 = cos x12918 in x12915 + x12916 * recip (x12919 * x12919)) (\\x12921 [x12922, x12923, x12924] x12925 [x12926, x12927, x12928] -> let x12929 = cos x12928 ; x12930 = x12929 * x12929 ; x12933 = x12924 * negate (sin x12928) in x12921 + x12922 * recip x12930 + ((x12933 * x12929 + x12933 * x12929) * negate (recip (x12930 * x12930))) * x12926) (\\x12937 x12938 [x12939, x12940, x12941] -> let x12942 = cos x12941 ; x12943 = x12942 * x12942 ; x12946 = negate (recip (x12943 * x12943)) * (x12939 * x12937) in [x12937, recip x12943 * x12937, 0, negate (sin x12941) * (x12942 * x12946 + x12942 * x12946)]) x12878 [rreplicate 33 x12877, rslice 0 33 v12911, rreplicate 33 x12879])), rreplicate 33 x12877, rreverse (rslice 0 33 v12911), rreplicate 33 x12879]) ; v12973 = cos (rreplicate 33 x12879) ; v12974 = v12973 * v12973 ; v12978 = negate (recip (v12974 * v12974)) * (rreplicate 33 x12877 * rgather [33] v12969 (\\[i12977] -> [1 + i12977])) ; v12984 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v13004 = rreverse (rscanZipDer (\\x12985 [x12986, x12987, x12988] -> x12985 + x12986) (\\x12990 [x12991, x12992, x12993] x12994 [x12995, x12996, x12997] -> x12990 + x12991) (\\x12999 x13000 [x13001, x13002, x13003] -> [x12999, x12999, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v12984), rreverse (rslice 0 33 v12911), rreplicate 33 x12879]) in [rsum (recip v12974 * rgather [33] v12969 (\\[i12981] -> [1 + i12981])), v12969 ! [0], (let v13005 = cos (rreplicate 33 x12879) in rsum (recip (v13005 * v13005) * (rgather [33] v13004 (\\[i13009] -> [1 + i13009]) + rgather [33] v12984 (\\[i13010] -> [1 + i13010])))) + rsum (negate (sin (rreplicate 33 x12879)) * (v12973 * v12978 + v12973 * v12978)), v13004 ! [0] + v12984 ! [0]]) x10648 [rreplicate 22 x10647, rslice 0 22 v10749, rreplicate 22 x10650]) (\\[i13011] -> [i13011])), rslice 0 33 (rscanZipDer (\\v11002 [v11003, v11004] -> v11002) (\\v11006 [v11007, v11008] v11009 [v11010, v11011] -> v11006) (\\v11012 v11013 [v11014, v11015] -> [v11012, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v10984 (\\[i11005] -> [21 + negate i11005])) [m10999, m11000]), m10999, m11000] ! [33])) (\\x13042 x13043 [x13044, x13045] -> let v13267 = rscanDer (\\x13170 x13171 -> rfoldDer (\\x13172 x13173 -> x13172 + tan x13173) (\\x13174 x13175 x13176 x13177 -> let x13178 = cos x13177 in x13174 + x13175 * recip (x13178 * x13178)) (\\x13180 x13181 x13182 -> let x13183 = cos x13182 in [x13180, recip (x13183 * x13183) * x13180]) x13171 (rreplicate 33 x13170)) (\\x13184 x13185 x13186 x13187 -> rfoldZipDer (\\x13201 [x13202, x13203, x13204] -> let x13205 = cos x13204 in x13201 + x13202 * recip (x13205 * x13205)) (\\x13207 [x13208, x13209, x13210] x13211 [x13212, x13213, x13214] -> let x13215 = cos x13214 ; x13216 = x13215 * x13215 ; x13219 = x13210 * negate (sin x13214) in x13207 + x13208 * recip x13216 + ((x13219 * x13215 + x13219 * x13215) * negate (recip (x13216 * x13216))) * x13212) (\\x13223 x13224 [x13225, x13226, x13227] -> let x13228 = cos x13227 ; x13229 = x13228 * x13228 ; x13232 = negate (recip (x13229 * x13229)) * (x13225 * x13223) in [x13223, recip x13229 * x13223, 0, negate (sin x13227) * (x13228 * x13232 + x13228 * x13232)]) x13185 [rreplicate 33 x13184, rslice 0 33 (rscanDer (\\x13188 x13189 -> x13188 + tan x13189) (\\x13190 x13191 x13192 x13193 -> let x13194 = cos x13193 in x13190 + x13191 * recip (x13194 * x13194)) (\\x13196 x13197 x13198 -> let x13199 = cos x13198 in [x13196, recip (x13199 * x13199) * x13196]) x13187 (rreplicate 33 x13186)), rreplicate 33 x13186]) (\\x13233 x13234 x13235 -> let v13262 = rreverse (rscanZipDer (\\x13249 [x13250, x13251] -> x13249) (\\x13252 [x13253, x13254] x13255 [x13256, x13257] -> x13252) (\\x13258 x13259 [x13260, x13261] -> [x13258, 0, 0]) x13233 [rreverse (rslice 0 33 (rscanDer (\\x13236 x13237 -> x13236 + tan x13237) (\\x13238 x13239 x13240 x13241 -> let x13242 = cos x13241 in x13238 + x13239 * recip (x13242 * x13242)) (\\x13244 x13245 x13246 -> let x13247 = cos x13246 in [x13244, recip (x13247 * x13247) * x13244]) x13235 (rreplicate 33 x13234))), rreplicate 33 x13234]) in [let v13263 = cos (rreplicate 33 x13234) in rsum (recip (v13263 * v13263) * rgather [33] v13262 (\\[i13266] -> [1 + i13266])), v13262 ! [0]]) x13045 (rreplicate 22 x13044) ; v13268 = rreverse (rslice 0 22 v13267) ; v13502 = rscanZipDer (\\x13270 [x13271, x13272] -> let v13300 = cos (rreplicate 33 x13271) in rsum (recip (v13300 * v13300) * rgather [33] (rscanZipDer (\\x13286 [x13287, x13288] -> x13286) (\\x13289 [x13290, x13291] x13292 [x13293, x13294] -> x13289) (\\x13295 x13296 [x13297, x13298] -> [x13295, 0, 0]) x13270 [rreverse (rslice 0 33 (rscanDer (\\x13273 x13274 -> x13273 + tan x13274) (\\x13275 x13276 x13277 x13278 -> let x13279 = cos x13278 in x13275 + x13276 * recip (x13279 * x13279)) (\\x13281 x13282 x13283 -> let x13284 = cos x13283 in [x13281, recip (x13284 * x13284) * x13281]) x13272 (rreplicate 33 x13271))), rreplicate 33 x13271]) (\\[i13303] -> [32 + negate i13303]))) (\\x13304 [x13305, x13306] x13307 [x13308, x13309] -> let v13322 = rscanDer (\\x13310 x13311 -> x13310 + tan x13311) (\\x13312 x13313 x13314 x13315 -> let x13316 = cos x13315 in x13312 + x13313 * recip (x13316 * x13316)) (\\x13318 x13319 x13320 -> let x13321 = cos x13320 in [x13318, recip (x13321 * x13321) * x13318]) x13309 (rreplicate 33 x13308) ; v13323 = rreverse (rslice 0 33 v13322) ; v13338 = rscanZipDer (\\x13325 [x13326, x13327] -> x13325) (\\x13328 [x13329, x13330] x13331 [x13332, x13333] -> x13328) (\\x13334 x13335 [x13336, x13337] -> [x13334, 0, 0]) x13307 [v13323, rreplicate 33 x13308] ; v13340 = cos (rreplicate 33 x13308) ; v13341 = v13340 * v13340 ; v13345 = rreplicate 33 x13305 * negate (sin (rreplicate 33 x13308)) in rsum (rgather [33] v13338 (\\[i13343] -> [32 + negate i13343]) * ((v13345 * v13340 + v13345 * v13340) * negate (recip (v13341 * v13341)))) + rsum (recip v13341 * rgather [33] (rscanZipDer (\\x13383 [x13384, x13385, x13386, x13387, x13388] -> x13383) (\\x13389 [x13390, x13391, x13392, x13393, x13394] x13395 [x13396, x13397, x13398, x13399, x13400] -> x13389) (\\x13401 x13402 [x13403, x13404, x13405, x13406, x13407] -> [x13401, 0, 0, 0, 0, 0]) x13304 [rreverse (rslice 0 33 (rscanZipDer (\\x13348 [x13349, x13350, x13351] -> let x13352 = cos x13351 in x13348 + x13349 * recip (x13352 * x13352)) (\\x13354 [x13355, x13356, x13357] x13358 [x13359, x13360, x13361] -> let x13362 = cos x13361 ; x13363 = x13362 * x13362 ; x13366 = x13357 * negate (sin x13361) in x13354 + x13355 * recip x13363 + ((x13366 * x13362 + x13366 * x13362) * negate (recip (x13363 * x13363))) * x13359) (\\x13370 x13371 [x13372, x13373, x13374] -> let x13375 = cos x13374 ; x13376 = x13375 * x13375 ; x13379 = negate (recip (x13376 * x13376)) * (x13372 * x13370) in [x13370, recip x13376 * x13370, 0, negate (sin x13374) * (x13375 * x13379 + x13375 * x13379)]) x13306 [rreplicate 33 x13305, rslice 0 33 v13322, rreplicate 33 x13308])), rreplicate 33 x13305, rslice 0 33 v13338, v13323, rreplicate 33 x13308]) (\\[i13409] -> [32 + negate i13409]))) (\\x13411 x13412 [x13413, x13414] -> let v13427 = rscanDer (\\x13415 x13416 -> x13415 + tan x13416) (\\x13417 x13418 x13419 x13420 -> let x13421 = cos x13420 in x13417 + x13418 * recip (x13421 * x13421)) (\\x13423 x13424 x13425 -> let x13426 = cos x13425 in [x13423, recip (x13426 * x13426) * x13423]) x13414 (rreplicate 33 x13413) ; v13428 = rreverse (rslice 0 33 v13427) ; v13443 = rscanZipDer (\\x13430 [x13431, x13432] -> x13430) (\\x13433 [x13434, x13435] x13436 [x13437, x13438] -> x13433) (\\x13439 x13440 [x13441, x13442] -> [x13439, 0, 0]) x13412 [v13428, rreplicate 33 x13413] ; v13445 = cos (rreplicate 33 x13413) ; v13446 = v13445 * v13445 ; v13450 = negate (recip (v13446 * v13446)) * (rgather [33] v13443 (\\[i13448] -> [32 + negate i13448]) * rreplicate 33 x13411) ; v13452 = rreverse (rscatter [34] (recip v13446 * rreplicate 33 x13411) (\\[i13451] -> [1 + i13451])) ; v13476 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v13495 = rreverse (rscanZipDer (\\x13477 [x13478, x13479, x13480] -> x13477 + x13478) (\\x13482 [x13483, x13484, x13485] x13486 [x13487, x13488, x13489] -> x13482 + x13483) (\\x13490 x13491 [x13492, x13493, x13494] -> [x13490, x13490, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v13476), rreverse (rslice 0 33 v13427), rreplicate 33 x13413]) in [rscanZipDer (\\x13453 [x13454, x13455, x13456, x13457] -> x13453 + x13454) (\\x13458 [x13459, x13460, x13461, x13462] x13463 [x13464, x13465, x13466, x13467] -> x13458 + x13459) (\\x13468 x13469 [x13470, x13471, x13472, x13473] -> [x13468, x13468, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v13452), rreverse (rslice 0 33 v13443), rreverse v13428, rreplicate 33 x13413] ! [33] + v13452 ! [0], (let v13496 = cos (rreplicate 33 x13413) in rsum (recip (v13496 * v13496) * (rgather [33] v13495 (\\[i13500] -> [1 + i13500]) + rgather [33] v13476 (\\[i13501] -> [1 + i13501])))) + sconst @[] 0.0 * rconst 33.0 + rsum (negate (sin (rreplicate 33 x13413)) * (v13445 * v13450 + v13445 * v13450)), v13495 ! [0] + v13476 ! [0]]) x13043 [v13268, rreplicate 22 x13044] ; m13516 = rscanDer (\\v13504 v13505 -> v13504 + tan v13505) (\\v13506 v13507 v13508 v13509 -> let v13510 = cos v13509 in v13506 + v13507 * recip (v13510 * v13510)) (\\v13512 v13513 v13514 -> let v13515 = cos v13514 in [v13512, recip (v13515 * v13515) * v13512]) (rreplicate 22 x13044) (rreplicate 33 (rslice 0 22 v13267)) ; m13517 = rreverse (rslice 0 33 m13516) ; m13518 = rreplicate 33 (rgather [22] v13267 (\\[i13519] -> [i13519])) ; m13537 = rreverse (rscatter [34,22] (rreplicate 22 x13042) (\\[i13536] -> [0, i13536])) ; v13567 = rscatter [23] (rsum (rreplicate 33 (sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])))) (\\[i13566] -> [i13566]) ; v13817 = rreverse (rscanZipDer (\\x13568 [x13569, x13570, x13571] -> let v13599 = cos (rreplicate 33 x13570) in rsum (recip (v13599 * v13599) * rgather [33] (rscanZipDer (\\x13585 [x13586, x13587] -> x13585) (\\x13588 [x13589, x13590] x13591 [x13592, x13593] -> x13588) (\\x13594 x13595 [x13596, x13597] -> [x13594, 0, 0]) (x13568 + x13569) [rreverse (rslice 0 33 (rscanDer (\\x13572 x13573 -> x13572 + tan x13573) (\\x13574 x13575 x13576 x13577 -> let x13578 = cos x13577 in x13574 + x13575 * recip (x13578 * x13578)) (\\x13580 x13581 x13582 -> let x13583 = cos x13582 in [x13580, recip (x13583 * x13583) * x13580]) x13571 (rreplicate 33 x13570))), rreplicate 33 x13570]) (\\[i13602] -> [32 + negate i13602]))) (\\x13603 [x13604, x13605, x13606] x13607 [x13608, x13609, x13610] -> let v13623 = rscanDer (\\x13611 x13612 -> x13611 + tan x13612) (\\x13613 x13614 x13615 x13616 -> let x13617 = cos x13616 in x13613 + x13614 * recip (x13617 * x13617)) (\\x13619 x13620 x13621 -> let x13622 = cos x13621 in [x13619, recip (x13622 * x13622) * x13619]) x13610 (rreplicate 33 x13609) ; v13624 = rreverse (rslice 0 33 v13623) ; v13639 = rscanZipDer (\\x13626 [x13627, x13628] -> x13626) (\\x13629 [x13630, x13631] x13632 [x13633, x13634] -> x13629) (\\x13635 x13636 [x13637, x13638] -> [x13635, 0, 0]) (x13607 + x13608) [v13624, rreplicate 33 x13609] ; v13641 = cos (rreplicate 33 x13609) ; v13642 = v13641 * v13641 ; v13646 = rreplicate 33 x13605 * negate (sin (rreplicate 33 x13609)) in rsum (rgather [33] v13639 (\\[i13644] -> [32 + negate i13644]) * ((v13646 * v13641 + v13646 * v13641) * negate (recip (v13642 * v13642)))) + rsum (recip v13642 * rgather [33] (rscanZipDer (\\x13686 [x13687, x13688, x13689, x13690, x13691] -> x13686) (\\x13692 [x13693, x13694, x13695, x13696, x13697] x13698 [x13699, x13700, x13701, x13702, x13703] -> x13692) (\\x13704 x13705 [x13706, x13707, x13708, x13709, x13710] -> [x13704, 0, 0, 0, 0, 0]) (x13603 + x13604) [rreverse (rslice 0 33 (rscanZipDer (\\x13650 [x13651, x13652, x13653] -> let x13654 = cos x13653 in x13650 + x13651 * recip (x13654 * x13654)) (\\x13656 [x13657, x13658, x13659] x13660 [x13661, x13662, x13663] -> let x13664 = cos x13663 ; x13665 = x13664 * x13664 ; x13668 = x13659 * negate (sin x13663) in x13656 + x13657 * recip x13665 + ((x13668 * x13664 + x13668 * x13664) * negate (recip (x13665 * x13665))) * x13661) (\\x13673 x13674 [x13675, x13676, x13677] -> let x13678 = cos x13677 ; x13679 = x13678 * x13678 ; x13682 = negate (recip (x13679 * x13679)) * (x13675 * x13673) in [x13673, recip x13679 * x13673, 0, negate (sin x13677) * (x13678 * x13682 + x13678 * x13682)]) x13606 [rreplicate 33 x13605, rslice 0 33 v13623, rreplicate 33 x13609])), rreplicate 33 x13605, rslice 0 33 v13639, v13624, rreplicate 33 x13609]) (\\[i13712] -> [32 + negate i13712]))) (\\x13715 x13716 [x13717, x13718, x13719] -> let v13737 = rscanDer (\\x13725 x13726 -> x13725 + tan x13726) (\\x13727 x13728 x13729 x13730 -> let x13731 = cos x13730 in x13727 + x13728 * recip (x13731 * x13731)) (\\x13733 x13734 x13735 -> let x13736 = cos x13735 in [x13733, recip (x13736 * x13736) * x13733]) x13719 (rreplicate 33 x13718) ; v13738 = rreverse (rslice 0 33 v13737) ; v13753 = rscanZipDer (\\x13740 [x13741, x13742] -> x13740) (\\x13743 [x13744, x13745] x13746 [x13747, x13748] -> x13743) (\\x13749 x13750 [x13751, x13752] -> [x13749, 0, 0]) (x13716 + x13717) [v13738, rreplicate 33 x13718] ; v13755 = cos (rreplicate 33 x13718) ; v13756 = v13755 * v13755 ; v13760 = negate (recip (v13756 * v13756)) * (rgather [33] v13753 (\\[i13758] -> [32 + negate i13758]) * rreplicate 33 x13715) ; v13762 = rreverse (rscatter [34] (recip v13756 * rreplicate 33 x13715) (\\[i13761] -> [1 + i13761])) ; v13789 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v13809 = rreverse (rscanZipDer (\\x13790 [x13791, x13792, x13793] -> x13790 + x13791) (\\x13795 [x13796, x13797, x13798] x13799 [x13800, x13801, x13802] -> x13795 + x13796) (\\x13804 x13805 [x13806, x13807, x13808] -> [x13804, x13804, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v13789), rreverse (rslice 0 33 v13737), rreplicate 33 x13718]) ; x13810 = rscanZipDer (\\x13763 [x13764, x13765, x13766, x13767] -> x13763 + x13764) (\\x13768 [x13769, x13770, x13771, x13772] x13773 [x13774, x13775, x13776, x13777] -> x13768 + x13769) (\\x13779 x13780 [x13781, x13782, x13783, x13784] -> [x13779, x13779, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v13762), rreverse (rslice 0 33 v13753), rreverse v13738, rreplicate 33 x13718] ! [33] + v13762 ! [0] in [x13810, x13810, (let v13811 = cos (rreplicate 33 x13718) in rsum (recip (v13811 * v13811) * (rgather [33] v13809 (\\[i13815] -> [1 + i13815]) + rgather [33] v13789 (\\[i13816] -> [1 + i13816])))) + rsum (rreplicate 33 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 33 x13718)) * (v13755 * v13760 + v13755 * v13760)), v13809 ! [0] + v13789 ! [0]]) (rconst 0.0) [rreverse (rslice 1 22 v13567), rreverse (rslice 0 22 v13267), rreplicate 22 x13044]) ; m13818 = rappend (rreplicate 0 (rreplicate 22 (rconst 0.0))) (rappend (rreplicate 33 (sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]))) (rreplicate 1 (rreplicate 22 (rconst 0.0)))) ; m13838 = rreverse (rscanZipDer (\\v13819 [v13820, v13821, v13822] -> v13819 + v13820) (\\v13824 [v13825, v13826, v13827] v13828 [v13829, v13830, v13831] -> v13824 + v13825) (\\v13833 v13834 [v13835, v13836, v13837] -> [v13833, v13833, 0, 0]) (rreplicate 22 (rconst 0.0)) [rreverse (rslice 1 33 m13818), rreverse (rslice 0 33 m13516), rreplicate 33 (rslice 0 22 v13267)]) ; v13845 = rappend (rreplicate 0 (rconst 0.0)) (rappend (let m13839 = cos (rreplicate 33 (rslice 0 22 v13267)) in rsum (recip (m13839 * m13839) * (rgather [33,22] m13838 (\\[i13843] -> [1 + i13843]) + rgather [33,22] m13818 (\\[i13844] -> [1 + i13844])))) (rreplicate 1 (rconst 0.0))) ; v14095 = rreverse (rscanZipDer (\\x13846 [x13847, x13848, x13849] -> let v13877 = cos (rreplicate 33 x13848) in rsum (recip (v13877 * v13877) * rgather [33] (rscanZipDer (\\x13863 [x13864, x13865] -> x13863) (\\x13866 [x13867, x13868] x13869 [x13870, x13871] -> x13866) (\\x13872 x13873 [x13874, x13875] -> [x13872, 0, 0]) (x13846 + x13847) [rreverse (rslice 0 33 (rscanDer (\\x13850 x13851 -> x13850 + tan x13851) (\\x13852 x13853 x13854 x13855 -> let x13856 = cos x13855 in x13852 + x13853 * recip (x13856 * x13856)) (\\x13858 x13859 x13860 -> let x13861 = cos x13860 in [x13858, recip (x13861 * x13861) * x13858]) x13849 (rreplicate 33 x13848))), rreplicate 33 x13848]) (\\[i13880] -> [32 + negate i13880]))) (\\x13881 [x13882, x13883, x13884] x13885 [x13886, x13887, x13888] -> let v13901 = rscanDer (\\x13889 x13890 -> x13889 + tan x13890) (\\x13891 x13892 x13893 x13894 -> let x13895 = cos x13894 in x13891 + x13892 * recip (x13895 * x13895)) (\\x13897 x13898 x13899 -> let x13900 = cos x13899 in [x13897, recip (x13900 * x13900) * x13897]) x13888 (rreplicate 33 x13887) ; v13902 = rreverse (rslice 0 33 v13901) ; v13917 = rscanZipDer (\\x13904 [x13905, x13906] -> x13904) (\\x13907 [x13908, x13909] x13910 [x13911, x13912] -> x13907) (\\x13913 x13914 [x13915, x13916] -> [x13913, 0, 0]) (x13885 + x13886) [v13902, rreplicate 33 x13887] ; v13919 = cos (rreplicate 33 x13887) ; v13920 = v13919 * v13919 ; v13924 = rreplicate 33 x13883 * negate (sin (rreplicate 33 x13887)) in rsum (rgather [33] v13917 (\\[i13922] -> [32 + negate i13922]) * ((v13924 * v13919 + v13924 * v13919) * negate (recip (v13920 * v13920)))) + rsum (recip v13920 * rgather [33] (rscanZipDer (\\x13964 [x13965, x13966, x13967, x13968, x13969] -> x13964) (\\x13970 [x13971, x13972, x13973, x13974, x13975] x13976 [x13977, x13978, x13979, x13980, x13981] -> x13970) (\\x13982 x13983 [x13984, x13985, x13986, x13987, x13988] -> [x13982, 0, 0, 0, 0, 0]) (x13881 + x13882) [rreverse (rslice 0 33 (rscanZipDer (\\x13928 [x13929, x13930, x13931] -> let x13932 = cos x13931 in x13928 + x13929 * recip (x13932 * x13932)) (\\x13934 [x13935, x13936, x13937] x13938 [x13939, x13940, x13941] -> let x13942 = cos x13941 ; x13943 = x13942 * x13942 ; x13946 = x13937 * negate (sin x13941) in x13934 + x13935 * recip x13943 + ((x13946 * x13942 + x13946 * x13942) * negate (recip (x13943 * x13943))) * x13939) (\\x13951 x13952 [x13953, x13954, x13955] -> let x13956 = cos x13955 ; x13957 = x13956 * x13956 ; x13960 = negate (recip (x13957 * x13957)) * (x13953 * x13951) in [x13951, recip x13957 * x13951, 0, negate (sin x13955) * (x13956 * x13960 + x13956 * x13960)]) x13884 [rreplicate 33 x13883, rslice 0 33 v13901, rreplicate 33 x13887])), rreplicate 33 x13883, rslice 0 33 v13917, v13902, rreplicate 33 x13887]) (\\[i13990] -> [32 + negate i13990]))) (\\x13993 x13994 [x13995, x13996, x13997] -> let v14015 = rscanDer (\\x14003 x14004 -> x14003 + tan x14004) (\\x14005 x14006 x14007 x14008 -> let x14009 = cos x14008 in x14005 + x14006 * recip (x14009 * x14009)) (\\x14011 x14012 x14013 -> let x14014 = cos x14013 in [x14011, recip (x14014 * x14014) * x14011]) x13997 (rreplicate 33 x13996) ; v14016 = rreverse (rslice 0 33 v14015) ; v14031 = rscanZipDer (\\x14018 [x14019, x14020] -> x14018) (\\x14021 [x14022, x14023] x14024 [x14025, x14026] -> x14021) (\\x14027 x14028 [x14029, x14030] -> [x14027, 0, 0]) (x13994 + x13995) [v14016, rreplicate 33 x13996] ; v14033 = cos (rreplicate 33 x13996) ; v14034 = v14033 * v14033 ; v14038 = negate (recip (v14034 * v14034)) * (rgather [33] v14031 (\\[i14036] -> [32 + negate i14036]) * rreplicate 33 x13993) ; v14040 = rreverse (rscatter [34] (recip v14034 * rreplicate 33 x13993) (\\[i14039] -> [1 + i14039])) ; v14067 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v14087 = rreverse (rscanZipDer (\\x14068 [x14069, x14070, x14071] -> x14068 + x14069) (\\x14073 [x14074, x14075, x14076] x14077 [x14078, x14079, x14080] -> x14073 + x14074) (\\x14082 x14083 [x14084, x14085, x14086] -> [x14082, x14082, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14067), rreverse (rslice 0 33 v14015), rreplicate 33 x13996]) ; x14088 = rscanZipDer (\\x14041 [x14042, x14043, x14044, x14045] -> x14041 + x14042) (\\x14046 [x14047, x14048, x14049, x14050] x14051 [x14052, x14053, x14054, x14055] -> x14046 + x14047) (\\x14057 x14058 [x14059, x14060, x14061, x14062] -> [x14057, x14057, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14040), rreverse (rslice 0 33 v14031), rreverse v14016, rreplicate 33 x13996] ! [33] + v14040 ! [0] in [x14088, x14088, (let v14089 = cos (rreplicate 33 x13996) in rsum (recip (v14089 * v14089) * (rgather [33] v14087 (\\[i14093] -> [1 + i14093]) + rgather [33] v14067 (\\[i14094] -> [1 + i14094])))) + rsum (rreplicate 33 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 33 x13996)) * (v14033 * v14038 + v14033 * v14038)), v14087 ! [0] + v14067 ! [0]]) (rconst 0.0) [rreverse (rslice 1 22 v13845), rreverse (rslice 0 22 v13267), rreplicate 22 x13044]) ; v14097 = rreverse (rscatter [23] (rscanZipDer (\\v13538 [v13539, v13540, v13541, v13542] -> v13538 + v13539) (\\v13543 [v13544, v13545, v13546, v13547] v13548 [v13549, v13550, v13551, v13552] -> v13543 + v13544) (\\v13554 v13555 [v13556, v13557, v13558, v13559] -> [v13554, v13554, 0, 0, 0]) (rreplicate 22 (rconst 0.0)) [rreverse (rslice 1 33 m13537), rreverse (rslice 0 33 (rscanZipDer (\\v13520 [v13521, v13522] -> v13520) (\\v13524 [v13525, v13526] v13527 [v13528, v13529] -> v13524) (\\v13530 v13531 [v13532, v13533] -> [v13530, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v13502 (\\[i13523] -> [21 + negate i13523])) [m13517, m13518])), rreverse m13517, rreverse m13518] ! [33] + m13537 ! [0]) (\\[i14096] -> [1 + i14096])) ; v14561 = rreverse (rscanZipDer (\\x14098 [x14099, x14100, x14101, x14102] -> let v14116 = rreverse (rslice 0 33 (rscanDer (\\x14103 x14104 -> x14103 + tan x14104) (\\x14105 x14106 x14107 x14108 -> let x14109 = cos x14108 in x14105 + x14106 * recip (x14109 * x14109)) (\\x14111 x14112 x14113 -> let x14114 = cos x14113 in [x14111, recip (x14114 * x14114) * x14111]) x14102 (rreplicate 33 x14101))) ; v14133 = cos (rreplicate 33 x14101) ; v14140 = rreverse (rscatter [34] (recip (v14133 * v14133) * rreplicate 33 (x14098 + x14099)) (\\[i14139] -> [1 + i14139])) in rscanZipDer (\\x14141 [x14142, x14143, x14144, x14145] -> x14141 + x14142) (\\x14146 [x14147, x14148, x14149, x14150] x14151 [x14152, x14153, x14154, x14155] -> x14146 + x14147) (\\x14156 x14157 [x14158, x14159, x14160, x14161] -> [x14156, x14156, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14140), rreverse (rslice 0 33 (rscanZipDer (\\x14118 [x14119, x14120] -> x14118) (\\x14121 [x14122, x14123] x14124 [x14125, x14126] -> x14121) (\\x14127 x14128 [x14129, x14130] -> [x14127, 0, 0]) x14100 [v14116, rreplicate 33 x14101])), rreverse v14116, rreplicate 33 x14101] ! [33] + v14140 ! [0]) (\\x14184 [x14185, x14186, x14187, x14188] x14189 [x14190, x14191, x14192, x14193] -> let v14206 = rscanDer (\\x14194 x14195 -> x14194 + tan x14195) (\\x14196 x14197 x14198 x14199 -> let x14200 = cos x14199 in x14196 + x14197 * recip (x14200 * x14200)) (\\x14202 x14203 x14204 -> let x14205 = cos x14204 in [x14202, recip (x14205 * x14205) * x14202]) x14193 (rreplicate 33 x14192) ; v14207 = rreverse (rslice 0 33 v14206) ; v14224 = rscanZipDer (\\x14211 [x14212, x14213] -> x14211) (\\x14214 [x14215, x14216] x14217 [x14218, x14219] -> x14214) (\\x14220 x14221 [x14222, x14223] -> [x14220, 0, 0]) x14191 [v14207, rreplicate 33 x14192] ; v14225 = cos (rreplicate 33 x14192) ; v14226 = v14225 * v14225 ; v14227 = recip v14226 ; v14228 = rreplicate 33 (x14189 + x14190) ; v14231 = rreverse (rslice 1 33 (rreverse (rscatter [34] (v14227 * v14228) (\\[i14229] -> [1 + i14229])))) ; v14232 = rreverse (rslice 0 33 v14224) ; v14233 = rreverse v14207 ; v14260 = rreplicate 33 x14187 * negate (sin (rreplicate 33 x14192)) ; v14267 = rreverse (rscatter [34] (((v14260 * v14225 + v14260 * v14225) * negate (recip (v14226 * v14226))) * v14228 + rreplicate 33 (x14184 + x14185) * v14227) (\\[i14265] -> [1 + i14265])) ; v14303 = rreverse (rslice 0 33 (rscanZipDer (\\x14269 [x14270, x14271, x14272] -> let x14273 = cos x14272 in x14269 + x14270 * recip (x14273 * x14273)) (\\x14275 [x14276, x14277, x14278] x14279 [x14280, x14281, x14282] -> let x14283 = cos x14282 ; x14284 = x14283 * x14283 ; x14287 = x14278 * negate (sin x14282) in x14275 + x14276 * recip x14284 + ((x14287 * x14283 + x14287 * x14283) * negate (recip (x14284 * x14284))) * x14280) (\\x14292 x14293 [x14294, x14295, x14296] -> let x14297 = cos x14296 ; x14298 = x14297 * x14297 ; x14301 = negate (recip (x14298 * x14298)) * (x14294 * x14292) in [x14292, recip x14298 * x14292, 0, negate (sin x14296) * (x14297 * x14301 + x14297 * x14301)]) x14188 [rreplicate 33 x14187, rslice 0 33 v14206, rreplicate 33 x14192])) in rscanZipDer (\\x14334 [x14335, x14336, x14337, x14338, x14339, x14340, x14341, x14342, x14343] -> x14334 + x14335) (\\x14344 [x14345, x14346, x14347, x14348, x14349, x14350, x14351, x14352, x14353] x14354 [x14355, x14356, x14357, x14358, x14359, x14360, x14361, x14362, x14363] -> x14344 + x14345) (\\x14365 x14366 [x14367, x14368, x14369, x14370, x14371, x14372, x14373, x14374, x14375] -> [x14365, x14365, 0, 0, 0, 0, 0, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14267), rreverse (rslice 0 33 (rscanZipDer (\\x14305 [x14306, x14307, x14308, x14309, x14310] -> x14305) (\\x14311 [x14312, x14313, x14314, x14315, x14316] x14317 [x14318, x14319, x14320, x14321, x14322] -> x14311) (\\x14323 x14324 [x14325, x14326, x14327, x14328, x14329] -> [x14323, 0, 0, 0, 0, 0]) x14186 [v14303, rreplicate 33 x14187, rslice 0 33 v14224, v14207, rreplicate 33 x14192])), rreverse v14303, rreplicate 33 x14187, rslice 0 33 (rscanZipDer (\\x14235 [x14236, x14237, x14238, x14239] -> x14235 + x14236) (\\x14240 [x14241, x14242, x14243, x14244] x14245 [x14246, x14247, x14248, x14249] -> x14240 + x14241) (\\x14250 x14251 [x14252, x14253, x14254, x14255] -> [x14250, x14250, 0, 0, 0]) (rconst 0.0) [v14231, v14232, v14233, rreplicate 33 x14192]), v14231, v14232, v14233, rreplicate 33 x14192] ! [33] + v14267 ! [0]) (\\x14380 x14381 [x14382, x14383, x14384, x14385] -> let v14411 = rscanDer (\\x14399 x14400 -> x14399 + tan x14400) (\\x14401 x14402 x14403 x14404 -> let x14405 = cos x14404 in x14401 + x14402 * recip (x14405 * x14405)) (\\x14407 x14408 x14409 -> let x14410 = cos x14409 in [x14407, recip (x14410 * x14410) * x14407]) x14385 (rreplicate 33 x14384) ; v14412 = rreverse (rslice 0 33 v14411) ; v14429 = rscanZipDer (\\x14416 [x14417, x14418] -> x14416) (\\x14419 [x14420, x14421] x14422 [x14423, x14424] -> x14419) (\\x14425 x14426 [x14427, x14428] -> [x14425, 0, 0]) x14383 [v14412, rreplicate 33 x14384] ; v14430 = cos (rreplicate 33 x14384) ; v14431 = v14430 * v14430 ; v14432 = recip v14431 ; v14433 = rreplicate 33 (x14381 + x14382) ; v14436 = rreverse (rslice 1 33 (rreverse (rscatter [34] (v14432 * v14433) (\\[i14434] -> [1 + i14434])))) ; v14437 = rreverse (rslice 0 33 v14429) ; v14438 = rreverse v14412 ; v14463 = rreverse (rscatter [34] x14380 (\\[] -> [0])) ; v14503 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v14531 = rgather [33] (rappend (rreplicate 1 (rconst 0.0)) (rappend (rreverse (rgather [33] (rscanZipDer (\\x14464 [x14465, x14466, x14467, x14468, x14469, x14470] -> x14464 + x14465) (\\x14471 [x14472, x14473, x14474, x14475, x14476, x14477] x14478 [x14479, x14480, x14481, x14482, x14483, x14484] -> x14471 + x14472) (\\x14486 x14487 [x14488, x14489, x14490, x14491, x14492, x14493] -> [x14486, x14486, 0, 0, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14463), rreverse (rslice 0 33 (rscanZipDer (\\x14440 [x14441, x14442, x14443, x14444] -> x14440 + x14441) (\\x14445 [x14446, x14447, x14448, x14449] x14450 [x14451, x14452, x14453, x14454] -> x14445 + x14446) (\\x14455 x14456 [x14457, x14458, x14459, x14460] -> [x14455, x14455, 0, 0, 0]) (rconst 0.0) [v14436, v14437, v14438, rreplicate 33 x14384])), rreverse v14436, rreverse v14437, rreverse v14438, rreplicate 33 x14384]) (\\[i14500] -> [32 + negate i14500]) + rgather [33] v14463 (\\[i14501] -> [1 + i14501]))) (rreplicate 0 (rconst 0.0))) + rscatter [34] x14380 (\\[] -> [0])) (\\[i14530] -> [32 + negate i14530]) ; x14532 = rsum (v14432 * v14531) ; v14533 = negate (recip (v14431 * v14431)) * (v14433 * v14531) ; v14534 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0))) (rreplicate 1 (rconst 0.0))) ; v14554 = rreverse (rscanZipDer (\\x14535 [x14536, x14537, x14538] -> x14535 + x14536) (\\x14540 [x14541, x14542, x14543] x14544 [x14545, x14546, x14547] -> x14540 + x14541) (\\x14549 x14550 [x14551, x14552, x14553] -> [x14549, x14549, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14534), rreverse (rslice 0 33 v14411), rreplicate 33 x14384]) in [x14532, x14532, rscanZipDer (\\x14504 [x14505, x14506, x14507, x14508] -> x14504 + x14505) (\\x14509 [x14510, x14511, x14512, x14513] x14514 [x14515, x14516, x14517, x14518] -> x14509 + x14510) (\\x14520 x14521 [x14522, x14523, x14524, x14525] -> [x14520, x14520, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14503), rreverse (rslice 0 33 v14429), rreverse v14412, rreplicate 33 x14384] ! [33] + v14503 ! [0], (let v14555 = cos (rreplicate 33 x14384) in rsum (recip (v14555 * v14555) * (rgather [33] v14554 (\\[i14559] -> [1 + i14559]) + rgather [33] v14534 (\\[i14560] -> [1 + i14560])))) + rsum (rreplicate 33 (sconst @[] 0.0) + rreplicate 33 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 33 x14384)) * (v14430 * v14533 + v14430 * v14533)), v14554 ! [0] + v14534 ! [0]]) (rconst 0.0) [rreverse (rslice 1 22 v14097), rreverse (rslice 0 22 v13502), rreverse v13268, rreplicate 22 x13044]) ; m14582 = rgather [22,34] (rscanDer (\\v14564 v14565 -> v14564 + tan v14565) (\\v14567 v14568 v14569 v14570 -> let v14574 = cos v14570 in v14567 + v14568 * recip (v14574 * v14574)) (\\v14576 v14577 v14578 -> let v14581 = cos v14578 in [v14576, recip (v14581 * v14581) * v14576]) (rreplicate 22 x13044) (rreplicate 33 v13268)) (\\[i15688, i15689] -> [i15689, i15688]) ; m14603 = cos (rtranspose [1,0] (rreplicate 33 v13268)) ; m14604 = m14603 * m14603 ; m14611 = negate (recip (m14604 * m14604)) * (rgather [22,33] (rscanZipDer (\\v14584 [v14585, v14586] -> v14584) (\\v14589 [v14590, v14591] v14592 [v14593, v14594] -> v14589) (\\v14596 v14597 [v14598, v14599] -> [v14596, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v13502 (\\[i14588] -> [i14588])) [rgather [33,22] m14582 (\\[i15687, i15686] -> [i15686, 32 + negate i15687]), rreplicate 33 v13268]) (\\[i14606, i14607] -> [let i15683 = 1 + i14607 in 33 + negate i15683, i14606]) * rtranspose [1,0] (rreplicate 33 (rgather [22] v14561 (\\[i14609] -> [1 + i14609]) + rgather [22] v14097 (\\[i14610] -> [1 + i14610])))) ; m14643 = rreplicate 22 (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)))) ; m14666 = rgather [22,34] (rscanZipDer (\\v14644 [v14645, v14646, v14647] -> v14644 + v14645) (\\v14651 [v14652, v14653, v14654] v14655 [v14656, v14657, v14658] -> v14651 + v14652) (\\v14660 v14661 [v14662, v14663, v14664] -> [v14660, v14660, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rreplicate 22 (rconst 0.0)) [rreverse (rslice 1 33 (rtranspose [1,0] m14643)), rreverse (rslice 0 33 (rtranspose [1,0] m14582)), rreplicate 33 v13268]) (\\[i15672, i15673] -> [33 + negate i15673, i15672]) ; v14684 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse ((let m14670 = cos (rtranspose [1,0] (rreplicate 33 v13268)) in rsum (rtranspose [1,0] (recip (m14670 * m14670) * (rgather [22,33] m14666 (\\[i14676, i14677] -> [i14676, 1 + i14677]) + rgather [22,33] m14643 (\\[i14678, i14679] -> [i14678, 1 + i14679]))))) + rreplicate 22 (sconst @[] 0.0 * rconst 33.0) + rsum (rtranspose [1,0] (negate (sin (rtranspose [1,0] (rreplicate 33 v13268))) * (m14603 * m14611 + m14603 * m14611))))) (rreplicate 1 (rconst 0.0))) ; v14934 = rreverse (rscanZipDer (\\x14685 [x14686, x14687, x14688] -> let v14716 = cos (rreplicate 33 x14687) in rsum (recip (v14716 * v14716) * rgather [33] (rscanZipDer (\\x14702 [x14703, x14704] -> x14702) (\\x14705 [x14706, x14707] x14708 [x14709, x14710] -> x14705) (\\x14711 x14712 [x14713, x14714] -> [x14711, 0, 0]) (x14685 + x14686) [rreverse (rslice 0 33 (rscanDer (\\x14689 x14690 -> x14689 + tan x14690) (\\x14691 x14692 x14693 x14694 -> let x14695 = cos x14694 in x14691 + x14692 * recip (x14695 * x14695)) (\\x14697 x14698 x14699 -> let x14700 = cos x14699 in [x14697, recip (x14700 * x14700) * x14697]) x14688 (rreplicate 33 x14687))), rreplicate 33 x14687]) (\\[i14719] -> [32 + negate i14719]))) (\\x14720 [x14721, x14722, x14723] x14724 [x14725, x14726, x14727] -> let v14740 = rscanDer (\\x14728 x14729 -> x14728 + tan x14729) (\\x14730 x14731 x14732 x14733 -> let x14734 = cos x14733 in x14730 + x14731 * recip (x14734 * x14734)) (\\x14736 x14737 x14738 -> let x14739 = cos x14738 in [x14736, recip (x14739 * x14739) * x14736]) x14727 (rreplicate 33 x14726) ; v14741 = rreverse (rslice 0 33 v14740) ; v14756 = rscanZipDer (\\x14743 [x14744, x14745] -> x14743) (\\x14746 [x14747, x14748] x14749 [x14750, x14751] -> x14746) (\\x14752 x14753 [x14754, x14755] -> [x14752, 0, 0]) (x14724 + x14725) [v14741, rreplicate 33 x14726] ; v14758 = cos (rreplicate 33 x14726) ; v14759 = v14758 * v14758 ; v14763 = rreplicate 33 x14722 * negate (sin (rreplicate 33 x14726)) in rsum (rgather [33] v14756 (\\[i14761] -> [32 + negate i14761]) * ((v14763 * v14758 + v14763 * v14758) * negate (recip (v14759 * v14759)))) + rsum (recip v14759 * rgather [33] (rscanZipDer (\\x14803 [x14804, x14805, x14806, x14807, x14808] -> x14803) (\\x14809 [x14810, x14811, x14812, x14813, x14814] x14815 [x14816, x14817, x14818, x14819, x14820] -> x14809) (\\x14821 x14822 [x14823, x14824, x14825, x14826, x14827] -> [x14821, 0, 0, 0, 0, 0]) (x14720 + x14721) [rreverse (rslice 0 33 (rscanZipDer (\\x14767 [x14768, x14769, x14770] -> let x14771 = cos x14770 in x14767 + x14768 * recip (x14771 * x14771)) (\\x14773 [x14774, x14775, x14776] x14777 [x14778, x14779, x14780] -> let x14781 = cos x14780 ; x14782 = x14781 * x14781 ; x14785 = x14776 * negate (sin x14780) in x14773 + x14774 * recip x14782 + ((x14785 * x14781 + x14785 * x14781) * negate (recip (x14782 * x14782))) * x14778) (\\x14790 x14791 [x14792, x14793, x14794] -> let x14795 = cos x14794 ; x14796 = x14795 * x14795 ; x14799 = negate (recip (x14796 * x14796)) * (x14792 * x14790) in [x14790, recip x14796 * x14790, 0, negate (sin x14794) * (x14795 * x14799 + x14795 * x14799)]) x14723 [rreplicate 33 x14722, rslice 0 33 v14740, rreplicate 33 x14726])), rreplicate 33 x14722, rslice 0 33 v14756, v14741, rreplicate 33 x14726]) (\\[i14829] -> [32 + negate i14829]))) (\\x14832 x14833 [x14834, x14835, x14836] -> let v14854 = rscanDer (\\x14842 x14843 -> x14842 + tan x14843) (\\x14844 x14845 x14846 x14847 -> let x14848 = cos x14847 in x14844 + x14845 * recip (x14848 * x14848)) (\\x14850 x14851 x14852 -> let x14853 = cos x14852 in [x14850, recip (x14853 * x14853) * x14850]) x14836 (rreplicate 33 x14835) ; v14855 = rreverse (rslice 0 33 v14854) ; v14870 = rscanZipDer (\\x14857 [x14858, x14859] -> x14857) (\\x14860 [x14861, x14862] x14863 [x14864, x14865] -> x14860) (\\x14866 x14867 [x14868, x14869] -> [x14866, 0, 0]) (x14833 + x14834) [v14855, rreplicate 33 x14835] ; v14872 = cos (rreplicate 33 x14835) ; v14873 = v14872 * v14872 ; v14877 = negate (recip (v14873 * v14873)) * (rgather [33] v14870 (\\[i14875] -> [32 + negate i14875]) * rreplicate 33 x14832) ; v14879 = rreverse (rscatter [34] (recip v14873 * rreplicate 33 x14832) (\\[i14878] -> [1 + i14878])) ; v14906 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0))) ; v14926 = rreverse (rscanZipDer (\\x14907 [x14908, x14909, x14910] -> x14907 + x14908) (\\x14912 [x14913, x14914, x14915] x14916 [x14917, x14918, x14919] -> x14912 + x14913) (\\x14921 x14922 [x14923, x14924, x14925] -> [x14921, x14921, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14906), rreverse (rslice 0 33 v14854), rreplicate 33 x14835]) ; x14927 = rscanZipDer (\\x14880 [x14881, x14882, x14883, x14884] -> x14880 + x14881) (\\x14885 [x14886, x14887, x14888, x14889] x14890 [x14891, x14892, x14893, x14894] -> x14885 + x14886) (\\x14896 x14897 [x14898, x14899, x14900, x14901] -> [x14896, x14896, 0, 0, 0]) (rconst 0.0) [rreverse (rslice 1 33 v14879), rreverse (rslice 0 33 v14870), rreverse v14855, rreplicate 33 x14835] ! [33] + v14879 ! [0] in [x14927, x14927, (let v14928 = cos (rreplicate 33 x14835) in rsum (recip (v14928 * v14928) * (rgather [33] v14926 (\\[i14932] -> [1 + i14932]) + rgather [33] v14906 (\\[i14933] -> [1 + i14933])))) + rsum (rreplicate 33 (sconst @[] 0.0)) + rsum (negate (sin (rreplicate 33 x14835)) * (v14872 * v14877 + v14872 * v14877)), v14926 ! [0] + v14906 ! [0]]) (rconst 0.0) [rreverse (rslice 1 22 v14684), rreverse (rslice 0 22 v13267), rreplicate 22 x13044]) in [v14561 ! [0] + v14097 ! [0], rsum (rscanZipDer (\\v14955 [v14956, v14957] -> v14955) (\\v14961 [v14962, v14963] v14964 [v14965, v14966] -> v14961) (\\v14968 v14969 [v14970, v14971] -> [v14968, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v14934 (\\[i14959] -> [1 + i14959]) + rgather [22] v14684 (\\[i14960] -> [1 + i14960])) [rreverse (rslice 0 33 (rscanDer (\\v14935 v14936 -> v14935 + tan v14936) (\\v14938 v14939 v14940 v14941 -> let v14945 = cos v14941 in v14938 + v14939 * recip (v14945 * v14945)) (\\v14947 v14948 v14949 -> let v14952 = cos v14949 in [v14947, recip (v14952 * v14952) * v14947]) (rreplicate 22 x13044) (rreplicate 33 (rslice 0 22 v13267)))), rreplicate 33 (rgather [22] v13267 (\\[i14954] -> [i14954]))] ! [33] + rscanZipDer (\\v15003 [v15004, v15005] -> v15003) (\\v15009 [v15010, v15011] v15012 [v15013, v15014] -> v15009) (\\v15016 v15017 [v15018, v15019] -> [v15016, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v14095 (\\[i15007] -> [1 + i15007]) + rgather [22] v13845 (\\[i15008] -> [1 + i15008])) [rreverse (rslice 0 33 (rscanDer (\\v14983 v14984 -> v14983 + tan v14984) (\\v14986 v14987 v14988 v14989 -> let v14993 = cos v14989 in v14986 + v14987 * recip (v14993 * v14993)) (\\v14995 v14996 v14997 -> let v15000 = cos v14997 in [v14995, recip (v15000 * v15000) * v14995]) (rreplicate 22 x13044) (rreplicate 33 (rslice 0 22 v13267)))), rreplicate 33 (rgather [22] v13267 (\\[i15002] -> [i15002]))] ! [33] + rscanZipDer (\\v15051 [v15052, v15053] -> v15051) (\\v15057 [v15058, v15059] v15060 [v15061, v15062] -> v15057) (\\v15064 v15065 [v15066, v15067] -> [v15064, sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[22] (fromList @[22] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rgather [22] v13817 (\\[i15055] -> [1 + i15055]) + rgather [22] v13567 (\\[i15056] -> [1 + i15056])) [rreverse (rslice 0 33 (rscanDer (\\v15031 v15032 -> v15031 + tan v15032) (\\v15034 v15035 v15036 v15037 -> let v15041 = cos v15037 in v15034 + v15035 * recip (v15041 * v15041)) (\\v15043 v15044 v15045 -> let v15048 = cos v15045 in [v15043, recip (v15048 * v15048) * v15043]) (rreplicate 22 x13044) (rreplicate 33 (rslice 0 22 v13267)))), rreplicate 33 (rgather [22] v13267 (\\[i15050] -> [i15050]))] ! [33]) + rsum (rgather [22] m14666 (\\[i14681] -> [i14681, 0]) + rgather [22] m14643 (\\[i14682] -> [i14682, 0])) + rsum (m13838 ! [0] + m13818 ! [0]), v14934 ! [0] + v14684 ! [0] + v14095 ! [0] + v13845 ! [0] + v13817 ! [0] + v13567 ! [0]]) (rconst 1.0) [rreverse (rslice 0 11 v10272), rconstant (rreplicate 11 (rconst 1.1))]) in [rsum (rscanZipDer (\\v15231 [v15232, v15233] -> let m15278 = cos (rtranspose [1,0] (rreplicate 33 v15232)) in rsum (rtranspose [1,0] (recip (m15278 * m15278) * rgather [11,33] (rscanZipDer (\\v15261 [v15262, v15263] -> v15261) (\\v15265 [v15266, v15267] v15268 [v15269, v15270] -> v15265) (\\v15272 v15273 [v15274, v15275] -> [v15272, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) v15231 [rreverse (rslice 0 33 (rscanDer (\\v15242 v15243 -> v15242 + tan v15243) (\\v15245 v15246 v15247 v15248 -> let v15252 = cos v15248 in v15245 + v15246 * recip (v15252 * v15252)) (\\v15254 v15255 v15256 -> let v15259 = cos v15256 in [v15254, recip (v15259 * v15259) * v15254]) v15233 (rreplicate 33 v15232))), rreplicate 33 v15232]) (\\[i15282, i15283] -> [let i15699 = 1 + i15283 in 33 + negate i15699, i15282])))) (\\v15284 [v15285, v15286] v15287 [v15288, v15289] -> let m15328 = rgather [11,34] (rscanDer (\\v15310 v15311 -> v15310 + tan v15311) (\\v15313 v15314 v15315 v15316 -> let v15320 = cos v15316 in v15313 + v15314 * recip (v15320 * v15320)) (\\v15322 v15323 v15324 -> let v15327 = cos v15324 in [v15322, recip (v15327 * v15327) * v15322]) v15289 (rreplicate 33 v15288)) (\\[i15700, i15701] -> [i15701, i15700]) ; m15329 = rgather [11,33] m15328 (\\[i15702, i15703] -> [i15702, 32 + negate i15703]) ; m15346 = rgather [11,34] (rscanZipDer (\\v15330 [v15331, v15332] -> v15330) (\\v15334 [v15335, v15336] v15337 [v15338, v15339] -> v15334) (\\v15341 v15342 [v15343, v15344] -> [v15341, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) v15287 [rtranspose [1,0] m15329, rreplicate 33 v15288]) (\\[i15704, i15705] -> [i15705, i15704]) ; m15348 = cos (rtranspose [1,0] (rreplicate 33 v15288)) ; m15349 = m15348 * m15348 ; m15354 = rtranspose [1,0] (rreplicate 33 v15285) * negate (sin (rtranspose [1,0] (rreplicate 33 v15288))) in rsum (rtranspose [1,0] (rgather [11,33] m15346 (\\[i15351, i15352] -> [i15351, let i15707 = 1 + i15352 in 33 + negate i15707]) * ((m15354 * m15348 + m15354 * m15348) * negate (recip (m15349 * m15349))))) + rsum (rtranspose [1,0] (recip m15349 * rgather [11,33] (rscanZipDer (\\v15409 [v15410, v15411, v15412, v15413, v15414] -> v15409) (\\v15416 [v15417, v15418, v15419, v15420, v15421] v15422 [v15423, v15424, v15425, v15426, v15427] -> v15416) (\\v15429 v15430 [v15431, v15432, v15433, v15434, v15435] -> [v15429, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) v15284 [rgather [33,11] (rscanZipDer (\\v15357 [v15358, v15359, v15360] -> let v15364 = cos v15360 in v15357 + v15358 * recip (v15364 * v15364)) (\\v15366 [v15367, v15368, v15369] v15370 [v15371, v15372, v15373] -> let v15383 = cos v15373 ; v15384 = v15383 * v15383 ; v15387 = v15369 * negate (sin v15373) in v15366 + v15367 * recip v15384 + ((v15387 * v15383 + v15387 * v15383) * negate (recip (v15384 * v15384))) * v15371) (\\v15391 v15392 [v15393, v15394, v15395] -> let v15402 = cos v15395 ; v15403 = v15402 * v15402 ; v15406 = negate (recip (v15403 * v15403)) * (v15393 * v15391) in [v15391, recip v15403 * v15391, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), negate (sin v15395) * (v15402 * v15406 + v15402 * v15406)]) v15286 [rreplicate 33 v15285, rslice 0 33 (rtranspose [1,0] m15328), rreplicate 33 v15288]) (\\[i15711] -> [32 + negate i15711]), rreplicate 33 v15285, rslice 0 33 (rtranspose [1,0] m15346), rtranspose [1,0] m15329, rreplicate 33 v15288]) (\\[i15438, i15439] -> [let i15713 = 1 + i15439 in 33 + negate i15713, i15438])))) (\\v15441 v15442 [v15443, v15444] -> let m15487 = rgather [11,34] (rscanDer (\\v15469 v15470 -> v15469 + tan v15470) (\\v15472 v15473 v15474 v15475 -> let v15479 = cos v15475 in v15472 + v15473 * recip (v15479 * v15479)) (\\v15481 v15482 v15483 -> let v15486 = cos v15483 in [v15481, recip (v15486 * v15486) * v15481]) v15444 (rreplicate 33 v15443)) (\\[i15730, i15731] -> [i15731, i15730]) ; m15488 = rgather [11,33] m15487 (\\[i15728, i15729] -> [i15728, 32 + negate i15729]) ; m15505 = rgather [11,34] (rscanZipDer (\\v15489 [v15490, v15491] -> v15489) (\\v15493 [v15494, v15495] v15496 [v15497, v15498] -> v15493) (\\v15500 v15501 [v15502, v15503] -> [v15500, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) v15442 [rtranspose [1,0] m15488, rreplicate 33 v15443]) (\\[i15726, i15727] -> [i15727, i15726]) ; m15507 = cos (rtranspose [1,0] (rreplicate 33 v15443)) ; m15508 = m15507 * m15507 ; m15513 = negate (recip (m15508 * m15508)) * (rgather [11,33] m15505 (\\[i15510, i15511] -> [i15510, let i15725 = 1 + i15511 in 33 + negate i15725]) * rtranspose [1,0] (rreplicate 33 v15441)) ; m15516 = rgather [11,34] (rscatter [34,11] (recip m15508 * rtranspose [1,0] (rreplicate 33 v15441)) (\\[i15514, i15515] -> [1 + i15515, i15514])) (\\[i15722, i15723] -> [33 + negate i15723, i15722]) ; m15543 = rreplicate 11 (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 33 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)))) ; m15566 = rgather [11,34] (rscanZipDer (\\v15544 [v15545, v15546, v15547] -> v15544 + v15545) (\\v15551 [v15552, v15553, v15554] v15555 [v15556, v15557, v15558] -> v15551 + v15552) (\\v15560 v15561 [v15562, v15563, v15564] -> [v15560, v15560, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rreplicate 11 (rconst 0.0)) [rreverse (rslice 1 33 (rtranspose [1,0] m15543)), rreverse (rslice 0 33 (rtranspose [1,0] m15487)), rreplicate 33 v15443]) (\\[i15714, i15715] -> [33 + negate i15715, i15714]) in [rscanZipDer (\\v15517 [v15518, v15519, v15520, v15521] -> v15517 + v15518) (\\v15523 [v15524, v15525, v15526, v15527] v15528 [v15529, v15530, v15531, v15532] -> v15523 + v15524) (\\v15534 v15535 [v15536, v15537, v15538, v15539] -> [v15534, v15534, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) (rreplicate 11 (rconst 0.0)) [rreverse (rslice 1 33 (rtranspose [1,0] m15516)), rreverse (rslice 0 33 (rtranspose [1,0] m15505)), rreverse (rtranspose [1,0] m15488), rreplicate 33 v15443] ! [33] + rgather [11] m15516 (\\[i15568] -> [i15568, 0]), (let m15569 = cos (rtranspose [1,0] (rreplicate 33 v15443)) in rsum (rtranspose [1,0] (recip (m15569 * m15569) * (rgather [11,33] m15566 (\\[i15575, i15576] -> [i15575, 1 + i15576]) + rgather [11,33] m15543 (\\[i15577, i15578] -> [i15577, 1 + i15578]))))) + rreplicate 11 (sconst @[] 0.0 * rconst 33.0) + rsum (rtranspose [1,0] (negate (sin (rtranspose [1,0] (rreplicate 33 v15443))) * (m15507 * m15513 + m15507 * m15513))), rgather [11] m15566 (\\[i15579] -> [i15579, 0]) + rgather [11] m15543 (\\[i15580] -> [i15580, 0])]) (rgather [11] v15079 (\\[i15241] -> [1 + i15241])) [rreverse (rslice 0 22 (rscanDer (\\v15080 v15081 -> rfoldDer (\\v15083 v15084 -> v15083 + tan v15084) (\\v15086 v15087 v15088 v15089 -> let v15093 = cos v15089 in v15086 + v15087 * recip (v15093 * v15093)) (\\v15095 v15096 v15097 -> let v15100 = cos v15097 in [v15095, recip (v15100 * v15100) * v15095]) v15081 (rreplicate 33 v15080)) (\\v15101 v15102 v15103 v15104 -> rfoldZipDer (\\v15126 [v15127, v15128, v15129] -> let v15133 = cos v15129 in v15126 + v15127 * recip (v15133 * v15133)) (\\v15135 [v15136, v15137, v15138] v15139 [v15140, v15141, v15142] -> let v15152 = cos v15142 ; v15153 = v15152 * v15152 ; v15156 = v15138 * negate (sin v15142) in v15135 + v15136 * recip v15153 + ((v15156 * v15152 + v15156 * v15152) * negate (recip (v15153 * v15153))) * v15140) (\\v15160 v15161 [v15162, v15163, v15164] -> let v15171 = cos v15164 ; v15172 = v15171 * v15171 ; v15175 = negate (recip (v15172 * v15172)) * (v15162 * v15160) in [v15160, recip v15172 * v15160, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), negate (sin v15164) * (v15171 * v15175 + v15171 * v15175)]) v15102 [rreplicate 33 v15101, rslice 0 33 (rscanDer (\\v15107 v15108 -> v15107 + tan v15108) (\\v15110 v15111 v15112 v15113 -> let v15117 = cos v15113 in v15110 + v15111 * recip (v15117 * v15117)) (\\v15119 v15120 v15121 -> let v15124 = cos v15121 in [v15119, recip (v15124 * v15124) * v15119]) v15104 (rreplicate 33 v15103)), rreplicate 33 v15103]) (\\v15176 v15177 v15178 -> let m15221 = rgather [11,34] (rscanZipDer (\\v15205 [v15206, v15207] -> v15205) (\\v15209 [v15210, v15211] v15212 [v15213, v15214] -> v15209) (\\v15216 v15217 [v15218, v15219] -> [v15216, sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]), sconst @[11] (fromList @[11] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0])]) v15176 [rreverse (rslice 0 33 (rscanDer (\\v15186 v15187 -> v15186 + tan v15187) (\\v15189 v15190 v15191 v15192 -> let v15196 = cos v15192 in v15189 + v15190 * recip (v15196 * v15196)) (\\v15198 v15199 v15200 -> let v15203 = cos v15200 in [v15198, recip (v15203 * v15203) * v15198]) v15178 (rreplicate 33 v15177))), rreplicate 33 v15177]) (\\[i15734, i15735] -> [33 + negate i15735, i15734]) in [let m15222 = cos (rtranspose [1,0] (rreplicate 33 v15177)) in rsum (rtranspose [1,0] (recip (m15222 * m15222) * rgather [11,33] m15221 (\\[i15226, i15227] -> [i15226, 1 + i15227]))), rgather [11] m15221 (\\[i15228] -> [i15228, 0])]) (rconstant (rreplicate 11 (rconst 1.1))) (rreplicate 22 (rslice 0 11 v10272)))), rreplicate 22 (rgather [11] v10272 (\\[i15230] -> [i15230]))] ! [22]) + v15079 ! [0]]"

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
      h :: forall g. HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. ( HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. ( HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. ( HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. ( HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
      h :: forall g. HVectorTensor (ADVal g) (ShapedOf (ADVal g))
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
  :: forall k rm shm r sh shaped.
     ( KnownNat k, GoodScalar rm, Sh.Shape shm, GoodScalar r, Sh.Shape sh
     , ADReadyS shaped )
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
                  , DynamicShaped $ sreverse as ])
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
  in fFoldS p as rf 26

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
