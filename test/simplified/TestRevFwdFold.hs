{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestRevFwdFold
  ( testTrees
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Int (Int64)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.IntMap as IM
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.AstFreshId (resetVarCounter)

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
  , testCase "4Sin0ScanD1RevPP" testSin0ScanD1RevPP
  , testCase "4Sin0ScanDFwdPP" testSin0ScanDFwdPP
  , testCase "4Sin0ScanD1Rev2PP" testSin0ScanD1Rev2PP
  , testCase "4Sin0ScanDFwd2PP" testSin0ScanDFwd2PP
  , testCase "4Sin0ScanD1Rev2" testSin0ScanD1Rev2
--  , testCase "4Sin0ScanD1Rev3PP" testSin0ScanD1Rev3PP
  , testCase "4Sin0ScanDFwd3PP" testSin0ScanDFwd3PP
  , testCase "4Sin0ScanD1Rev3" testSin0ScanD1Rev3
  , testCase "4Sin0ScanD0fwd" testSin0ScanD0fwd
  , testCase "4Sin0ScanD1fwd" testSin0ScanD1fwd
  , testCase "4Sin0ScanD8fwd" testSin0ScanD8fwd
  , testCase "4Sin0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4Sin0FoldNestedS1" testSin0FoldNestedS1
  , testCase "4Sin0FoldNestedS2" testSin0FoldNestedS2
  , testCase "4Sin0FoldNestedS3" testSin0FoldNestedS3
--  , testCase "4Sin0FoldNestedS4" testSin0FoldNestedS4
  , testCase "4Sin0FoldNestedS5rev" testSin0FoldNestedS5rev
  , testCase "4Sin0FoldNestedS5fwd" testSin0FoldNestedS5fwd
  , testCase "4Sin0FoldNestedSi" testSin0FoldNestedSi
  , testCase "4Sin0FoldNestedR1" testSin0FoldNestedR1
  , testCase "4Sin0FoldNestedR2" testSin0FoldNestedR2
  , testCase "4Sin0FoldNestedR3" testSin0FoldNestedR3
--  , testCase "4Sin0FoldNestedR4" testSin0FoldNestedR4
--  , testCase "4Sin0FoldNestedR41" testSin0FoldNestedR41
--  , testCase "4Sin0FoldNestedR40" testSin0FoldNestedR40
--  , testCase "4Sin0FoldNestedR400" testSin0FoldNestedR400
  , testCase "4Sin0FoldNestedRi" testSin0FoldNestedRi
  ]

foo :: RealFloat a => (a, a, a) -> a
foo (x, y, z) =
  let w = x * sin y
  in atan2 z w + z * w

fooRrev :: forall g a. (ADReady g, GoodScalar a, Differentiable a)
        => (a, a, a) -> (g a 0, g a 0, g a 0)
fooRrev (x, y, z) =
  let fDomains :: forall f. ADReady f => Domains f -> f a 0
      fDomains v = foo (rfromD $ v V.! 0, rfromD $ v V.! 1, rfromD $ v V.! 2)
      sh = []
      zero = odFromSh @a @0 sh
      shapes = V.fromList [zero, zero, zero]
      domsOf = rrev @g fDomains shapes
                    (V.fromList
                     $ [ DynamicRanked $ rconst @g $ OR.scalar x
                       , DynamicRanked $ rconst @g $ OR.scalar y
                       , DynamicRanked $ rconst @g $ OR.scalar z ])
  in ( rletDomainsIn shapes domsOf (\v -> rfromD $ v V.! 0)
     , rletDomainsIn shapes domsOf (\v -> rfromD $ v V.! 1)
     , rletDomainsIn shapes domsOf (\v -> rfromD $ v V.! 2) )

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
    @?= "rletDomainsIn (let x16 = sin (rconst 2.2) ; x17 = rconst 1.1 * x16 ; x18 = recip (rconst 3.3 * rconst 3.3 + x17 * x17) ; x19 = sin (rconst 2.2) ; x20 = rconst 1.1 * x19 ; x21 = rreshape [] (rreplicate 1 (rconst 1.0)) ; x22 = rconst 3.3 * x21 ; x23 = negate (rconst 3.3 * x18) * x21 in (x16 * x23 + x19 * x22, cos (rconst 2.2) * (rconst 1.1 * x23) + cos (rconst 2.2) * (rconst 1.1 * x22), (x17 * x18) * x21 + x20 * x21)) (\\[dret @Natural @Double @[], x2 @Natural @Double @[], x3 @Natural @Double @[]] -> dret)"

_testFooRrevPP2 :: Assertion
_testFooRrevPP2 = do
  let (a1, _, _) = fooRrev @(AstRanked FullSpan) @Double (1.1, 2.2, 3.3)
  printAstSimple IM.empty a1
    @?= "rletDomainsIn (rletInDomains (sin (rconst 2.2)) (\\x39 -> rletInDomains (rconst 1.1 * x39) (\\x40 -> rletInDomains (recip (rconst 3.3 * rconst 3.3 + x40 * x40)) (\\x41 -> rletInDomains (sin (rconst 2.2)) (\\x42 -> rletInDomains (rconst 1.1 * x42) (\\x43 -> rletInDomains (rreshape [] (rreplicate 1 (rconst 1.0))) (\\x44 -> rletInDomains (rconst 3.3 * x44) (\\x45 -> rletInDomains (negate (rconst 3.3 * x41) * x44) (\\x46 -> dmkDomains (fromList [DynamicRanked (x39 * x46 + x42 * x45), DynamicRanked (cos (rconst 2.2) * (rconst 1.1 * x46) + cos (rconst 2.2) * (rconst 1.1 * x45)), DynamicRanked ((x40 * x41) * x44 + x43 * x44)])))))))))) (\\[x24 @Natural @Double @[], x25 @Natural @Double @[], x26 @Natural @Double @[]] -> x24)"

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
    @?= "rletDomainsIn (let m127 = sscanDer (\\v110 x111 -> atan2 (sreplicate x111) (sreplicate (sin (ssum (sreplicate x111))))) (\\v112 x113 v114 x115 -> let x116 = ssum (sreplicate x115) ; v117 = sreplicate (sin x116) ; v118 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x115 * sreplicate x115 + v117 * v117) ; x119 = ssum (sreplicate x113) ; x120 = x119 * cos x116 in sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x120 * negate (sreplicate x115 * v118) + sreplicate x113 * (v117 * v118)) (\\v121 v122 x123 -> let x124 = ssum (sreplicate x123) ; v125 = sreplicate (sin x124) ; v126 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x123 * sreplicate x123 + v125 * v125) in (0, sconst @[] 0.0 + ssum ((v125 * v126) * v121) + ssum (sreplicate (cos x124 * ssum (negate (sreplicate x123 * v126) * v121))))) (sreplicate (sconstant (rconst 1.1))) (sreplicate (sconstant (rconst 1.1))) ; m162 = sreverse (sscanDDer (\\v128 [v129 @[Natural] @Double @[5], x130 @[Natural] @Double @[]] -> sletDomainsIn (let x137 = ssum (sreplicate x130) ; v138 = sreplicate (sin x137) ; v139 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + v138 * v138 + sreplicate x130 * sreplicate x130) in (0, sconst @[] 0.0 + ssum (sreplicate (cos x137 * ssum (negate (sreplicate x130 * v139) * v128))) + ssum ((v138 * v139) * v128))) (\\[v135 @[Natural] @Double @[5], x136 @[Natural] @Double @[]] -> v135)) (\\v140 [v141 @[Natural] @Double @[5], x142 @[Natural] @Double @[]] v143 [v144 @[Natural] @Double @[5], x145 @[Natural] @Double @[]] -> sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) (\\v154 v155 [v156 @[Natural] @Double @[5], x157 @[Natural] @Double @[]] -> (0, 0, 0)) (rreplicate 5 (rconst 1.0)) (sreverse (sslice m127), sreverse (sreplicate (sconstant (rconst 1.1))))) in (ssum (m162 !$ [0]) + ssum (sletDomainsIn (let v165 = sreplicate (ssum (sreplicate (sconstant (rconst 1.1)))) ; m167 = stranspose (sreplicate (sin (sgather v165 (\\[i166] -> [i166])))) ; m170 = recip (sreplicate (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) + sgather m167 (\\[i168] -> [i168]) * sgather m167 (\\[i169] -> [i169]) + sreplicate (sreplicate (sconstant (rconst 1.1)) * sreplicate (sconstant (rconst 1.1))) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0]) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0])) in (sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0]), sreplicate (sconst @[] 0.0) + ssum (stranspose ((sgather m167 (\\[i175] -> [i175]) * sgather m170 (\\[i176] -> [i176])) * sgather (sslice m162) (\\[i177] -> [i177]))) + ssum (stranspose (stranspose (sreplicate (cos (sgather v165 (\\[i171] -> [i171])) * ssum (stranspose (negate (stranspose (sreplicate (sgather (sreplicate (sconstant (rconst 1.1))) (\\[i172] -> [i172]))) * sgather m170 (\\[i173] -> [i173])) * sgather (sslice m162) (\\[i174] -> [i174]))))))) + sconst @[1] (fromList @[1] [0.0]) + sconst @[1] (fromList @[1] [0.0]))) (\\[m163 @[Natural] @Double @[1,5], v164 @[Natural] @Double @[1]] -> sgather v164 (\\[i178] -> [i178]))))) (\\[dret @Natural @Double @[]] -> dret)"

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
    @?= "rletDomainsIn (let v64 = rscanDer (\\x55 x56 -> sin x55) (\\x57 x58 x59 x60 -> x57 * cos x59) (\\x61 x62 x63 -> (cos x62 * x61, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0])) in (rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanDDer (\\x66 [x67 @Natural @Double @[], x68 @Natural @Double @[]] -> cos x67 * x66) (\\x73 [x74 @Natural @Double @[], x75 @Natural @Double @[]] x76 [x77 @Natural @Double @[], x78 @Natural @Double @[]] -> (x74 * negate (sin x77)) * x76 + x73 * cos x77) (\\x90 x91 [x92 @Natural @Double @[], x93 @Natural @Double @[]] -> (cos x92 * x90, negate (sin x92) * (x91 * x90), 0)) (rconst 1.0) (rreverse (rslice 0 1 v64), rconst (fromList [1] [42.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanDDer (\\x130 [x131 @Natural @Double @[], x132 @Natural @Double @[]] -> cos x131 * x130) (\\x137 [x138 @Natural @Double @[], x139 @Natural @Double @[]] x140 [x141 @Natural @Double @[], x142 @Natural @Double @[]] -> (x138 * negate (sin x141)) * x140 + x137 * cos x141) (\\x154 x155 [x156 @Natural @Double @[], x157 @Natural @Double @[]] -> (cos x156 * x154, negate (sin x156) * (x155 * x154), 0)) (rconst 1.0) (rreverse (rslice 0 2 v64), rconst (fromList [2] [42.0,42.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i163] -> [i163, i163])))) (\\[dret @Natural @Double @[]] -> dret)"

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
    @?= "rscanDDer (\\x67 [x68 @Natural @Double @[], x69 @Natural @Double @[], x70 @Natural @Double @[]] -> x67 * cos x69) (\\x80 [x81 @Natural @Double @[], x82 @Natural @Double @[], x83 @Natural @Double @[]] x84 [x85 @Natural @Double @[], x86 @Natural @Double @[], x87 @Natural @Double @[]] -> x80 * cos x86 + (x82 * negate (sin x86)) * x84) (\\x109 x110 [x111 @Natural @Double @[], x112 @Natural @Double @[], x113 @Natural @Double @[]] -> (cos x112 * x109, 0, negate (sin x112) * (x110 * x109), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDer (\\x57 x58 -> sin x57) (\\x59 x60 x61 x62 -> x59 * cos x61) (\\x63 x64 x65 -> (cos x64 * x63, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0]))), rconst (fromList [2] [42.0,42.0]))"

testSin0Scan1Rev2PP :: Assertion
testSin0Scan1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rletDomainsIn (let v67 = rscanDer (\\x57 x58 -> sin x57 - x58) (\\x59 x60 x61 x62 -> x59 * cos x61 + x60 * rconst -1.0) (\\x64 x65 x66 -> (cos x65 * x64, rconst -1.0 * x64)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0])) in (rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanDDer (\\x69 [x70 @Natural @Double @[], x71 @Natural @Double @[]] -> cos x70 * x69) (\\x76 [x77 @Natural @Double @[], x78 @Natural @Double @[]] x79 [x80 @Natural @Double @[], x81 @Natural @Double @[]] -> (x77 * negate (sin x80)) * x79 + x76 * cos x80) (\\x93 x94 [x95 @Natural @Double @[], x96 @Natural @Double @[]] -> (cos x95 * x93, negate (sin x95) * (x94 * x93), 0)) (rconst 1.0) (rreverse (rslice 0 1 v67), rconst (fromList [1] [5.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanDDer (\\x133 [x134 @Natural @Double @[], x135 @Natural @Double @[]] -> cos x134 * x133) (\\x140 [x141 @Natural @Double @[], x142 @Natural @Double @[]] x143 [x144 @Natural @Double @[], x145 @Natural @Double @[]] -> (x141 * negate (sin x144)) * x143 + x140 * cos x144) (\\x157 x158 [x159 @Natural @Double @[], x160 @Natural @Double @[]] -> (cos x159 * x157, negate (sin x159) * (x158 * x157), 0)) (rconst 1.0) (rreverse (rslice 0 2 v67), rconst (fromList [2] [7.0,5.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i166] -> [i166, i166])))) (\\[dret @Natural @Double @[]] -> dret)"

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
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanDDer (\\x77 [x78 @Natural @Double @[], x79 @Natural @Double @[], x80 @Natural @Double @[]] -> x77 * cos x79 + x78 * rconst -1.0) (\\x91 [x92 @Natural @Double @[], x93 @Natural @Double @[], x94 @Natural @Double @[]] x95 [x96 @Natural @Double @[], x97 @Natural @Double @[], x98 @Natural @Double @[]] -> x92 * rconst -1.0 + x91 * cos x97 + (x93 * negate (sin x97)) * x95) (\\x123 x124 [x125 @Natural @Double @[], x126 @Natural @Double @[], x127 @Natural @Double @[]] -> (cos x126 * x123, rconst -1.0 * x123, negate (sin x126) * (x124 * x123), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDer (\\x66 x67 -> sin x66 - x67) (\\x68 x69 x70 x71 -> x68 * cos x70 + x69 * rconst -1.0) (\\x73 x74 x75 -> (cos x74 * x73, rconst -1.0 * x73)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0]))), rconst (fromList [2] [5.0,7.0]))"

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
    @?= "rletDomainsIn (let v72 = rscanDer (\\x62 x63 -> sin x62 - x63) (\\x64 x65 x66 x67 -> x64 * cos x66 + x65 * rconst -1.0) (\\x69 x70 x71 -> (cos x70 * x69, rconst -1.0 * x69)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0]) ; m73 = rfromList [rappend (rreverse (rscanDDer (\\x74 [x75 @Natural @Double @[], x76 @Natural @Double @[]] -> cos x75 * x74) (\\x81 [x82 @Natural @Double @[], x83 @Natural @Double @[]] x84 [x85 @Natural @Double @[], x86 @Natural @Double @[]] -> (x82 * negate (sin x85)) * x84 + x81 * cos x85) (\\x98 x99 [x100 @Natural @Double @[], x101 @Natural @Double @[]] -> (cos x100 * x98, negate (sin x100) * (x99 * x98), 0)) (rconst 1.0) (rreverse (rslice 0 1 v72), rreplicate 1 (rconst 1.1 * rconst 5.0)))) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rreverse (rscanDDer (\\x147 [x148 @Natural @Double @[], x149 @Natural @Double @[]] -> cos x148 * x147) (\\x154 [x155 @Natural @Double @[], x156 @Natural @Double @[]] x157 [x158 @Natural @Double @[], x159 @Natural @Double @[]] -> (x155 * negate (sin x158)) * x157 + x154 * cos x158) (\\x171 x172 [x173 @Natural @Double @[], x174 @Natural @Double @[]] -> (cos x173 * x171, negate (sin x173) * (x172 * x171), 0)) (rconst 1.0) (rreverse (rslice 0 2 v72), rfromList [rconst 1.1 * rconst 7.0, rconst 1.1 * rconst 5.0]))) (rconstant (rreplicate 0 (rconst 0.0)))] ; v107 = rsum (rfromList [rappend (rconstant (rreplicate 1 (rconst -1.0)) * rgather [1] (m73 ! [0]) (\\[i109] -> [1 + i109])) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rconstant (rreplicate 2 (rconst -1.0)) * rgather [2] (m73 ! [1]) (\\[i117] -> [1 + i117])) (rconstant (rreplicate 0 (rconst 0.0)))]) in (rconst 5.0 * v107 ! [0] + rconst 7.0 * v107 ! [1] + rconst 1.0 + rsum (rgather [2] m73 (\\[i111] -> [i111, 0])))) (\\[dret @Natural @Double @[]] -> dret)"

testSin0Scan1Rev3PPForComparison :: Assertion
testSin0Scan1Rev3PPForComparison = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rfromList [sin (sin x0 - x0 * 5) - x0 * 7, sin x0 - x0 * 5, x0]) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rletDomainsIn (let x11 = cos (sin (rconst 1.1) - rconst 1.1 * rconst 5.0) * rconst 1.0 in (cos (rconst 1.1) * x11 + rconst 5.0 * (rconst -1.0 * x11) + rconst 7.0 * (rconst -1.0 * rconst 1.0) + cos (rconst 1.1) * rconst 1.0 + rconst 5.0 * (rconst -1.0 * rconst 1.0) + rconst 1.0)) (\\[dret @Natural @Double @[]] -> dret)"

testSin0ScanFwd3PP :: Assertion
testSin0ScanFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanDDer (\\x83 [x84 @Natural @Double @[], x85 @Natural @Double @[], x86 @Natural @Double @[]] -> x83 * cos x85 + x84 * rconst -1.0) (\\x97 [x98 @Natural @Double @[], x99 @Natural @Double @[], x100 @Natural @Double @[]] x101 [x102 @Natural @Double @[], x103 @Natural @Double @[], x104 @Natural @Double @[]] -> x98 * rconst -1.0 + x97 * cos x103 + (x99 * negate (sin x103)) * x101) (\\x129 x130 [x131 @Natural @Double @[], x132 @Natural @Double @[], x133 @Natural @Double @[]] -> (cos x132 * x129, rconst -1.0 * x129, negate (sin x132) * (x130 * x129), 0)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanDer (\\x69 x70 -> sin x69 - x70) (\\x71 x72 x73 x74 -> x71 * cos x73 + x72 * rconst -1.0) (\\x76 x77 x78 -> (cos x77 * x76, rconst -1.0 * x76)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])), rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])"

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
               f x0 = rscanD (\x _a -> sin x)
                             (V.fromList [odFromSh @Double ZS])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$ ZS))
           in f) 1.1)

testSin0ScanD1 :: Assertion
testSin0ScanD1 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanD (\x _a -> sin x)
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [1] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanD (\x _a -> sin x)
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [5] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD3 :: Assertion
testSin0ScanD3 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.360788364276732] :: OR.Array 5 Double)
    (rev' (\a0 -> rscanD (\_x a ->
                            sin $ rfromD @Double @5
                                    (dunDomains (V.fromList [ odFromSh @Double (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , odFromSh @Double (4 :$ 5 :$ 6 :$ 7 :$ 8 :$ ZS) ]) a V.! 0))
                         (V.fromList [ odFromSh @Double (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , odFromSh @Double (4 :$ 5 :$ 6 :$ 7 :$ 8 :$ ZS) ])
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
    (rev' (\a0 -> rscanD (\x a -> atan2 (sin x)
                                        (sin $ rfromD (dunDomains (V.fromList [odFromSh @Double
                                                                               (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)]) a V.! 0)))
                         (V.fromList [odFromSh @Double
                                        (1 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)])
                         (rreplicate0N [1,1,1,1,1] 2 * a0)
                         (V.singleton $ DynamicRanked
                          $ rreplicate 3 a0)) (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD5 :: Assertion
testSin0ScanD5 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1] [4.126141830000979] :: OR.Array 4 Double)
    (rev' (\a0 -> rscanD (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rfromD (dunDomains (V.fromList [ odFromSh @Double
                                                                             (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                                                           , odFromSh @Double
                                                                             (8 :$ 3 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS) ]) a V.! 0)))
                         (V.fromList [ odFromSh @Double
                                         (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , odFromSh @Double
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
    (rev' (\a0 -> rscanD (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rreplicate 2 $ rreplicate 5
                                          $ rsum $ rsum
                                          $ rfromD (dunDomains (V.fromList [ odFromSh @Double
                                                                             (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                                                           , odFromSh @Double
                                                                             (8 :$ 3 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS) ]) a V.! 1)))
                         (V.fromList [ odFromSh @Double
                                         (2 :$ 5 :$ 1 :$ 1 :$ 1 :$ 1 :$ ZS)
                                     , odFromSh @Double
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
                 sscanD
                   (let g :: forall f2. ADReadyS f2
                          => f2 Double '[1,1,1,1] -> DomainsOf (RankedOf f2)
                          -> f2 Double '[1,1,1,1]
                        g x a =
                          ssum
                          $ atan2 (sin $ sreplicate @f2 @5 x)
                                  (ssum $ sin $ ssum
                                   $ str $ sreplicate @f2 @7
                                   $ sreplicate @f2 @2 $ sreplicate @f2 @5
                                   $ ssum @_ @_ @3 $ ssum @_ @_ @8
                                   $ sfromD (dunDomains (V.fromList [ odFromShS @Double
                                                                             @'[2, 5, 1, 1, 1, 1]
                                                                           , odFromShS @Double
                                                                             @'[8, 3, 1, 1, 1, 1] ]) a V.! 1))
                    in g)
                   (V.fromList [ odFromShS @Double
                                                                             @'[2, 5, 1, 1, 1, 1]
                                                                           , odFromShS @Double
                                                                             @'[8, 3, 1, 1, 1, 1] ])
                   (sreplicate0N @_ @_ @[1,1,1,1] 2 * a0)
                   (V.fromList
                      [ DynamicShaped
                        $ sreplicate @f @3 (sreplicate @f @2 (sreplicate @f @5 a0))
                      , DynamicShaped
                        $ sreplicate @f @3 (sreplicate @f @8 (sreplicate @f @3 a0)) ]
                   )
           in rfromS . f . sfromR) (rreplicate0N [1,1,1,1] 1.1))

testSin0ScanD6 :: Assertion
testSin0ScanD6 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [12] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanD (\x a -> rtr
                                 $ rtr x + rreplicate 1
                                             (rreplicate 2
                                                (rfromD (dunDomains (V.fromList [odFromSh @Double (1 :$ 1 :$ ZS)]) a V.! 0))))
                         (V.fromList [odFromSh @Double (1 :$ 1 :$ ZS)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanD (\x _a -> rtr $ rreplicate 5
                                   $ (rsum (rtr x)))
                         (V.fromList [odFromSh @Double (1 :$ 1 :$ ZS)])
                         (rreplicate 2 (rreplicate 5 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD8 :: Assertion
testSin0ScanD8 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1] [9.532987357352765] :: OR.Array 3 Double)
    (rev' (\a0 -> rscanD (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7)
                                                     (dunDomains (V.fromList [odFromSh @Double (1 :$ 1 :$ 1 :$ ZS)]) a))))
                       (V.fromList [odFromSh @Double (1 :$ 1 :$ 1 :$ ZS)])
                       (rreplicate 2 (rreplicate 5
                                        (rreplicate0N [1,1,1] 2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
                       (rreplicate0N [1,1,1] 1.1))

testSin0ScanD8rev :: Assertion
testSin0ScanD8rev = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [9.53298735735276])
    (rrev1 @(Flip OR.Array) @Double @0 @3
       (\a0 -> rscanD (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7)
                                                     (dunDomains (V.fromList [odFromSh @Int64 ZS]) a))))
                       (V.fromList [odFromSh @Int64 ZS])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8rev2 :: Assertion
testSin0ScanD8rev2 = do
  let h = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanD (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked10 rsum
                                                 $ mapDomainsRanked01
                                                     (rreplicate 7)
                                                     (dunDomains (V.fromList [odFromSh @Int64 ZS]) a))))
                       (V.fromList [odFromSh @Int64 ZS])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.9579482947575])
    (crev h 1.1)

testSin0ScanD1RevPP :: Assertion
testSin0ScanD1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x _a -> sin x)
                           (V.fromList [odFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rletDomainsIn (let v90 = rscanDDer (\\x77 [x78 @Natural @Double @[]] -> sin x77) (\\x80 [x81 @Natural @Double @[]] x82 [x83 @Natural @Double @[]] -> x80 * cos x82) (\\x86 x87 [x88 @Natural @Double @[]] -> (cos x87 * x86, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0])) in (rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanDDer (\\x92 [x93 @Natural @Double @[], x94 @Natural @Double @[]] -> cos x93 * x92) (\\x99 [x100 @Natural @Double @[], x101 @Natural @Double @[]] x102 [x103 @Natural @Double @[], x104 @Natural @Double @[]] -> (x100 * negate (sin x103)) * x102 + x99 * cos x103) (\\x116 x117 [x118 @Natural @Double @[], x119 @Natural @Double @[]] -> (cos x118 * x116, negate (sin x118) * (x117 * x116), 0)) (rconst 1.0) (rreverse (rslice 0 1 v90), rconst (fromList [1] [42.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanDDer (\\x159 [x160 @Natural @Double @[], x161 @Natural @Double @[]] -> cos x160 * x159) (\\x166 [x167 @Natural @Double @[], x168 @Natural @Double @[]] x169 [x170 @Natural @Double @[], x171 @Natural @Double @[]] -> (x167 * negate (sin x170)) * x169 + x166 * cos x170) (\\x183 x184 [x185 @Natural @Double @[], x186 @Natural @Double @[]] -> (cos x185 * x183, negate (sin x185) * (x184 * x183), 0)) (rconst 1.0) (rreverse (rslice 0 2 v90), rconst (fromList [2] [42.0,42.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i192] -> [i192, i192])))) (\\[dret @Natural @Double @[]] -> dret)"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x _a -> sin x)
                           (V.fromList [odFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanDDer (\\x81 [x82 @Natural @Double @[], x83 @Natural @Double @[], x84 @Natural @Double @[]] -> x81 * cos x83) (\\x94 [x95 @Natural @Double @[], x96 @Natural @Double @[], x97 @Natural @Double @[]] x98 [x99 @Natural @Double @[], x100 @Natural @Double @[], x101 @Natural @Double @[]] -> x94 * cos x100 + (x96 * negate (sin x100)) * x98) (\\x123 x124 [x125 @Natural @Double @[], x126 @Natural @Double @[], x127 @Natural @Double @[]] -> (cos x126 * x123, 0, negate (sin x126) * (x124 * x123), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDDer (\\x67 [x68 @Natural @Double @[]] -> sin x67) (\\x70 [x71 @Natural @Double @[]] x72 [x73 @Natural @Double @[]] -> x70 * cos x72) (\\x76 x77 [x78 @Natural @Double @[]] -> (cos x77 * x76, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0]))), rconst (fromList [2] [42.0,42.0]))"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rletDomainsIn (let v96 = rscanDDer (\\x82 [x83 @Natural @Double @[]] -> sin x82 - x83) (\\x85 [x86 @Natural @Double @[]] x87 [x88 @Natural @Double @[]] -> x85 * cos x87 + x86 * rconst -1.0) (\\x92 x93 [x94 @Natural @Double @[]] -> (cos x93 * x92, rconst -1.0 * x92)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0])) in (rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanDDer (\\x98 [x99 @Natural @Double @[], x100 @Natural @Double @[]] -> cos x99 * x98) (\\x105 [x106 @Natural @Double @[], x107 @Natural @Double @[]] x108 [x109 @Natural @Double @[], x110 @Natural @Double @[]] -> (x106 * negate (sin x109)) * x108 + x105 * cos x109) (\\x122 x123 [x124 @Natural @Double @[], x125 @Natural @Double @[]] -> (cos x124 * x122, negate (sin x124) * (x123 * x122), 0)) (rconst 1.0) (rreverse (rslice 0 1 v96), rconst (fromList [1] [5.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanDDer (\\x165 [x166 @Natural @Double @[], x167 @Natural @Double @[]] -> cos x166 * x165) (\\x172 [x173 @Natural @Double @[], x174 @Natural @Double @[]] x175 [x176 @Natural @Double @[], x177 @Natural @Double @[]] -> (x173 * negate (sin x176)) * x175 + x172 * cos x176) (\\x189 x190 [x191 @Natural @Double @[], x192 @Natural @Double @[]] -> (cos x191 * x189, negate (sin x191) * (x190 * x189), 0)) (rconst 1.0) (rreverse (rslice 0 2 v96), rconst (fromList [2] [7.0,5.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i198] -> [i198, i198])))) (\\[dret @Natural @Double @[]] -> dret)"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanDDer (\\x94 [x95 @Natural @Double @[], x96 @Natural @Double @[], x97 @Natural @Double @[]] -> x94 * cos x96 + x95 * rconst -1.0) (\\x108 [x109 @Natural @Double @[], x110 @Natural @Double @[], x111 @Natural @Double @[]] x112 [x113 @Natural @Double @[], x114 @Natural @Double @[], x115 @Natural @Double @[]] -> x109 * rconst -1.0 + x108 * cos x114 + (x110 * negate (sin x114)) * x112) (\\x140 x141 [x142 @Natural @Double @[], x143 @Natural @Double @[], x144 @Natural @Double @[]] -> (cos x143 * x140, rconst -1.0 * x140, negate (sin x143) * (x141 * x140), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDDer (\\x79 [x80 @Natural @Double @[]] -> sin x79 - x80) (\\x82 [x83 @Natural @Double @[]] x84 [x85 @Natural @Double @[]] -> x82 * cos x84 + x83 * rconst -1.0) (\\x89 x90 [x91 @Natural @Double @[]] -> (cos x90 * x89, rconst -1.0 * x89)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0]))), rconst (fromList [2] [5.0,7.0]))"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1)

_testSin0ScanD1Rev3PP :: Assertion
_testSin0ScanD1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                                (V.fromList [odFromSh @Double ZS])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rletDomainsIn (let v104 = rscanDDer (\\x88 [x89 @Natural @Double @[]] -> sin x88 - x89) (\\x92 [x93 @Natural @Double @[]] x94 [x95 @Natural @Double @[]] -> x92 * cos x94 + x93 * rconst -1.0) (\\x100 x101 [x102 @Natural @Double @[]] -> (cos x101 * x100, rconst -1.0 * x100)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0]) ; m105 = rfromList [rappend (rreverse (rscanDDer (\\x106 [x107 @Natural @Double @[], x108 @Natural @Double @[]] -> cos x107 * x106) (\\x117 [x118 @Natural @Double @[], x119 @Natural @Double @[]] x120 [x121 @Natural @Double @[], x122 @Natural @Double @[]] -> (x118 * negate (sin x121)) * x120 + x117 * cos x121) (\\x135 x136 [x137 @Natural @Double @[], x138 @Natural @Double @[]] -> (cos x137 * x135, negate (sin x137) * (x136 * x135), 0)) (rconst 1.0) (rreverse (rslice 0 1 v104), rreplicate 1 (rconst 1.1 * rconst 5.0)))) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rreverse (rscanDDer (\\x190 [x191 @Natural @Double @[], x192 @Natural @Double @[]] -> cos x191 * x190) (\\x201 [x202 @Natural @Double @[], x203 @Natural @Double @[]] x204 [x205 @Natural @Double @[], x206 @Natural @Double @[]] -> (x202 * negate (sin x205)) * x204 + x201 * cos x205) (\\x219 x220 [x221 @Natural @Double @[], x222 @Natural @Double @[]] -> (cos x221 * x219, negate (sin x221) * (x220 * x219), 0)) (rconst 1.0) (rreverse (rslice 0 2 v104), rfromList [rconst 1.1 * rconst 7.0, rconst 1.1 * rconst 5.0]))) (rconstant (rreplicate 0 (rconst 0.0)))] ; v145 = rappend (rreplicate 1 (rconst -1.0 * m105 ! [0, 1])) (rconstant (rreplicate 1 (rconst 0.0))) + rappend (rfromList [rconst -1.0 * m105 ! [1, 1], rconst -1.0 * m105 ! [1, 2]]) (rconstant (rreplicate 0 (rconst 0.0))) in (rconst 5.0 * v145 ! [0] + rconst 7.0 * v145 ! [1] + rconst 1.0 + rsum (rgather [2] m105 (\\[i151] -> [i151, 0])))) (\\[dret @Natural @Double @[]] -> dret)"

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                                (V.fromList [odFromSh @Double ZS])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanDDer (\\x100 [x101 @Natural @Double @[], x102 @Natural @Double @[], x103 @Natural @Double @[]] -> x100 * cos x102 + x101 * rconst -1.0) (\\x114 [x115 @Natural @Double @[], x116 @Natural @Double @[], x117 @Natural @Double @[]] x118 [x119 @Natural @Double @[], x120 @Natural @Double @[], x121 @Natural @Double @[]] -> x115 * rconst -1.0 + x114 * cos x120 + (x116 * negate (sin x120)) * x118) (\\x146 x147 [x148 @Natural @Double @[], x149 @Natural @Double @[], x150 @Natural @Double @[]] -> (cos x149 * x146, rconst -1.0 * x146, negate (sin x149) * (x147 * x146), 0)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanDDer (\\x82 [x83 @Natural @Double @[]] -> sin x82 - x83) (\\x85 [x86 @Natural @Double @[]] x87 [x88 @Natural @Double @[]] -> x85 * cos x87 + x86 * rconst -1.0) (\\x92 x93 [x94 @Natural @Double @[]] -> (cos x93 * x92, rconst -1.0 * x92)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])), rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])"

testSin0ScanD1Rev3 :: Assertion
testSin0ScanD1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [-10.076255083995068] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanD (\x a -> sin x - rfromD (dunDomains (V.fromList [odFromSh @Double ZS]) a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rfromList [x0 * 5, x0 * 7])) 1.1)

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.1])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanD (\x _a -> sin x)
                       (V.fromList [odFromSh @Float ZS])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$ ZS))
     in f) 1.1)

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscanD (\x _a -> sin x)
                   (V.fromList [ odFromSh @Float ZS
                               , odFromSh @Float (3 :$ 4 :$ ZS)])
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
       (\a0 -> rscanD (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7)
                                                     (dunDomains (V.fromList [odFromSh @Float ZS]) a))))
                      (V.fromList [odFromSh @Float ZS])
                      (rreplicate 2 (rreplicate 5 (2 * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanD (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked10 rsum
                                                 $ mapDomainsRanked01
                                                     (rreplicate 7)
                                                     (dunDomains (V.fromList [odFromSh @Int64 ZS]) a))))
                       (V.fromList [odFromSh @Int64 ZS])
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

-- TODO: change back to rev' once simplification of AstShaped is completed
testSin0FoldNestedSi :: Assertion
testSin0FoldNestedSi = do
  assertEqualUpToEpsilon 1e-10
    (-0.20775612781643243 :: Flip OR.Array Double 0)
    (crev (let f :: forall f. ADReadyS f => f Double '[] -> f Double '[3]
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
