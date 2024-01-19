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
  , testCase "4Sin0ScanD1Rev3" testSin0ScanD1Rev3
  , testCase "4Sin0ScanD1Rev3PP" testSin0ScanD1Rev3PP
  , testCase "4Sin0ScanDFwd3PP" testSin0ScanDFwd3PP
  , testCase "4Sin0ScanD0fwd" testSin0ScanD0fwd
  , testCase "4Sin0ScanD1fwd" testSin0ScanD1fwd
  , testCase "4Sin0ScanD8fwd" testSin0ScanD8fwd
  , testCase "4Sin0ScanD8fwd2" testSin0ScanD8fwd2
  , testCase "4Sin0FoldNestedS1" testSin0FoldNestedS1
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
    @?= "let m105 = sscanDer (\\v88 x89 -> atan2 (sreplicate x89) (sreplicate (sin (ssum (sreplicate x89))))) (\\v90 x91 v92 x93 -> let x94 = ssum (sreplicate x93) ; v95 = sreplicate (sin x94) ; v96 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x93 * sreplicate x93 + v95 * v95) ; x97 = ssum (sreplicate x91) ; x98 = x97 * cos x94 in sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x98 * negate (sreplicate x93 * v96) + sreplicate x91 * (v95 * v96)) (\\v99 v100 x101 -> let x102 = ssum (sreplicate x101) ; v103 = sreplicate (sin x102) ; v104 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x101 * sreplicate x101 + v103 * v103) in (0, sconst @[] 0.0 + ssum ((v103 * v104) * v99) + ssum (sreplicate (cos x102 * ssum (negate (sreplicate x101 * v104) * v99))))) (sreplicate (sconstant (rconst 1.1))) (sreplicate (sconstant (rconst 1.1))) ; m122 = sreverse (sscanZipDer (\\v106 [v107 @[Natural] @Double @[5], x108 @[Natural] @Double @[]] -> let x109 = ssum (sreplicate x108) ; v110 = sreplicate (sin x109) ; v111 = recip (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0]) + sreplicate x108 * sreplicate x108 + v110 * v110) in sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) (\\v112 [v113 @[Natural] @Double @[5], x114 @[Natural] @Double @[]] v115 [v116 @[Natural] @Double @[5], x117 @[Natural] @Double @[]] -> sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) (\\v118 v119 [v120 @[Natural] @Double @[5], x121 @[Natural] @Double @[]] -> (0, 0, 0)) (rreplicate 5 (rconst 1.0)) (sreverse (sslice m105), sreverse (sreplicate (sconstant (rconst 1.1))))) in ssum (m122 !$ [0]) + ssum (let v124 = ssum (stranspose (stranspose (sreplicate (sgather (sreplicate (sconstant (rconst 1.1))) (\\[i123] -> [i123]))))) ; m126 = stranspose (sreplicate (sin (sgather v124 (\\[i125] -> [i125])))) ; m129 = recip (sreplicate (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) + sreplicate (sreplicate (sconstant (rconst 1.1)) * sreplicate (sconstant (rconst 1.1))) + sgather m126 (\\[i127] -> [i127]) * sgather m126 (\\[i128] -> [i128]) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0]) + sconst @[1,5] (fromList @[1,5] [0.0,0.0,0.0,0.0,0.0])) ; m130 = sreplicate (sconst @[5] (fromList @[5] [0.0,0.0,0.0,0.0,0.0])) in sreplicate (sconst @[] 0.0) + ssum (stranspose ((sgather m126 (\\[i134] -> [i134]) * sgather m129 (\\[i135] -> [i135])) * sgather m122 (\\[i136] -> [1 + i136]))) + ssum (stranspose (stranspose (sreplicate (cos (sgather v124 (\\[i131] -> [i131])) * ssum (stranspose (negate (sreplicate (sreplicate (sconstant (rconst 1.1))) * sgather m129 (\\[i132] -> [i132])) * sgather m122 (\\[i133] -> [1 + i133]))))))) + sconst @[1] (fromList @[1] [0.0]) + sconst @[1] (fromList @[1] [0.0]))"

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
    @?= "let v58 = rscanDer (\\x49 x50 -> sin x49) (\\x51 x52 x53 x54 -> x51 * cos x53) (\\x55 x56 x57 -> (cos x56 * x55, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0])) in rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x60 [x61 @Natural @Double @[], x62 @Natural @Double @[]] -> cos x61 * x60) (\\x63 [x64 @Natural @Double @[], x65 @Natural @Double @[]] x66 [x67 @Natural @Double @[], x68 @Natural @Double @[]] -> (x64 * negate (sin x67)) * x66 + x63 * cos x67) (\\x72 x73 [x74 @Natural @Double @[], x75 @Natural @Double @[]] -> (cos x74 * x72, negate (sin x74) * (x73 * x72), 0)) (rconst 1.0) (rreverse (rslice 0 1 v58), rconst (fromList [1] [42.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x102 [x103 @Natural @Double @[], x104 @Natural @Double @[]] -> cos x103 * x102) (\\x105 [x106 @Natural @Double @[], x107 @Natural @Double @[]] x108 [x109 @Natural @Double @[], x110 @Natural @Double @[]] -> (x106 * negate (sin x109)) * x108 + x105 * cos x109) (\\x114 x115 [x116 @Natural @Double @[], x117 @Natural @Double @[]] -> (cos x116 * x114, negate (sin x116) * (x115 * x114), 0)) (rconst 1.0) (rreverse (rslice 0 2 v58), rconst (fromList [2] [42.0,42.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i119] -> [i119, i119]))"

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
    @?= "rscanZipDer (\\x58 [x59 @Natural @Double @[], x60 @Natural @Double @[], x61 @Natural @Double @[]] -> x58 * cos x60) (\\x62 [x63 @Natural @Double @[], x64 @Natural @Double @[], x65 @Natural @Double @[]] x66 [x67 @Natural @Double @[], x68 @Natural @Double @[], x69 @Natural @Double @[]] -> x62 * cos x68 + (x64 * negate (sin x68)) * x66) (\\x73 x74 [x75 @Natural @Double @[], x76 @Natural @Double @[], x77 @Natural @Double @[]] -> (cos x76 * x73, 0, negate (sin x76) * (x74 * x73), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDer (\\x48 x49 -> sin x48) (\\x50 x51 x52 x53 -> x50 * cos x52) (\\x54 x55 x56 -> (cos x55 * x54, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0]))), rconst (fromList [2] [42.0,42.0]))"

testSin0Scan1Rev2PP :: Assertion
testSin0Scan1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscan (\x a -> sin x - a) x0
                           (rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v61 = rscanDer (\\x51 x52 -> sin x51 - x52) (\\x53 x54 x55 x56 -> x53 * cos x55 + x54 * rconst -1.0) (\\x58 x59 x60 -> (cos x59 * x58, rconst -1.0 * x58)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0])) in rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x63 [x64 @Natural @Double @[], x65 @Natural @Double @[]] -> cos x64 * x63) (\\x66 [x67 @Natural @Double @[], x68 @Natural @Double @[]] x69 [x70 @Natural @Double @[], x71 @Natural @Double @[]] -> (x67 * negate (sin x70)) * x69 + x66 * cos x70) (\\x75 x76 [x77 @Natural @Double @[], x78 @Natural @Double @[]] -> (cos x77 * x75, negate (sin x77) * (x76 * x75), 0)) (rconst 1.0) (rreverse (rslice 0 1 v61), rconst (fromList [1] [5.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x105 [x106 @Natural @Double @[], x107 @Natural @Double @[]] -> cos x106 * x105) (\\x108 [x109 @Natural @Double @[], x110 @Natural @Double @[]] x111 [x112 @Natural @Double @[], x113 @Natural @Double @[]] -> (x109 * negate (sin x112)) * x111 + x108 * cos x112) (\\x117 x118 [x119 @Natural @Double @[], x120 @Natural @Double @[]] -> (cos x119 * x117, negate (sin x119) * (x118 * x117), 0)) (rconst 1.0) (rreverse (rslice 0 2 v61), rconst (fromList [2] [7.0,5.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i122] -> [i122, i122]))"

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
    @?= "rscanZipDer (\\x68 [x69 @Natural @Double @[], x70 @Natural @Double @[], x71 @Natural @Double @[]] -> x68 * cos x70 + x69 * rconst -1.0) (\\x73 [x74 @Natural @Double @[], x75 @Natural @Double @[], x76 @Natural @Double @[]] x77 [x78 @Natural @Double @[], x79 @Natural @Double @[], x80 @Natural @Double @[]] -> x74 * rconst -1.0 + x73 * cos x79 + (x75 * negate (sin x79)) * x77) (\\x87 x88 [x89 @Natural @Double @[], x90 @Natural @Double @[], x91 @Natural @Double @[]] -> (cos x90 * x87, rconst -1.0 * x87, negate (sin x90) * (x88 * x87), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanDer (\\x57 x58 -> sin x57 - x58) (\\x59 x60 x61 x62 -> x59 * cos x61 + x60 * rconst -1.0) (\\x64 x65 x66 -> (cos x65 * x64, rconst -1.0 * x64)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0]))), rconst (fromList [2] [5.0,7.0]))"

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
    @?= "let v66 = rscanDer (\\x56 x57 -> sin x56 - x57) (\\x58 x59 x60 x61 -> x58 * cos x60 + x59 * rconst -1.0) (\\x63 x64 x65 -> (cos x64 * x63, rconst -1.0 * x63)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0]) ; m67 = rfromList [rappend (rreverse (rscanZipDer (\\x68 [x69 @Natural @Double @[], x70 @Natural @Double @[]] -> cos x69 * x68) (\\x71 [x72 @Natural @Double @[], x73 @Natural @Double @[]] x74 [x75 @Natural @Double @[], x76 @Natural @Double @[]] -> (x72 * negate (sin x75)) * x74 + x71 * cos x75) (\\x80 x81 [x82 @Natural @Double @[], x83 @Natural @Double @[]] -> (cos x82 * x80, negate (sin x82) * (x81 * x80), 0)) (rconst 1.0) (rreverse (rslice 0 1 v66), rreplicate 1 (rconst 1.1 * rconst 5.0)))) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rreverse (rscanZipDer (\\x119 [x120 @Natural @Double @[], x121 @Natural @Double @[]] -> cos x120 * x119) (\\x122 [x123 @Natural @Double @[], x124 @Natural @Double @[]] x125 [x126 @Natural @Double @[], x127 @Natural @Double @[]] -> (x123 * negate (sin x126)) * x125 + x122 * cos x126) (\\x131 x132 [x133 @Natural @Double @[], x134 @Natural @Double @[]] -> (cos x133 * x131, negate (sin x133) * (x132 * x131), 0)) (rconst 1.0) (rreverse (rslice 0 2 v66), rfromList [rconst 1.1 * rconst 7.0, rconst 1.1 * rconst 5.0]))) (rconstant (rreplicate 0 (rconst 0.0)))] ; v85 = rsum (rfromList [rappend (rconstant (rreplicate 1 (rconst -1.0)) * rgather [1] (m67 ! [0]) (\\[i87] -> [1 + i87])) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rconstant (rreplicate 2 (rconst -1.0)) * rgather [2] (m67 ! [1]) (\\[i95] -> [1 + i95])) (rconstant (rreplicate 0 (rconst 0.0)))]) in rconst 5.0 * v85 ! [0] + rconst 7.0 * v85 ! [1] + rconst 1.0 + rsum (rgather [2] m67 (\\[i89] -> [i89, 0]))"

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
    @?= "rscanZipDer (\\x74 [x75 @Natural @Double @[], x76 @Natural @Double @[], x77 @Natural @Double @[]] -> x74 * cos x76 + x75 * rconst -1.0) (\\x79 [x80 @Natural @Double @[], x81 @Natural @Double @[], x82 @Natural @Double @[]] x83 [x84 @Natural @Double @[], x85 @Natural @Double @[], x86 @Natural @Double @[]] -> x80 * rconst -1.0 + x79 * cos x85 + (x81 * negate (sin x85)) * x83) (\\x93 x94 [x95 @Natural @Double @[], x96 @Natural @Double @[], x97 @Natural @Double @[]] -> (cos x96 * x93, rconst -1.0 * x93, negate (sin x96) * (x94 * x93), 0)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanDer (\\x60 x61 -> sin x60 - x61) (\\x62 x63 x64 x65 -> x62 * cos x64 + x63 * rconst -1.0) (\\x67 x68 x69 -> (cos x68 * x67, rconst -1.0 * x67)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])), rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])"

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
                             (V.fromList [odFromSh @Double ZS])
                             x0 (V.singleton $ DynamicRanked
                                 $ rzero @f @Double (0 :$ ZS))
           in f) 1.1)

testSin0ScanD1 :: Assertion
testSin0ScanD1 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [1.4535961214255773] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.constant @Double @1 [1] 42)))
          (rreplicate0N [1,1,1,1,1] 1.1))

testSin0ScanD2 :: Assertion
testSin0ScanD2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1,1,1,1] [2.2207726343670955] :: OR.Array 5 Double)
    (rev' (\x0 -> rscanZip (\x _a -> sin x)
                         (V.fromList [odFromSh @Double ZS])
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
    (rev' (\a0 -> rscanZip (\x a -> atan2 (sin x)
                                        (sin $ rfromD (a V.! 0)))
                         (V.fromList [odFromSh @Double
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
    (rev' (\a0 -> rscanZip (\x a -> rsum
                                 $ atan2 (sin $ rreplicate 5 x)
                                         (rsum $ sin $ rsum
                                          $ rtr $ rreplicate 7
                                          $ rreplicate 2 $ rreplicate 5
                                          $ rsum $ rsum
                                          $ rfromD (a V.! 1)))
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
                 sscanZip
                   (let g :: forall f2. ADReadyS f2
                          => f2 Double '[1,1,1,1] -> Domains (RankedOf f2)
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
    (rev' (\a0 -> rscanZip (\x a -> rtr
                                 $ rtr x + rreplicate 1
                                             (rreplicate 2
                                                (rfromD (a V.! 0))))
                         (V.fromList [odFromSh @Double (1 :$ 1 :$ ZS)])
                         (rreplicate 2 (rreplicate 1 a0))
                         (V.singleton $ DynamicRanked
                          $ rreplicate 2 a0)) (rreplicate0N [1,1] 1.1))

testSin0ScanD7 :: Assertion
testSin0ScanD7 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [1,1] [310] :: OR.Array 2 Double)
    (rev' (\a0 -> rscanZip (\x _a -> rtr $ rreplicate 5
                                   $ (rsum (rtr x)))
                         (V.fromList [odFromSh @Double (1 :$ 1 :$ ZS)])
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
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7) a)))
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
       (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7) a)))
                       (V.fromList [odFromSh @Double ZS])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8rev2 :: Assertion
testSin0ScanD8rev2 = do
  let h = rrev1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked10 rsum
                                                 $ mapDomainsRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [odFromSh @Double ZS])
                       (rreplicate 2 (rreplicate 5 (2 * a0)))
                       (V.singleton $ DynamicRanked $ rreplicate 3 a0))
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [] [285.9579482947575])
    (crev h 1.1)

testSin0ScanD1RevPP :: Assertion
testSin0ScanD1RevPP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [odFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v68 = rscanZipDer (\\x59 [x60 @Natural @Double @[]] -> sin x59) (\\x61 [x62 @Natural @Double @[]] x63 [x64 @Natural @Double @[]] -> x61 * cos x63) (\\x65 x66 [x67 @Natural @Double @[]] -> (cos x66 * x65, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0])) in rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x70 [x71 @Natural @Double @[], x72 @Natural @Double @[]] -> cos x71 * x70) (\\x73 [x74 @Natural @Double @[], x75 @Natural @Double @[]] x76 [x77 @Natural @Double @[], x78 @Natural @Double @[]] -> (x74 * negate (sin x77)) * x76 + x73 * cos x77) (\\x82 x83 [x84 @Natural @Double @[], x85 @Natural @Double @[]] -> (cos x84 * x82, negate (sin x84) * (x83 * x82), 0)) (rconst 1.0) (rreverse (rslice 0 1 v68), rconst (fromList [1] [42.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x116 [x117 @Natural @Double @[], x118 @Natural @Double @[]] -> cos x117 * x116) (\\x119 [x120 @Natural @Double @[], x121 @Natural @Double @[]] x122 [x123 @Natural @Double @[], x124 @Natural @Double @[]] -> (x120 * negate (sin x123)) * x122 + x119 * cos x123) (\\x128 x129 [x130 @Natural @Double @[], x131 @Natural @Double @[]] -> (cos x130 * x128, negate (sin x130) * (x129 * x128), 0)) (rconst 1.0) (rreverse (rslice 0 2 v68), rconst (fromList [2] [42.0,42.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i133] -> [i133, i133]))"

testSin0ScanDFwdPP :: Assertion
testSin0ScanDFwdPP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x _a -> sin x)
                           (V.fromList [odFromSh @Double ZS])
                           x0 (V.singleton $ DynamicRanked
                               $ rconst (OR.constant @Double @1 [2] 42))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanZipDer (\\x58 [x59 @Natural @Double @[], x60 @Natural @Double @[], x61 @Natural @Double @[]] -> x58 * cos x60) (\\x62 [x63 @Natural @Double @[], x64 @Natural @Double @[], x65 @Natural @Double @[]] x66 [x67 @Natural @Double @[], x68 @Natural @Double @[], x69 @Natural @Double @[]] -> x62 * cos x68 + (x64 * negate (sin x68)) * x66) (\\x73 x74 [x75 @Natural @Double @[], x76 @Natural @Double @[], x77 @Natural @Double @[]] -> (cos x76 * x73, 0, negate (sin x76) * (x74 * x73), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanZipDer (\\x48 [x49 @Natural @Double @[]] -> sin x48) (\\x50 [x51 @Natural @Double @[]] x52 [x53 @Natural @Double @[]] -> x50 * cos x52) (\\x54 x55 [x56 @Natural @Double @[]] -> (cos x55 * x54, 0)) (rconst 1.1) (rconst (fromList [2] [42.0,42.0]))), rconst (fromList [2] [42.0,42.0]))"

testSin0ScanD1Rev2PP :: Assertion
testSin0ScanD1Rev2PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                             $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v73 = rscanZipDer (\\x63 [x64 @Natural @Double @[]] -> sin x63 - x64) (\\x65 [x66 @Natural @Double @[]] x67 [x68 @Natural @Double @[]] -> x65 * cos x67 + x66 * rconst -1.0) (\\x70 x71 [x72 @Natural @Double @[]] -> (cos x71 * x70, rconst -1.0 * x70)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0])) in rconst 1.0 + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x75 [x76 @Natural @Double @[], x77 @Natural @Double @[]] -> cos x76 * x75) (\\x78 [x79 @Natural @Double @[], x80 @Natural @Double @[]] x81 [x82 @Natural @Double @[], x83 @Natural @Double @[]] -> (x79 * negate (sin x82)) * x81 + x78 * cos x82) (\\x87 x88 [x89 @Natural @Double @[], x90 @Natural @Double @[]] -> (cos x89 * x87, negate (sin x89) * (x88 * x87), 0)) (rconst 1.0) (rreverse (rslice 0 1 v73), rconst (fromList [1] [5.0])))) (rconstant (rreplicate 1 (rconst 0.0))) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x125 [x126 @Natural @Double @[], x127 @Natural @Double @[]] -> cos x126 * x125) (\\x128 [x129 @Natural @Double @[], x130 @Natural @Double @[]] x131 [x132 @Natural @Double @[], x133 @Natural @Double @[]] -> (x129 * negate (sin x132)) * x131 + x128 * cos x132) (\\x137 x138 [x139 @Natural @Double @[], x140 @Natural @Double @[]] -> (cos x139 * x137, negate (sin x139) * (x138 * x137), 0)) (rconst 1.0) (rreverse (rslice 0 2 v73), rconst (fromList [2] [7.0,5.0])))) (rconstant (rreplicate 0 (rconst 0.0))) ! [0])]) (\\[i142] -> [i142, i142]))"

testSin0ScanDFwd2PP :: Assertion
testSin0ScanDFwd2PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanZipDer (\\x68 [x69 @Natural @Double @[], x70 @Natural @Double @[], x71 @Natural @Double @[]] -> x68 * cos x70 + x69 * rconst -1.0) (\\x73 [x74 @Natural @Double @[], x75 @Natural @Double @[], x76 @Natural @Double @[]] x77 [x78 @Natural @Double @[], x79 @Natural @Double @[], x80 @Natural @Double @[]] -> x74 * rconst -1.0 + x73 * cos x79 + (x75 * negate (sin x79)) * x77) (\\x87 x88 [x89 @Natural @Double @[], x90 @Natural @Double @[], x91 @Natural @Double @[]] -> (cos x90 * x87, rconst -1.0 * x87, negate (sin x90) * (x88 * x87), 0)) (rconst 1.1) (rconstant (rreplicate 2 (rconst 0.0)), rslice 0 2 (rscanZipDer (\\x57 [x58 @Natural @Double @[]] -> sin x57 - x58) (\\x59 [x60 @Natural @Double @[]] x61 [x62 @Natural @Double @[]] -> x59 * cos x61 + x60 * rconst -1.0) (\\x64 x65 [x66 @Natural @Double @[]] -> (cos x65 * x64, rconst -1.0 * x64)) (rconst 1.1) (rconst (fromList [2] [5.0,7.0]))), rconst (fromList [2] [5.0,7.0]))"

testSin0ScanD1Rev2 :: Assertion
testSin0ScanD1Rev2 = do
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [] [1.1961317861865948] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                         (V.fromList [odFromSh @Double ZS])
                         x0 (V.singleton $ DynamicRanked
                         $ rconst (OR.fromList @Double @1 [2] [5, 7]))) 1.1)

testSin0ScanD1Rev3 :: Assertion
testSin0ScanD1Rev3 = do
  assertEqualUpToEpsilon' 1e-5
    (OR.fromList [] [47.150000000000006] :: OR.Array 0 Double)
    (rev' (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [odFromSh @Double ZS])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1)

testSin0ScanD1Rev3PP :: Assertion
testSin0ScanD1Rev3PP = do
  resetVarCounter
  let a1 = rrev1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> x + rfromD (a V.! 0))
                           (V.fromList [odFromSh @Double ZS])
                           x0
                           (V.singleton $ DynamicRanked
                            $ rscan (\x a -> a * x) x0
                                    (rfromList [x0 * 5, x0]))) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v120 = rscanDer (\\x111 x112 -> x112 * x111) (\\x113 x114 x115 x116 -> x114 * x115 + x113 * x116) (\\x117 x118 x119 -> (x119 * x117, x118 * x117)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1]) ; v130 = rscanZipDer (\\x121 [x122 @Natural @Double @[]] -> x121 + x122) (\\x123 [x124 @Natural @Double @[]] x125 [x126 @Natural @Double @[]] -> x123 + x124) (\\x127 x128 [x129 @Natural @Double @[]] -> (x127, x127)) (rconst 1.1) (v120) ; m131 = rfromList [rappend (rreverse (rscanZipDer (\\x132 [x133 @Natural @Double @[], x134 @Natural @Double @[]] -> x132) (\\x135 [x136 @Natural @Double @[], x137 @Natural @Double @[]] x138 [x139 @Natural @Double @[], x140 @Natural @Double @[]] -> x135) (\\x141 x142 [x143 @Natural @Double @[], x144 @Natural @Double @[]] -> (x141, 0, 0)) (rconst 1.0) (rreverse (rslice 0 1 v130), rreverse (rslice 0 1 v120)))) (rconstant (rreplicate 2 (rconst 0.0))), rappend (rreverse (rscanZipDer (\\x241 [x242 @Natural @Double @[], x243 @Natural @Double @[]] -> x241) (\\x244 [x245 @Natural @Double @[], x246 @Natural @Double @[]] x247 [x248 @Natural @Double @[], x249 @Natural @Double @[]] -> x244) (\\x250 x251 [x252 @Natural @Double @[], x253 @Natural @Double @[]] -> (x250, 0, 0)) (rconst 1.0) (rreverse (rslice 0 2 v130), rreverse (rslice 0 2 v120)))) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rreverse (rscanZipDer (\\x273 [x274 @Natural @Double @[], x275 @Natural @Double @[]] -> x273) (\\x276 [x277 @Natural @Double @[], x278 @Natural @Double @[]] x279 [x280 @Natural @Double @[], x281 @Natural @Double @[]] -> x276) (\\x282 x283 [x284 @Natural @Double @[], x285 @Natural @Double @[]] -> (x282, 0, 0)) (rconst 1.0) (rreverse (rslice 0 3 v130), rreverse v120))) (rconstant (rreplicate 0 (rconst 0.0)))] ; v157 = rappend (rgather [3] (m131 ! [2]) (\\[i147] -> [1 + i147])) (rconstant (rreplicate 0 (rconst 0.0))) + rappend (rgather [1] (m131 ! [0]) (\\[i155] -> [1 + i155])) (rconstant (rreplicate 2 (rconst 0.0))) + rappend (rgather [2] (m131 ! [1]) (\\[i151] -> [1 + i151])) (rconstant (rreplicate 1 (rconst 0.0))) ; m158 = rfromList [rappend (rreverse (rscanZipDer (\\x159 [x160 @Natural @Double @[], x161 @Natural @Double @[]] -> x161 * x159) (\\x162 [x163 @Natural @Double @[], x164 @Natural @Double @[]] x165 [x166 @Natural @Double @[], x167 @Natural @Double @[]] -> x164 * x165 + x162 * x167) (\\x169 x170 [x171 @Natural @Double @[], x172 @Natural @Double @[]] -> (x172 * x169, 0, x170 * x169)) (v157 ! [1]) (rreverse (rslice 0 1 v120), rreplicate 1 (rconst 1.1 * rconst 5.0)))) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rreverse (rscanZipDer (\\x197 [x198 @Natural @Double @[], x199 @Natural @Double @[]] -> x199 * x197) (\\x200 [x201 @Natural @Double @[], x202 @Natural @Double @[]] x203 [x204 @Natural @Double @[], x205 @Natural @Double @[]] -> x202 * x203 + x200 * x205) (\\x207 x208 [x209 @Natural @Double @[], x210 @Natural @Double @[]] -> (x210 * x207, 0, x208 * x207)) (v157 ! [2]) (rreverse (rslice 0 2 v120), rfromList [rconst 1.1, rconst 1.1 * rconst 5.0]))) (rconstant (rreplicate 0 (rconst 0.0)))] ; v173 = rsum (rfromList [rappend (rgather [1] v120 (\\[i175] -> [i175]) * rgather [1] (m158 ! [0]) (\\[i176] -> [1 + i176])) (rconstant (rreplicate 1 (rconst 0.0))), rappend (rgather [2] v120 (\\[i216] -> [i216]) * rgather [2] (m158 ! [1]) (\\[i217] -> [1 + i217])) (rconstant (rreplicate 0 (rconst 0.0)))]) in rconst 5.0 * v173 ! [0] + v173 ! [1] + v157 ! [0] + rsum (rgather [2] m158 (\\[i219] -> [i219, 0])) + rconst 1.0 + rsum (rgather [3] m131 (\\[i221] -> [i221, 0]))"

testSin0ScanDFwd3PP :: Assertion
testSin0ScanDFwd3PP = do
  resetVarCounter
  let a1 = rfwd1 @(AstRanked FullSpan) @Double @0 @1
                 (\x0 -> rscanZip (\x a -> sin x - rfromD (a V.! 0))
                                (V.fromList [odFromSh @Double ZS])
                                x0 (V.singleton $ DynamicRanked
                                    $ rfromList [x0 * 5, x0 * 7])) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "rscanZipDer (\\x74 [x75 @Natural @Double @[], x76 @Natural @Double @[], x77 @Natural @Double @[]] -> x74 * cos x76 + x75 * rconst -1.0) (\\x79 [x80 @Natural @Double @[], x81 @Natural @Double @[], x82 @Natural @Double @[]] x83 [x84 @Natural @Double @[], x85 @Natural @Double @[], x86 @Natural @Double @[]] -> x80 * rconst -1.0 + x79 * cos x85 + (x81 * negate (sin x85)) * x83) (\\x93 x94 [x95 @Natural @Double @[], x96 @Natural @Double @[], x97 @Natural @Double @[]] -> (cos x96 * x93, rconst -1.0 * x93, negate (sin x96) * (x94 * x93), 0)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0], rslice 0 2 (rscanZipDer (\\x60 [x61 @Natural @Double @[]] -> sin x60 - x61) (\\x62 [x63 @Natural @Double @[]] x64 [x65 @Natural @Double @[]] -> x62 * cos x64 + x63 * rconst -1.0) (\\x67 x68 [x69 @Natural @Double @[]] -> (cos x68 * x67, rconst -1.0 * x67)) (rconst 1.1) (rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])), rfromList [rconst 1.1 * rconst 5.0, rconst 1.1 * rconst 7.0])"

testSin0ScanD0fwd :: Assertion
testSin0ScanD0fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [1] [1.1])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (let f :: forall f. ADReady f => f Double 0 -> f Double 1
         f x0 = rscanZip (\x _a -> sin x)
                       (V.fromList [odFromSh @Double ZS])
                       x0 (V.singleton $ DynamicRanked
                           $ rzero @f @Double (0 :$ ZS))
     in f) 1.1)

testSin0ScanD1fwd :: Assertion
testSin0ScanD1fwd = do
  assertEqualUpToEpsilon 1e-10
    (Flip $ OR.fromList [2] [1.1,0.4989557335681351])
    (rfwd1 @(Flip OR.Array) @Double @0 @1
    (\x0 -> rscanZip (\x _a -> sin x)
                   (V.fromList [ odFromSh @Double ZS
                               , odFromSh @Double (3 :$ 4 :$ ZS)])
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
                                                 $ mapDomainsRanked
                                                     (rsum . rreplicate 7) a)))
                      (V.fromList [odFromSh @Double ZS])
                      (rreplicate 2 (rreplicate 5 (2 * a0)))
                      (V.singleton $ DynamicRanked $ rreplicate 3 a0)) 1.1)

testSin0ScanD8fwd2 :: Assertion
testSin0ScanD8fwd2 = do
  let h = rfwd1 @(ADVal (Flip OR.Array)) @Double @0 @3
        (\a0 -> rscanZip (\x a -> rtr $ rreplicate 5
                                 $ atan2 (rsum (rtr $ sin x))
                                         (rreplicate 2
                                          $ sin (rfromD $ (V.! 0)
                                                 $ mapDomainsRanked10 rsum
                                                 $ mapDomainsRanked01
                                                     (rreplicate 7) a)))
                       (V.fromList [odFromSh @Double ZS])
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
    (6.213134457780058e-8 :: OR.Array 0 Double)
    (rev' (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                          rfold (\x3 a3 -> 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) a
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) x (rreplicate 2 a)))
                            a0 (rreplicate 2 a0)
           in f) 1.1)

testSin0FoldNestedR21PP :: Assertion
testSin0FoldNestedR21PP = do
  resetVarCounter
  let a1 =
        rrev1 @(AstRanked FullSpan) @Double @0 @0
          (let f :: forall f. ADReady f => f Double 0 -> f Double 0
               f a0 = rfold (\x a ->
                          rfold (\x3 a3 -> 0.1 * x3 * a3)
                                (rfold (\x4 a4 -> x4 * a4) a
                                       (rreplicate 2 x))
                                (rscan (\x4 a4 -> x4 + a4) x (rreplicate 2 a)))
                            a0 (rreplicate 2 a0)
           in f) 1.1
  printAstPretty IM.empty (simplifyAst6 a1)
    @?= "let v2281 = rscanDer (\\x2055 x2056 -> rfoldDer (\\x2057 x2058 -> (rconst 0.1 * x2057) * x2058) (\\x2077 x2078 x2079 x2080 -> (x2077 * rconst 0.1) * x2080 + x2078 * (rconst 0.1 * x2079)) (\\x2083 x2084 x2085 -> (rconst 0.1 * (x2085 * x2083), (rconst 0.1 * x2084) * x2083)) (rfoldDer (\\x2059 x2060 -> x2059 * x2060) (\\x2061 x2062 x2063 x2064 -> x2061 * x2064 + x2062 * x2063) (\\x2065 x2066 x2067 -> (x2067 * x2065, x2066 * x2065)) x2056 (rreplicate 2 x2055)) (rscanDer (\\x2068 x2069 -> x2068 + x2069) (\\x2070 x2071 x2072 x2073 -> x2070 + x2071) (\\x2074 x2075 x2076 -> (x2074, x2074)) x2055 (rreplicate 2 x2056))) (\\x2087 x2088 x2089 x2090 -> let v2100 = rscanDer (\\x2091 x2092 -> x2091 * x2092) (\\x2093 x2094 x2095 x2096 -> x2093 * x2096 + x2094 * x2095) (\\x2097 x2098 x2099 -> (x2099 * x2097, x2098 * x2097)) x2090 (rreplicate 2 x2089) ; v2110 = rscanDer (\\x2101 x2102 -> x2101 + x2102) (\\x2103 x2104 x2105 x2106 -> x2103 + x2104) (\\x2107 x2108 x2109 -> (x2107, x2107)) x2089 (rreplicate 2 x2090) in rfoldZipDer (\\x2141 [x2142 @Natural @Double @[], x2143 @Natural @Double @[], x2144 @Natural @Double @[]] -> (x2141 * rconst 0.1) * x2144 + x2142 * (rconst 0.1 * x2143)) (\\x2166 [x2167 @Natural @Double @[], x2168 @Natural @Double @[], x2169 @Natural @Double @[]] x2170 [x2171 @Natural @Double @[], x2172 @Natural @Double @[], x2173 @Natural @Double @[]] -> (x2166 * rconst 0.1) * x2173 + x2169 * (x2170 * rconst 0.1) + x2167 * (rconst 0.1 * x2172) + (x2168 * rconst 0.1) * x2171) (\\x2180 x2181 [x2182 @Natural @Double @[], x2183 @Natural @Double @[], x2184 @Natural @Double @[]] -> (rconst 0.1 * (x2184 * x2180), (rconst 0.1 * x2183) * x2180, rconst 0.1 * (x2182 * x2180), (x2181 * rconst 0.1) * x2180)) (rfoldZipDer (\\x2145 [x2146 @Natural @Double @[], x2147 @Natural @Double @[], x2148 @Natural @Double @[]] -> x2145 * x2148 + x2146 * x2147) (\\x2149 [x2150 @Natural @Double @[], x2151 @Natural @Double @[], x2152 @Natural @Double @[]] x2153 [x2154 @Natural @Double @[], x2155 @Natural @Double @[], x2156 @Natural @Double @[]] -> x2149 * x2156 + x2152 * x2153 + x2150 * x2155 + x2151 * x2154) (\\x2159 x2160 [x2161 @Natural @Double @[], x2162 @Natural @Double @[], x2163 @Natural @Double @[]] -> (x2163 * x2159, x2162 * x2159, x2161 * x2159, x2160 * x2159)) x2088 (rreplicate 2 x2087, rslice 0 2 v2100, rreplicate 2 x2089)) (rscanZipDer (\\x2124 [x2125 @Natural @Double @[], x2126 @Natural @Double @[], x2127 @Natural @Double @[]] -> x2124 + x2125) (\\x2128 [x2129 @Natural @Double @[], x2130 @Natural @Double @[], x2131 @Natural @Double @[]] x2132 [x2133 @Natural @Double @[], x2134 @Natural @Double @[], x2135 @Natural @Double @[]] -> x2128 + x2129) (\\x2136 x2137 [x2138 @Natural @Double @[], x2139 @Natural @Double @[], x2140 @Natural @Double @[]] -> (x2136, x2136, 0, 0)) x2087 (rreplicate 2 x2088, rslice 0 2 v2110, rreplicate 2 x2090), rslice 0 3 (rscanDer (\\x2111 x2112 -> (rconst 0.1 * x2111) * x2112) (\\x2113 x2114 x2115 x2116 -> (x2113 * rconst 0.1) * x2116 + x2114 * (rconst 0.1 * x2115)) (\\x2119 x2120 x2121 -> (rconst 0.1 * (x2121 * x2119), (rconst 0.1 * x2120) * x2119)) (v2100 ! [2]) v2110), v2110)) (\\x2187 x2188 x2189 -> let v2199 = rscanDer (\\x2190 x2191 -> x2190 * x2191) (\\x2192 x2193 x2194 x2195 -> x2192 * x2195 + x2193 * x2194) (\\x2196 x2197 x2198 -> (x2198 * x2196, x2197 * x2196)) x2189 (rreplicate 2 x2188) ; v2209 = rscanDer (\\x2200 x2201 -> x2200 + x2201) (\\x2202 x2203 x2204 x2205 -> x2202 + x2203) (\\x2206 x2207 x2208 -> (x2206, x2206)) x2188 (rreplicate 2 x2189) ; v2222 = rscanDer (\\x2210 x2211 -> (rconst 0.1 * x2210) * x2211) (\\x2212 x2213 x2214 x2215 -> (x2212 * rconst 0.1) * x2215 + x2213 * (rconst 0.1 * x2214)) (\\x2218 x2219 x2220 -> (rconst 0.1 * (x2220 * x2218), (rconst 0.1 * x2219) * x2218)) (v2199 ! [2]) v2209 ; v2241 = rreverse (rscanZipDer (\\x2223 [x2224 @Natural @Double @[], x2225 @Natural @Double @[]] -> rconst 0.1 * (x2225 * x2223)) (\\x2227 [x2228 @Natural @Double @[], x2229 @Natural @Double @[]] x2230 [x2231 @Natural @Double @[], x2232 @Natural @Double @[]] -> (x2229 * x2230 + x2227 * x2232) * rconst 0.1) (\\x2235 x2236 [x2237 @Natural @Double @[], x2238 @Natural @Double @[]] -> let x2240 = rconst 0.1 * x2235 in (x2238 * x2240, 0, x2236 * x2240)) x2187 (rreverse (rslice 0 3 v2222), rreverse v2209)) ; v2256 = rreverse (rscanZipDer (\\x2243 [x2244 @Natural @Double @[], x2245 @Natural @Double @[]] -> x2245 * x2243) (\\x2246 [x2247 @Natural @Double @[], x2248 @Natural @Double @[]] x2249 [x2250 @Natural @Double @[], x2251 @Natural @Double @[]] -> x2248 * x2249 + x2246 * x2251) (\\x2252 x2253 [x2254 @Natural @Double @[], x2255 @Natural @Double @[]] -> (x2255 * x2252, 0, x2253 * x2252)) (v2241 ! [0]) (rreverse (rslice 0 2 v2199), rreplicate 2 x2188)) ; v2261 = (rreplicate 3 (rconst 0.1) * rslice 0 3 v2222) * rgather [3] v2241 (\\[i2260] -> [1 + i2260]) ; m2262 = rfromList [rappend (rreverse (rscanZipDer (\\x2263 [x2264 @Natural @Double @[], x2265 @Natural @Double @[]] -> x2263) (\\x2266 [x2267 @Natural @Double @[], x2268 @Natural @Double @[]] x2269 [x2270 @Natural @Double @[], x2271 @Natural @Double @[]] -> x2266) (\\x2272 x2273 [x2274 @Natural @Double @[], x2275 @Natural @Double @[]] -> (x2272, 0, 0)) (v2261 ! [1]) (rreverse (rslice 0 1 v2209), rreplicate 1 x2189))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x4278 [x4279 @Natural @Double @[], x4280 @Natural @Double @[]] -> x4278) (\\x4281 [x4282 @Natural @Double @[], x4283 @Natural @Double @[]] x4284 [x4285 @Natural @Double @[], x4286 @Natural @Double @[]] -> x4281) (\\x4287 x4288 [x4289 @Natural @Double @[], x4290 @Natural @Double @[]] -> (x4287, 0, 0)) (v2261 ! [2]) (rreverse (rslice 0 2 v2209), rreplicate 2 x2189))) (rreplicate 0 (rconst 0.0))] in (rsum (rgather [2] v2199 (\\[i2277] -> [i2277]) * rgather [2] v2256 (\\[i2278] -> [1 + i2278])) + v2261 ! [0] + rsum (rgather [2] m2262 (\\[i4258] -> [i4258, 0])), rsum (rgather [4] (rfromList [rgather [4] (rappend (rgather [1] (m2262 ! [0]) (\\[i2280] -> [1 + i2280])) (rreplicate 1 (rconst 0.0))) (\\[i4259] -> [rem i4259 2]), rgather [4] (rappend (rgather [2] (m2262 ! [1]) (\\[i4263] -> [1 + i4263])) (rreplicate 0 (rconst 0.0))) (\\[i4259] -> [rem i4259 2])]) (\\[i4264] -> [rem (quot i4264 2) 2, i4264])) + v2256 ! [0])) (rconst 1.1) (rconstant (rreplicate 2 (rconst 1.1))) ; v4058 = rreverse (rscanZipDer (\\x2283 [x2284 @Natural @Double @[], x2285 @Natural @Double @[]] -> let v2295 = rscanDer (\\x2286 x2287 -> x2286 * x2287) (\\x2288 x2289 x2290 x2291 -> x2288 * x2291 + x2289 * x2290) (\\x2292 x2293 x2294 -> (x2294 * x2292, x2293 * x2292)) x2285 (rreplicate 2 x2284) ; v2305 = rscanDer (\\x2296 x2297 -> x2296 + x2297) (\\x2298 x2299 x2300 x2301 -> x2298 + x2299) (\\x2302 x2303 x2304 -> (x2302, x2302)) x2284 (rreplicate 2 x2285) ; v2318 = rscanDer (\\x2306 x2307 -> (rconst 0.1 * x2306) * x2307) (\\x2308 x2309 x2310 x2311 -> (x2308 * rconst 0.1) * x2311 + x2309 * (rconst 0.1 * x2310)) (\\x2314 x2315 x2316 -> (rconst 0.1 * (x2316 * x2314), (rconst 0.1 * x2315) * x2314)) (v2295 ! [2]) v2305 ; v2337 = rreverse (rscanZipDer (\\x2319 [x2320 @Natural @Double @[], x2321 @Natural @Double @[]] -> rconst 0.1 * (x2321 * x2319)) (\\x2323 [x2324 @Natural @Double @[], x2325 @Natural @Double @[]] x2326 [x2327 @Natural @Double @[], x2328 @Natural @Double @[]] -> (x2325 * x2326 + x2323 * x2328) * rconst 0.1) (\\x2331 x2332 [x2333 @Natural @Double @[], x2334 @Natural @Double @[]] -> let x2336 = rconst 0.1 * x2331 in (x2334 * x2336, 0, x2332 * x2336)) x2283 (rreverse (rslice 0 3 v2318), rreverse v2305)) ; v2357 = (rreplicate 3 (rconst 0.1) * rslice 0 3 v2318) * rgather [3] v2337 (\\[i2356] -> [1 + i2356]) in rsum (rgather [2] v2295 (\\[i2373] -> [i2373]) * rgather [2] (rscanZipDer (\\x2339 [x2340 @Natural @Double @[], x2341 @Natural @Double @[]] -> x2341 * x2339) (\\x2342 [x2343 @Natural @Double @[], x2344 @Natural @Double @[]] x2345 [x2346 @Natural @Double @[], x2347 @Natural @Double @[]] -> x2344 * x2345 + x2342 * x2347) (\\x2348 x2349 [x2350 @Natural @Double @[], x2351 @Natural @Double @[]] -> (x2351 * x2348, 0, x2349 * x2348)) (v2337 ! [0]) (rreverse (rslice 0 2 v2295), rreplicate 2 x2284)) (\\[i2374] -> [1 + negate i2374])) + v2357 ! [0] + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x2359 [x2360 @Natural @Double @[], x2361 @Natural @Double @[]] -> x2359) (\\x2362 [x2363 @Natural @Double @[], x2364 @Natural @Double @[]] x2365 [x2366 @Natural @Double @[], x2367 @Natural @Double @[]] -> x2362) (\\x2368 x2369 [x2370 @Natural @Double @[], x2371 @Natural @Double @[]] -> (x2368, 0, 0)) (v2357 ! [1]) (rreverse (rslice 0 1 v2305), rreplicate 1 x2285))) (rreplicate 1 (rconst 0.0)) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x4306 [x4307 @Natural @Double @[], x4308 @Natural @Double @[]] -> x4306) (\\x4309 [x4310 @Natural @Double @[], x4311 @Natural @Double @[]] x4312 [x4313 @Natural @Double @[], x4314 @Natural @Double @[]] -> x4309) (\\x4315 x4316 [x4317 @Natural @Double @[], x4318 @Natural @Double @[]] -> (x4315, 0, 0)) (v2357 ! [2]) (rreverse (rslice 0 2 v2305), rreplicate 2 x2285))) (rreplicate 0 (rconst 0.0)) ! [0])]) (\\[i4319] -> [i4319, i4319]))) (\\x2375 [x2376 @Natural @Double @[], x2377 @Natural @Double @[]] x2378 [x2379 @Natural @Double @[], x2380 @Natural @Double @[]] -> let v2390 = rscanDer (\\x2381 x2382 -> x2381 * x2382) (\\x2383 x2384 x2385 x2386 -> x2383 * x2386 + x2384 * x2385) (\\x2387 x2388 x2389 -> (x2389 * x2387, x2388 * x2387)) x2380 (rreplicate 2 x2379) ; v2400 = rscanDer (\\x2391 x2392 -> x2391 + x2392) (\\x2393 x2394 x2395 x2396 -> x2393 + x2394) (\\x2397 x2398 x2399 -> (x2397, x2397)) x2379 (rreplicate 2 x2380) ; v2413 = rscanDer (\\x2401 x2402 -> (rconst 0.1 * x2401) * x2402) (\\x2403 x2404 x2405 x2406 -> (x2403 * rconst 0.1) * x2406 + x2404 * (rconst 0.1 * x2405)) (\\x2409 x2410 x2411 -> (rconst 0.1 * (x2411 * x2409), (rconst 0.1 * x2410) * x2409)) (v2390 ! [2]) v2400 ; v2432 = rscanZipDer (\\x2414 [x2415 @Natural @Double @[], x2416 @Natural @Double @[]] -> rconst 0.1 * (x2416 * x2414)) (\\x2418 [x2419 @Natural @Double @[], x2420 @Natural @Double @[]] x2421 [x2422 @Natural @Double @[], x2423 @Natural @Double @[]] -> (x2420 * x2421 + x2418 * x2423) * rconst 0.1) (\\x2426 x2427 [x2428 @Natural @Double @[], x2429 @Natural @Double @[]] -> let x2431 = rconst 0.1 * x2426 in (x2429 * x2431, 0, x2427 * x2431)) x2378 (rreverse (rslice 0 3 v2413), rreverse v2400) ; v2433 = rreverse v2432 ; v2448 = rscanZipDer (\\x2435 [x2436 @Natural @Double @[], x2437 @Natural @Double @[]] -> x2437 * x2435) (\\x2438 [x2439 @Natural @Double @[], x2440 @Natural @Double @[]] x2441 [x2442 @Natural @Double @[], x2443 @Natural @Double @[]] -> x2440 * x2441 + x2438 * x2443) (\\x2444 x2445 [x2446 @Natural @Double @[], x2447 @Natural @Double @[]] -> (x2447 * x2444, 0, x2445 * x2444)) (v2433 ! [0]) (rreverse (rslice 0 2 v2390), rreplicate 2 x2379) ; v2450 = rreplicate 3 (rconst 0.1) * rslice 0 3 v2413 ; v2452 = rgather [3] v2433 (\\[i2451] -> [1 + i2451]) ; v2453 = v2450 * v2452 ; x2529 = rscanZipDer (\\x2509 [x2510 @Natural @Double @[], x2511 @Natural @Double @[], x2512 @Natural @Double @[]] -> x2509 * x2512 + x2510 * x2511) (\\x2513 [x2514 @Natural @Double @[], x2515 @Natural @Double @[], x2516 @Natural @Double @[]] x2517 [x2518 @Natural @Double @[], x2519 @Natural @Double @[], x2520 @Natural @Double @[]] -> x2513 * x2520 + x2516 * x2517 + x2514 * x2519 + x2515 * x2518) (\\x2524 x2525 [x2526 @Natural @Double @[], x2527 @Natural @Double @[], x2528 @Natural @Double @[]] -> (x2528 * x2524, x2527 * x2524, x2526 * x2524, x2525 * x2524)) x2377 (rreplicate 2 x2376, rslice 0 2 v2390, rreplicate 2 x2379) ! [2] ; v2631 = rreverse (rscanZipDer (\\x2597 [x2598 @Natural @Double @[], x2599 @Natural @Double @[], x2600 @Natural @Double @[], x2601 @Natural @Double @[], x2602 @Natural @Double @[]] -> (x2599 * x2600 + x2597 * x2602) * rconst 0.1) (\\x2605 [x2606 @Natural @Double @[], x2607 @Natural @Double @[], x2608 @Natural @Double @[], x2609 @Natural @Double @[], x2610 @Natural @Double @[]] x2611 [x2612 @Natural @Double @[], x2613 @Natural @Double @[], x2614 @Natural @Double @[], x2615 @Natural @Double @[], x2616 @Natural @Double @[]] -> (x2607 * x2614 + x2608 * x2613 + x2605 * x2616 + x2610 * x2611) * rconst 0.1) (\\x2622 x2623 [x2624 @Natural @Double @[], x2625 @Natural @Double @[], x2626 @Natural @Double @[], x2627 @Natural @Double @[], x2628 @Natural @Double @[]] -> let x2630 = rconst 0.1 * x2622 in (x2628 * x2630, 0, x2626 * x2630, x2625 * x2630, 0, x2623 * x2630)) x2375 (rreverse (rslice 0 3 (rscanZipDer (\\x2548 [x2549 @Natural @Double @[], x2550 @Natural @Double @[], x2551 @Natural @Double @[]] -> (x2548 * rconst 0.1) * x2551 + x2549 * (rconst 0.1 * x2550)) (\\x2554 [x2555 @Natural @Double @[], x2556 @Natural @Double @[], x2557 @Natural @Double @[]] x2558 [x2559 @Natural @Double @[], x2560 @Natural @Double @[], x2561 @Natural @Double @[]] -> (x2554 * rconst 0.1) * x2561 + x2557 * (x2558 * rconst 0.1) + x2555 * (rconst 0.1 * x2560) + (x2556 * rconst 0.1) * x2559) (\\x2569 x2570 [x2571 @Natural @Double @[], x2572 @Natural @Double @[], x2573 @Natural @Double @[]] -> (rconst 0.1 * (x2573 * x2569), (rconst 0.1 * x2572) * x2569, rconst 0.1 * (x2571 * x2569), (x2570 * rconst 0.1) * x2569)) x2529 (rscanZipDer (\\x2530 [x2531 @Natural @Double @[], x2532 @Natural @Double @[], x2533 @Natural @Double @[]] -> x2530 + x2531) (\\x2534 [x2535 @Natural @Double @[], x2536 @Natural @Double @[], x2537 @Natural @Double @[]] x2538 [x2539 @Natural @Double @[], x2540 @Natural @Double @[], x2541 @Natural @Double @[]] -> x2534 + x2535) (\\x2543 x2544 [x2545 @Natural @Double @[], x2546 @Natural @Double @[], x2547 @Natural @Double @[]] -> (x2543, x2543, 0, 0)) x2376 (rreplicate 2 x2377, rslice 0 2 v2400, rreplicate 2 x2380), rslice 0 3 v2413, v2400))), rreverse (rscanZipDer (\\x2578 [x2579 @Natural @Double @[], x2580 @Natural @Double @[], x2581 @Natural @Double @[]] -> x2578 + x2579) (\\x2582 [x2583 @Natural @Double @[], x2584 @Natural @Double @[], x2585 @Natural @Double @[]] x2586 [x2587 @Natural @Double @[], x2588 @Natural @Double @[], x2589 @Natural @Double @[]] -> x2582 + x2583) (\\x2591 x2592 [x2593 @Natural @Double @[], x2594 @Natural @Double @[], x2595 @Natural @Double @[]] -> (x2591, x2591, 0, 0)) x2376 (rreplicate 2 x2377, rslice 0 2 v2400, rreplicate 2 x2380)), rslice 0 3 v2432, rreverse (rslice 0 3 v2413), rreverse v2400)) ; v2739 = (rreplicate 3 (rconst 0.0) * rslice 0 3 v2413 + rslice 0 3 (rscanZipDer (\\x2707 [x2708 @Natural @Double @[], x2709 @Natural @Double @[], x2710 @Natural @Double @[]] -> (x2707 * rconst 0.1) * x2710 + x2708 * (rconst 0.1 * x2709)) (\\x2713 [x2714 @Natural @Double @[], x2715 @Natural @Double @[], x2716 @Natural @Double @[]] x2717 [x2718 @Natural @Double @[], x2719 @Natural @Double @[], x2720 @Natural @Double @[]] -> (x2713 * rconst 0.1) * x2720 + x2716 * (x2717 * rconst 0.1) + x2714 * (rconst 0.1 * x2719) + (x2715 * rconst 0.1) * x2718) (\\x2728 x2729 [x2730 @Natural @Double @[], x2731 @Natural @Double @[], x2732 @Natural @Double @[]] -> (rconst 0.1 * (x2732 * x2728), (rconst 0.1 * x2731) * x2728, rconst 0.1 * (x2730 * x2728), (x2729 * rconst 0.1) * x2728)) x2529 (rscanZipDer (\\x2689 [x2690 @Natural @Double @[], x2691 @Natural @Double @[], x2692 @Natural @Double @[]] -> x2689 + x2690) (\\x2693 [x2694 @Natural @Double @[], x2695 @Natural @Double @[], x2696 @Natural @Double @[]] x2697 [x2698 @Natural @Double @[], x2699 @Natural @Double @[], x2700 @Natural @Double @[]] -> x2693 + x2694) (\\x2702 x2703 [x2704 @Natural @Double @[], x2705 @Natural @Double @[], x2706 @Natural @Double @[]] -> (x2702, x2702, 0, 0)) x2376 (rreplicate 2 x2377, rslice 0 2 v2400, rreplicate 2 x2380), rslice 0 3 v2413, v2400)) * rreplicate 3 (rconst 0.1)) * v2452 + rgather [3] v2631 (\\[i2737] -> [1 + i2737]) * v2450 in rsum (rgather [2] v2448 (\\[i2485] -> [1 + negate i2485]) * rgather [2] (rscanZipDer (\\x2487 [x2488 @Natural @Double @[], x2489 @Natural @Double @[], x2490 @Natural @Double @[]] -> x2487 * x2490 + x2488 * x2489) (\\x2491 [x2492 @Natural @Double @[], x2493 @Natural @Double @[], x2494 @Natural @Double @[]] x2495 [x2496 @Natural @Double @[], x2497 @Natural @Double @[], x2498 @Natural @Double @[]] -> x2491 * x2498 + x2494 * x2495 + x2492 * x2497 + x2493 * x2496) (\\x2502 x2503 [x2504 @Natural @Double @[], x2505 @Natural @Double @[], x2506 @Natural @Double @[]] -> (x2506 * x2502, x2505 * x2502, x2504 * x2502, x2503 * x2502)) x2377 (rreplicate 2 x2376, rslice 0 2 v2390, rreplicate 2 x2379)) (\\[i2507] -> [i2507])) + rsum (rgather [2] v2390 (\\[i2483] -> [i2483]) * rgather [2] (rscanZipDer (\\x2656 [x2657 @Natural @Double @[], x2658 @Natural @Double @[], x2659 @Natural @Double @[], x2660 @Natural @Double @[], x2661 @Natural @Double @[]] -> x2658 * x2659 + x2656 * x2661) (\\x2662 [x2663 @Natural @Double @[], x2664 @Natural @Double @[], x2665 @Natural @Double @[], x2666 @Natural @Double @[], x2667 @Natural @Double @[]] x2668 [x2669 @Natural @Double @[], x2670 @Natural @Double @[], x2671 @Natural @Double @[], x2672 @Natural @Double @[], x2673 @Natural @Double @[]] -> x2664 * x2671 + x2665 * x2670 + x2662 * x2673 + x2667 * x2668) (\\x2677 x2678 [x2679 @Natural @Double @[], x2680 @Natural @Double @[], x2681 @Natural @Double @[], x2682 @Natural @Double @[], x2683 @Natural @Double @[]] -> (x2683 * x2677, 0, x2681 * x2677, x2680 * x2677, 0, x2678 * x2677)) (v2631 ! [0]) (rreverse (rslice 0 2 (rscanZipDer (\\x2633 [x2634 @Natural @Double @[], x2635 @Natural @Double @[], x2636 @Natural @Double @[]] -> x2633 * x2636 + x2634 * x2635) (\\x2637 [x2638 @Natural @Double @[], x2639 @Natural @Double @[], x2640 @Natural @Double @[]] x2641 [x2642 @Natural @Double @[], x2643 @Natural @Double @[], x2644 @Natural @Double @[]] -> x2637 * x2644 + x2640 * x2641 + x2638 * x2643 + x2639 * x2642) (\\x2648 x2649 [x2650 @Natural @Double @[], x2651 @Natural @Double @[], x2652 @Natural @Double @[]] -> (x2652 * x2648, x2651 * x2648, x2650 * x2648, x2649 * x2648)) x2377 (rreplicate 2 x2376, rslice 0 2 v2390, rreplicate 2 x2379))), rreplicate 2 x2376, rslice 0 2 v2448, rreverse (rslice 0 2 v2390), rreplicate 2 x2379)) (\\[i2685] -> [1 + negate i2685])) + v2739 ! [0] + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x2763 [x2764 @Natural @Double @[], x2765 @Natural @Double @[], x2766 @Natural @Double @[], x2767 @Natural @Double @[], x2768 @Natural @Double @[]] -> x2763) (\\x2769 [x2770 @Natural @Double @[], x2771 @Natural @Double @[], x2772 @Natural @Double @[], x2773 @Natural @Double @[], x2774 @Natural @Double @[]] x2775 [x2776 @Natural @Double @[], x2777 @Natural @Double @[], x2778 @Natural @Double @[], x2779 @Natural @Double @[], x2780 @Natural @Double @[]] -> x2769) (\\x2781 x2782 [x2783 @Natural @Double @[], x2784 @Natural @Double @[], x2785 @Natural @Double @[], x2786 @Natural @Double @[], x2787 @Natural @Double @[]] -> (x2781, 0, 0, 0, 0, 0)) (v2739 ! [1]) (rreverse (rslice 0 1 (rscanZipDer (\\x2742 [x2743 @Natural @Double @[], x2744 @Natural @Double @[], x2745 @Natural @Double @[]] -> x2742 + x2743) (\\x2746 [x2747 @Natural @Double @[], x2748 @Natural @Double @[], x2749 @Natural @Double @[]] x2750 [x2751 @Natural @Double @[], x2752 @Natural @Double @[], x2753 @Natural @Double @[]] -> x2746 + x2747) (\\x2755 x2756 [x2757 @Natural @Double @[], x2758 @Natural @Double @[], x2759 @Natural @Double @[]] -> (x2755, x2755, 0, 0)) x2376 (rreplicate 2 x2377, rslice 0 2 v2400, rreplicate 2 x2380))), rreplicate 1 x2377, rslice 0 1 (rscanZipDer (\\x2454 [x2455 @Natural @Double @[], x2456 @Natural @Double @[]] -> x2454) (\\x2457 [x2458 @Natural @Double @[], x2459 @Natural @Double @[]] x2460 [x2461 @Natural @Double @[], x2462 @Natural @Double @[]] -> x2457) (\\x2463 x2464 [x2465 @Natural @Double @[], x2466 @Natural @Double @[]] -> (x2463, 0, 0)) (v2453 ! [1]) (rreverse (rslice 0 1 v2400), rreplicate 1 x2380)), rreverse (rslice 0 1 v2400), rreplicate 1 x2380))) (rreplicate 1 (rconst 0.0)) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x2813 [x2814 @Natural @Double @[], x2815 @Natural @Double @[], x2816 @Natural @Double @[], x2817 @Natural @Double @[], x2818 @Natural @Double @[]] -> x2813) (\\x2819 [x2820 @Natural @Double @[], x2821 @Natural @Double @[], x2822 @Natural @Double @[], x2823 @Natural @Double @[], x2824 @Natural @Double @[]] x2825 [x2826 @Natural @Double @[], x2827 @Natural @Double @[], x2828 @Natural @Double @[], x2829 @Natural @Double @[], x2830 @Natural @Double @[]] -> x2819) (\\x2831 x2832 [x2833 @Natural @Double @[], x2834 @Natural @Double @[], x2835 @Natural @Double @[], x2836 @Natural @Double @[], x2837 @Natural @Double @[]] -> (x2831, 0, 0, 0, 0, 0)) (v2739 ! [2]) (rreverse (rslice 0 2 (rscanZipDer (\\x2792 [x2793 @Natural @Double @[], x2794 @Natural @Double @[], x2795 @Natural @Double @[]] -> x2792 + x2793) (\\x2796 [x2797 @Natural @Double @[], x2798 @Natural @Double @[], x2799 @Natural @Double @[]] x2800 [x2801 @Natural @Double @[], x2802 @Natural @Double @[], x2803 @Natural @Double @[]] -> x2796 + x2797) (\\x2805 x2806 [x2807 @Natural @Double @[], x2808 @Natural @Double @[], x2809 @Natural @Double @[]] -> (x2805, x2805, 0, 0)) x2376 (rreplicate 2 x2377, rslice 0 2 v2400, rreplicate 2 x2380))), rreplicate 2 x2377, rslice 0 2 (rscanZipDer (\\x2468 [x2469 @Natural @Double @[], x2470 @Natural @Double @[]] -> x2468) (\\x2471 [x2472 @Natural @Double @[], x2473 @Natural @Double @[]] x2474 [x2475 @Natural @Double @[], x2476 @Natural @Double @[]] -> x2471) (\\x2477 x2478 [x2479 @Natural @Double @[], x2480 @Natural @Double @[]] -> (x2477, 0, 0)) (v2453 ! [2]) (rreverse (rslice 0 2 v2400), rreplicate 2 x2380)), rreverse (rslice 0 2 v2400), rreplicate 2 x2380))) (rreplicate 0 (rconst 0.0)) ! [0])]) (\\[i4322] -> [i4322, i4322]))) (\\x2846 x2847 [x2848 @Natural @Double @[], x2849 @Natural @Double @[]] -> let v2916 = rscanDer (\\x2907 x2908 -> x2907 * x2908) (\\x2909 x2910 x2911 x2912 -> x2909 * x2912 + x2910 * x2911) (\\x2913 x2914 x2915 -> (x2915 * x2913, x2914 * x2913)) x2849 (rreplicate 2 x2848) ; v2926 = rscanDer (\\x2917 x2918 -> x2917 + x2918) (\\x2919 x2920 x2921 x2922 -> x2919 + x2920) (\\x2923 x2924 x2925 -> (x2923, x2923)) x2848 (rreplicate 2 x2849) ; v2939 = rscanDer (\\x2927 x2928 -> (rconst 0.1 * x2927) * x2928) (\\x2929 x2930 x2931 x2932 -> (x2929 * rconst 0.1) * x2932 + x2930 * (rconst 0.1 * x2931)) (\\x2935 x2936 x2937 -> (rconst 0.1 * (x2937 * x2935), (rconst 0.1 * x2936) * x2935)) (v2916 ! [2]) v2926 ; v2958 = rscanZipDer (\\x2940 [x2941 @Natural @Double @[], x2942 @Natural @Double @[]] -> rconst 0.1 * (x2942 * x2940)) (\\x2944 [x2945 @Natural @Double @[], x2946 @Natural @Double @[]] x2947 [x2948 @Natural @Double @[], x2949 @Natural @Double @[]] -> (x2946 * x2947 + x2944 * x2949) * rconst 0.1) (\\x2952 x2953 [x2954 @Natural @Double @[], x2955 @Natural @Double @[]] -> let x2957 = rconst 0.1 * x2952 in (x2955 * x2957, 0, x2953 * x2957)) x2847 (rreverse (rslice 0 3 v2939), rreverse v2926) ; v2959 = rreverse v2958 ; v2974 = rscanZipDer (\\x2961 [x2962 @Natural @Double @[], x2963 @Natural @Double @[]] -> x2963 * x2961) (\\x2964 [x2965 @Natural @Double @[], x2966 @Natural @Double @[]] x2967 [x2968 @Natural @Double @[], x2969 @Natural @Double @[]] -> x2966 * x2967 + x2964 * x2969) (\\x2970 x2971 [x2972 @Natural @Double @[], x2973 @Natural @Double @[]] -> (x2973 * x2970, 0, x2971 * x2970)) (v2959 ! [0]) (rreverse (rslice 0 2 v2916), rreplicate 2 x2848) ; v2976 = rreplicate 3 (rconst 0.1) * rslice 0 3 v2939 ; v2978 = rgather [3] v2959 (\\[i2977] -> [1 + i2977]) ; v2979 = v2976 * v2978 ; v3007 = rscanZipDer (\\x2994 [x2995 @Natural @Double @[], x2996 @Natural @Double @[]] -> x2994) (\\x2997 [x2998 @Natural @Double @[], x2999 @Natural @Double @[]] x3000 [x3001 @Natural @Double @[], x3002 @Natural @Double @[]] -> x2997) (\\x3003 x3004 [x3005 @Natural @Double @[], x3006 @Natural @Double @[]] -> (x3003, 0, 0)) (v2979 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849) ; v3014 = rscatter [3] (rgather [2] v2974 (\\[i3011] -> [1 + negate i3011]) * rreplicate 2 x2846) (\\[i3013] -> [i3013]) ; m3015 = rfromList [rappend (rreverse (rscanZipDer (\\x3016 [x3017 @Natural @Double @[], x3018 @Natural @Double @[]] -> x3018 * x3016) (\\x3019 [x3020 @Natural @Double @[], x3021 @Natural @Double @[]] x3022 [x3023 @Natural @Double @[], x3024 @Natural @Double @[]] -> x3021 * x3022 + x3019 * x3024) (\\x3026 x3027 [x3028 @Natural @Double @[], x3029 @Natural @Double @[]] -> (x3029 * x3026, 0, x3027 * x3026)) (v3014 ! [1]) (rreverse (rslice 0 1 v2916), rreplicate 1 x2848))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x4414 [x4415 @Natural @Double @[], x4416 @Natural @Double @[]] -> x4416 * x4414) (\\x4417 [x4418 @Natural @Double @[], x4419 @Natural @Double @[]] x4420 [x4421 @Natural @Double @[], x4422 @Natural @Double @[]] -> x4419 * x4420 + x4417 * x4422) (\\x4424 x4425 [x4426 @Natural @Double @[], x4427 @Natural @Double @[]] -> (x4427 * x4424, 0, x4425 * x4424)) (v3014 ! [2]) (rreverse (rslice 0 2 v2916), rreplicate 2 x2848))) (rreplicate 0 (rconst 0.0))] ; m3030 = rtranspose [1,0] (rscatter [3,2] (rreplicate 2 x2846) (\\[] -> [0])) ; v3032 = rreverse (m3030 ! [1]) ; v3057 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)) + rappend (rreplicate 2 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)))) (rreplicate 1 (rconst 0.0))) ; m3058 = rfromList [rappend (rreverse (rscanZipDer (\\x3059 [x3060 @Natural @Double @[], x3061 @Natural @Double @[]] -> x3059) (\\x3062 [x3063 @Natural @Double @[], x3064 @Natural @Double @[]] x3065 [x3066 @Natural @Double @[], x3067 @Natural @Double @[]] -> x3062) (\\x3068 x3069 [x3070 @Natural @Double @[], x3071 @Natural @Double @[]] -> (x3068, 0, 0)) (v3057 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x4045 [x4046 @Natural @Double @[], x4047 @Natural @Double @[]] -> x4045) (\\x4048 [x4049 @Natural @Double @[], x4050 @Natural @Double @[]] x4051 [x4052 @Natural @Double @[], x4053 @Natural @Double @[]] -> x4048) (\\x4054 x4055 [x4056 @Natural @Double @[], x4057 @Natural @Double @[]] -> (x4054, 0, 0)) (v3057 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0))] ; v3073 = rreverse (rslice 0 2 (m3030 ! [0])) ; v3095 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)))) (rreplicate 2 (rconst 0.0))) ; m3096 = rfromList [rappend (rreverse (rscanZipDer (\\x3097 [x3098 @Natural @Double @[], x3099 @Natural @Double @[]] -> x3097) (\\x3100 [x3101 @Natural @Double @[], x3102 @Natural @Double @[]] x3103 [x3104 @Natural @Double @[], x3105 @Natural @Double @[]] -> x3100) (\\x3106 x3107 [x3108 @Natural @Double @[], x3109 @Natural @Double @[]] -> (x3106, 0, 0)) (v3095 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3819 [x3820 @Natural @Double @[], x3821 @Natural @Double @[]] -> x3819) (\\x3822 [x3823 @Natural @Double @[], x3824 @Natural @Double @[]] x3825 [x3826 @Natural @Double @[], x3827 @Natural @Double @[]] -> x3822) (\\x3828 x3829 [x3830 @Natural @Double @[], x3831 @Natural @Double @[]] -> (x3828, 0, 0)) (v3095 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0))] ; v3110 = rscatter [3] (v3073 ! [0] + rsum (rreplicate 1 (rappend (rreverse (rscanZipDer (\\x3075 [x3076 @Natural @Double @[], x3077 @Natural @Double @[], x3078 @Natural @Double @[]] -> x3075) (\\x3079 [x3080 @Natural @Double @[], x3081 @Natural @Double @[], x3082 @Natural @Double @[]] x3083 [x3084 @Natural @Double @[], x3085 @Natural @Double @[], x3086 @Natural @Double @[]] -> x3079) (\\x3087 x3088 [x3089 @Natural @Double @[], x3090 @Natural @Double @[], x3091 @Natural @Double @[]] -> (x3087, 0, 0, 0)) (v3073 ! [1]) (rreverse (rslice 0 1 (rscanZipDer (\\x2980 [x2981 @Natural @Double @[], x2982 @Natural @Double @[]] -> x2980) (\\x2983 [x2984 @Natural @Double @[], x2985 @Natural @Double @[]] x2986 [x2987 @Natural @Double @[], x2988 @Natural @Double @[]] -> x2983) (\\x2989 x2990 [x2991 @Natural @Double @[], x2992 @Natural @Double @[]] -> (x2989, 0, 0)) (v2979 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))), rslice 0 1 v2926, rreplicate 1 x2849))) (rreplicate 0 (rconst 0.0)) ! [0]))) (\\[] -> [1]) + rscatter [3] (v3032 ! [0] + rsum (rgather [2] (rfromList [rreplicate 2 (rappend (rreverse (rscanZipDer (\\x3034 [x3035 @Natural @Double @[], x3036 @Natural @Double @[], x3037 @Natural @Double @[]] -> x3034) (\\x3038 [x3039 @Natural @Double @[], x3040 @Natural @Double @[], x3041 @Natural @Double @[]] x3042 [x3043 @Natural @Double @[], x3044 @Natural @Double @[], x3045 @Natural @Double @[]] -> x3038) (\\x3046 x3047 [x3048 @Natural @Double @[], x3049 @Natural @Double @[], x3050 @Natural @Double @[]] -> (x3046, 0, 0, 0)) (v3032 ! [1]) (rreverse (rslice 0 1 v3007), rreverse (rslice 0 1 (rreverse (rslice 0 2 v2926))), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)) ! [0]), rreplicate 2 (rappend (rreverse (rscanZipDer (\\x4377 [x4378 @Natural @Double @[], x4379 @Natural @Double @[], x4380 @Natural @Double @[]] -> x4377) (\\x4381 [x4382 @Natural @Double @[], x4383 @Natural @Double @[], x4384 @Natural @Double @[]] x4385 [x4386 @Natural @Double @[], x4387 @Natural @Double @[], x4388 @Natural @Double @[]] -> x4381) (\\x4389 x4390 [x4391 @Natural @Double @[], x4392 @Natural @Double @[], x4393 @Natural @Double @[]] -> (x4389, 0, 0, 0)) (v3032 ! [2]) (rreverse (rslice 0 2 v3007), rslice 0 2 v2926, rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0)) ! [0])]) (\\[i4428] -> [i4428, i4428]))) (\\[] -> [2]) + rscatter [3] x2846 (\\[] -> [0]) ; v3112 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreplicate 3 (rconst 0.1) * (v2978 * v3110)) (rreplicate 1 (rconst 0.0))) ; m3113 = rfromList [rappend (rreverse (rscanZipDer (\\x3114 [x3115 @Natural @Double @[], x3116 @Natural @Double @[]] -> rconst 0.1 * (x3116 * x3114)) (\\x3118 [x3119 @Natural @Double @[], x3120 @Natural @Double @[]] x3121 [x3122 @Natural @Double @[], x3123 @Natural @Double @[]] -> (x3120 * x3121 + x3118 * x3123) * rconst 0.1) (\\x3127 x3128 [x3129 @Natural @Double @[], x3130 @Natural @Double @[]] -> let x3132 = rconst 0.1 * x3127 in (x3130 * x3132, 0, x3128 * x3132)) (v3112 ! [1]) (rreverse (rslice 0 1 v2939), rreverse (rslice 0 1 v2926)))) (rreplicate 2 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3861 [x3862 @Natural @Double @[], x3863 @Natural @Double @[]] -> rconst 0.1 * (x3863 * x3861)) (\\x3865 [x3866 @Natural @Double @[], x3867 @Natural @Double @[]] x3868 [x3869 @Natural @Double @[], x3870 @Natural @Double @[]] -> (x3867 * x3868 + x3865 * x3870) * rconst 0.1) (\\x3874 x3875 [x3876 @Natural @Double @[], x3877 @Natural @Double @[]] -> let x3879 = rconst 0.1 * x3874 in (x3877 * x3879, 0, x3875 * x3879)) (v3112 ! [2]) (rreverse (rslice 0 2 v2939), rreverse (rslice 0 2 v2926)))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3909 [x3910 @Natural @Double @[], x3911 @Natural @Double @[]] -> rconst 0.1 * (x3911 * x3909)) (\\x3913 [x3914 @Natural @Double @[], x3915 @Natural @Double @[]] x3916 [x3917 @Natural @Double @[], x3918 @Natural @Double @[]] -> (x3915 * x3916 + x3913 * x3918) * rconst 0.1) (\\x3922 x3923 [x3924 @Natural @Double @[], x3925 @Natural @Double @[]] -> let x3927 = rconst 0.1 * x3922 in (x3925 * x3927, 0, x3923 * x3927)) (v3112 ! [3]) (rreverse (rslice 0 3 v2939), rreverse v2926))) (rreplicate 0 (rconst 0.0))] ; v3133 = rsum (rfromList [rappend ((rreplicate 1 (rconst 0.1) * rslice 0 1 v2939) * rgather [1] (m3113 ! [0]) (\\[i3138] -> [1 + i3138])) (rreplicate 2 (rconst 0.0)), rappend ((rreplicate 2 (rconst 0.1) * rslice 0 2 v2939) * rgather [2] (m3113 ! [1]) (\\[i3938] -> [1 + i3938])) (rreplicate 1 (rconst 0.0)), rappend ((rreplicate 3 (rconst 0.1) * rslice 0 3 v2939) * rgather [3] (m3113 ! [2]) (\\[i3948] -> [1 + i3948])) (rreplicate 0 (rconst 0.0))]) ; m3139 = rfromList [rappend (rreverse (rscanZipDer (\\x3140 [x3141 @Natural @Double @[], x3142 @Natural @Double @[]] -> x3140) (\\x3143 [x3144 @Natural @Double @[], x3145 @Natural @Double @[]] x3146 [x3147 @Natural @Double @[], x3148 @Natural @Double @[]] -> x3143) (\\x3149 x3150 [x3151 @Natural @Double @[], x3152 @Natural @Double @[]] -> (x3149, 0, 0)) (v3133 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3968 [x3969 @Natural @Double @[], x3970 @Natural @Double @[]] -> x3968) (\\x3971 [x3972 @Natural @Double @[], x3973 @Natural @Double @[]] x3974 [x3975 @Natural @Double @[], x3976 @Natural @Double @[]] -> x3971) (\\x3977 x3978 [x3979 @Natural @Double @[], x3980 @Natural @Double @[]] -> (x3977, 0, 0)) (v3133 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0))] ; v3154 = rreverse (rscatter [3] (rgather [2] v2916 (\\[i3009] -> [i3009]) * rreplicate 2 x2846) (\\[i3153] -> [1 + i3153])) ; m3155 = rfromList [rappend (rreverse (rscanZipDer (\\x3156 [x3157 @Natural @Double @[], x3158 @Natural @Double @[], x3159 @Natural @Double @[]] -> x3159 * x3156) (\\x3160 [x3161 @Natural @Double @[], x3162 @Natural @Double @[], x3163 @Natural @Double @[]] x3164 [x3165 @Natural @Double @[], x3166 @Natural @Double @[], x3167 @Natural @Double @[]] -> x3163 * x3164 + x3160 * x3167) (\\x3169 x3170 [x3171 @Natural @Double @[], x3172 @Natural @Double @[], x3173 @Natural @Double @[]] -> (x3173 * x3169, 0, 0, x3170 * x3169)) (v3154 ! [1]) (rreverse (rslice 0 1 v2974), rreverse (rslice 0 1 (rreverse (rslice 0 2 v2916))), rreplicate 1 x2848))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x4008 [x4009 @Natural @Double @[], x4010 @Natural @Double @[], x4011 @Natural @Double @[]] -> x4011 * x4008) (\\x4012 [x4013 @Natural @Double @[], x4014 @Natural @Double @[], x4015 @Natural @Double @[]] x4016 [x4017 @Natural @Double @[], x4018 @Natural @Double @[], x4019 @Natural @Double @[]] -> x4015 * x4016 + x4012 * x4019) (\\x4021 x4022 [x4023 @Natural @Double @[], x4024 @Natural @Double @[], x4025 @Natural @Double @[]] -> (x4025 * x4021, 0, 0, x4022 * x4021)) (v3154 ! [2]) (rreverse (rslice 0 2 v2974), rslice 0 2 v2916, rreplicate 2 x2848))) (rreplicate 0 (rconst 0.0))] ; v3186 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)) + rappend (rreplicate 2 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)))) (rreplicate 1 (rconst 0.0))) ; m3187 = rfromList [rappend (rreverse (rscanZipDer (\\x3188 [x3189 @Natural @Double @[], x3190 @Natural @Double @[]] -> x3190 * x3188) (\\x3191 [x3192 @Natural @Double @[], x3193 @Natural @Double @[]] x3194 [x3195 @Natural @Double @[], x3196 @Natural @Double @[]] -> x3193 * x3194 + x3191 * x3196) (\\x3198 x3199 [x3200 @Natural @Double @[], x3201 @Natural @Double @[]] -> (x3201 * x3198, 0, x3199 * x3198)) (v3186 ! [1]) (rreverse (rslice 0 1 v2916), rreplicate 1 x2848))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3664 [x3665 @Natural @Double @[], x3666 @Natural @Double @[]] -> x3666 * x3664) (\\x3667 [x3668 @Natural @Double @[], x3669 @Natural @Double @[]] x3670 [x3671 @Natural @Double @[], x3672 @Natural @Double @[]] -> x3669 * x3670 + x3667 * x3672) (\\x3674 x3675 [x3676 @Natural @Double @[], x3677 @Natural @Double @[]] -> (x3677 * x3674, 0, x3675 * x3674)) (v3186 ! [2]) (rreverse (rslice 0 2 v2916), rreplicate 2 x2848))) (rreplicate 0 (rconst 0.0))] ; v3203 = rreverse (rscatter [4] (v3154 ! [0] + rsum (rgather [2] m3155 (\\[i4328] -> [i4328, 0]))) (\\[] -> [0]) + rscatter [4] (v2976 * v3110) (\\[i3202] -> [1 + i3202])) ; m3204 = rfromList [rappend (rreverse (rscanZipDer (\\x3205 [x3206 @Natural @Double @[], x3207 @Natural @Double @[], x3208 @Natural @Double @[]] -> x3208 * (rconst 0.1 * x3205)) (\\x3211 [x3212 @Natural @Double @[], x3213 @Natural @Double @[], x3214 @Natural @Double @[]] x3215 [x3216 @Natural @Double @[], x3217 @Natural @Double @[], x3218 @Natural @Double @[]] -> x3214 * (rconst 0.1 * x3215) + (x3211 * rconst 0.1) * x3218) (\\x3222 x3223 [x3224 @Natural @Double @[], x3225 @Natural @Double @[], x3226 @Natural @Double @[]] -> (rconst 0.1 * (x3226 * x3222), 0, 0, (rconst 0.1 * x3223) * x3222)) (v3203 ! [1]) (rreverse (rslice 0 1 v2958), rreverse (rslice 0 1 (rreverse (rslice 0 3 v2939))), rreverse (rslice 0 1 (rreverse v2926))))) (rreplicate 2 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3716 [x3717 @Natural @Double @[], x3718 @Natural @Double @[], x3719 @Natural @Double @[]] -> x3719 * (rconst 0.1 * x3716)) (\\x3722 [x3723 @Natural @Double @[], x3724 @Natural @Double @[], x3725 @Natural @Double @[]] x3726 [x3727 @Natural @Double @[], x3728 @Natural @Double @[], x3729 @Natural @Double @[]] -> x3725 * (rconst 0.1 * x3726) + (x3722 * rconst 0.1) * x3729) (\\x3733 x3734 [x3735 @Natural @Double @[], x3736 @Natural @Double @[], x3737 @Natural @Double @[]] -> (rconst 0.1 * (x3737 * x3733), 0, 0, (rconst 0.1 * x3734) * x3733)) (v3203 ! [2]) (rreverse (rslice 0 2 v2958), rreverse (rslice 0 2 (rreverse (rslice 0 3 v2939))), rreverse (rslice 0 2 (rreverse v2926))))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3777 [x3778 @Natural @Double @[], x3779 @Natural @Double @[], x3780 @Natural @Double @[]] -> x3780 * (rconst 0.1 * x3777)) (\\x3783 [x3784 @Natural @Double @[], x3785 @Natural @Double @[], x3786 @Natural @Double @[]] x3787 [x3788 @Natural @Double @[], x3789 @Natural @Double @[], x3790 @Natural @Double @[]] -> x3786 * (rconst 0.1 * x3787) + (x3783 * rconst 0.1) * x3790) (\\x3794 x3795 [x3796 @Natural @Double @[], x3797 @Natural @Double @[], x3798 @Natural @Double @[]] -> (rconst 0.1 * (x3798 * x3794), 0, 0, (rconst 0.1 * x3795) * x3794)) (v3203 ! [3]) (rreverse (rslice 0 3 v2958), rslice 0 3 v2939, v2926))) (rreplicate 0 (rconst 0.0))] ; v3255 = rreverse (rappend (rgather [3] v2958 (\\[i3235] -> [i3235]) * (rreplicate 3 (rconst 0.1) * rgather [3] (m3204 ! [2]) (\\[i3231] -> [1 + i3231]))) (rreplicate 0 (rconst 0.0)) + rappend (rgather [1] v2958 (\\[i3253] -> [i3253]) * (rreplicate 1 (rconst 0.1) * rgather [1] (m3204 ! [0]) (\\[i3249] -> [1 + i3249]))) (rreplicate 2 (rconst 0.0)) + rappend (rgather [2] v2958 (\\[i3244] -> [i3244]) * (rreplicate 2 (rconst 0.1) * rgather [2] (m3204 ! [1]) (\\[i3240] -> [1 + i3240]))) (rreplicate 1 (rconst 0.0))) ; m3256 = rfromList [rappend (rreverse (rscanZipDer (\\x3257 [x3258 @Natural @Double @[], x3259 @Natural @Double @[]] -> x3257) (\\x3260 [x3261 @Natural @Double @[], x3262 @Natural @Double @[]] x3263 [x3264 @Natural @Double @[], x3265 @Natural @Double @[]] -> x3260) (\\x3266 x3267 [x3268 @Natural @Double @[], x3269 @Natural @Double @[]] -> (x3266, 0, 0)) (v3255 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3346 [x3347 @Natural @Double @[], x3348 @Natural @Double @[]] -> x3346) (\\x3349 [x3350 @Natural @Double @[], x3351 @Natural @Double @[]] x3352 [x3353 @Natural @Double @[], x3354 @Natural @Double @[]] -> x3349) (\\x3355 x3356 [x3357 @Natural @Double @[], x3358 @Natural @Double @[]] -> (x3355, 0, 0)) (v3255 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0))] ; v3270 = rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 3 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)) + rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 2 (rconst 0.0)) + rappend (rreplicate 2 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)))) (rreplicate 1 (rconst 0.0))) ; m3271 = rfromList [rappend (rreverse (rscanZipDer (\\x3272 [x3273 @Natural @Double @[], x3274 @Natural @Double @[]] -> rconst 0.1 * (x3274 * x3272)) (\\x3276 [x3277 @Natural @Double @[], x3278 @Natural @Double @[]] x3279 [x3280 @Natural @Double @[], x3281 @Natural @Double @[]] -> (x3278 * x3279 + x3276 * x3281) * rconst 0.1) (\\x3285 x3286 [x3287 @Natural @Double @[], x3288 @Natural @Double @[]] -> let x3290 = rconst 0.1 * x3285 in (x3288 * x3290, 0, x3286 * x3290)) (v3270 ! [1]) (rreverse (rslice 0 1 v2939), rreverse (rslice 0 1 v2926)))) (rreplicate 2 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3388 [x3389 @Natural @Double @[], x3390 @Natural @Double @[]] -> rconst 0.1 * (x3390 * x3388)) (\\x3392 [x3393 @Natural @Double @[], x3394 @Natural @Double @[]] x3395 [x3396 @Natural @Double @[], x3397 @Natural @Double @[]] -> (x3394 * x3395 + x3392 * x3397) * rconst 0.1) (\\x3401 x3402 [x3403 @Natural @Double @[], x3404 @Natural @Double @[]] -> let x3406 = rconst 0.1 * x3401 in (x3404 * x3406, 0, x3402 * x3406)) (v3270 ! [2]) (rreverse (rslice 0 2 v2939), rreverse (rslice 0 2 v2926)))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3436 [x3437 @Natural @Double @[], x3438 @Natural @Double @[]] -> rconst 0.1 * (x3438 * x3436)) (\\x3440 [x3441 @Natural @Double @[], x3442 @Natural @Double @[]] x3443 [x3444 @Natural @Double @[], x3445 @Natural @Double @[]] -> (x3442 * x3443 + x3440 * x3445) * rconst 0.1) (\\x3449 x3450 [x3451 @Natural @Double @[], x3452 @Natural @Double @[]] -> let x3454 = rconst 0.1 * x3449 in (x3452 * x3454, 0, x3450 * x3454)) (v3270 ! [3]) (rreverse (rslice 0 3 v2939), rreverse v2926))) (rreplicate 0 (rconst 0.0))] ; v3291 = rsum (rfromList [rappend ((rreplicate 1 (rconst 0.1) * rslice 0 1 v2939) * rgather [1] (m3271 ! [0]) (\\[i3296] -> [1 + i3296])) (rreplicate 2 (rconst 0.0)), rappend ((rreplicate 2 (rconst 0.1) * rslice 0 2 v2939) * rgather [2] (m3271 ! [1]) (\\[i3465] -> [1 + i3465])) (rreplicate 1 (rconst 0.0)), rappend ((rreplicate 3 (rconst 0.1) * rslice 0 3 v2939) * rgather [3] (m3271 ! [2]) (\\[i3475] -> [1 + i3475])) (rreplicate 0 (rconst 0.0))]) ; m3297 = rfromList [rappend (rreverse (rscanZipDer (\\x3298 [x3299 @Natural @Double @[], x3300 @Natural @Double @[]] -> x3298) (\\x3301 [x3302 @Natural @Double @[], x3303 @Natural @Double @[]] x3304 [x3305 @Natural @Double @[], x3306 @Natural @Double @[]] -> x3301) (\\x3307 x3308 [x3309 @Natural @Double @[], x3310 @Natural @Double @[]] -> (x3307, 0, 0)) (v3291 ! [1]) (rreverse (rslice 0 1 v2926), rreplicate 1 x2849))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3495 [x3496 @Natural @Double @[], x3497 @Natural @Double @[]] -> x3495) (\\x3498 [x3499 @Natural @Double @[], x3500 @Natural @Double @[]] x3501 [x3502 @Natural @Double @[], x3503 @Natural @Double @[]] -> x3498) (\\x3504 x3505 [x3506 @Natural @Double @[], x3507 @Natural @Double @[]] -> (x3504, 0, 0)) (v3291 ! [2]) (rreverse (rslice 0 2 v2926), rreplicate 2 x2849))) (rreplicate 0 (rconst 0.0))] ; v3311 = rscatter [3] (v3270 ! [0] + rsum (rgather [3] m3271 (\\[i4330] -> [i4330, 0])) + v3112 ! [0] + rsum (rgather [3] m3113 (\\[i4332] -> [i4332, 0]))) (\\[] -> [2]) ; m3312 = rfromList [rappend (rreverse (rscanZipDer (\\x3313 [x3314 @Natural @Double @[], x3315 @Natural @Double @[]] -> x3315 * x3313) (\\x3316 [x3317 @Natural @Double @[], x3318 @Natural @Double @[]] x3319 [x3320 @Natural @Double @[], x3321 @Natural @Double @[]] -> x3318 * x3319 + x3316 * x3321) (\\x3323 x3324 [x3325 @Natural @Double @[], x3326 @Natural @Double @[]] -> (x3326 * x3323, 0, x3324 * x3323)) (v3311 ! [1]) (rreverse (rslice 0 1 v2916), rreplicate 1 x2848))) (rreplicate 1 (rconst 0.0)), rappend (rreverse (rscanZipDer (\\x3528 [x3529 @Natural @Double @[], x3530 @Natural @Double @[]] -> x3530 * x3528) (\\x3531 [x3532 @Natural @Double @[], x3533 @Natural @Double @[]] x3534 [x3535 @Natural @Double @[], x3536 @Natural @Double @[]] -> x3533 * x3534 + x3531 * x3536) (\\x3538 x3539 [x3540 @Natural @Double @[], x3541 @Natural @Double @[]] -> (x3541 * x3538, 0, x3539 * x3538)) (v3311 ! [2]) (rreverse (rslice 0 2 v2916), rreplicate 2 x2848))) (rreplicate 0 (rconst 0.0))] in (v3203 ! [0] + rsum (rgather [3] m3204 (\\[i4334] -> [i4334, 0])), rsum (rsum (rfromList [rappend (rgather [1] v2916 (\\[i3547] -> [i3547]) * rgather [1] (m3312 ! [0]) (\\[i3548] -> [1 + i3548])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] v2916 (\\[i3554] -> [i3554]) * rgather [2] (m3312 ! [1]) (\\[i3555] -> [1 + i3555])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] v2916 (\\[i3561] -> [i3561]) * rgather [1] (m3187 ! [0]) (\\[i3562] -> [1 + i3562])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] v2916 (\\[i3568] -> [i3568]) * rgather [2] (m3187 ! [1]) (\\[i3569] -> [1 + i3569])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] v2916 (\\[i3575] -> [i3575]) * rgather [1] (m3015 ! [0]) (\\[i3576] -> [1 + i3576])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] v2916 (\\[i3582] -> [i3582]) * rgather [2] (m3015 ! [1]) (\\[i3583] -> [1 + i3583])) (rreplicate 0 (rconst 0.0))])) + v3291 ! [0] + rsum (rgather [2] m3297 (\\[i4336] -> [i4336, 0])) + v3255 ! [0] + rsum (rgather [2] m3256 (\\[i4338] -> [i4338, 0])) + rsum (rappend (rgather [1] v2974 (\\[i3183] -> [i3183]) * rgather [1] (m3155 ! [0]) (\\[i3184] -> [1 + i3184])) (rreplicate 1 (rconst 0.0)) + rappend (rgather [2] v2974 (\\[i3177] -> [i3177]) * rgather [2] (m3155 ! [1]) (\\[i3178] -> [1 + i3178])) (rreplicate 0 (rconst 0.0))) + v3133 ! [0] + rsum (rgather [2] m3139 (\\[i4340] -> [i4340, 0])) + v3095 ! [0] + rsum (rgather [2] m3096 (\\[i4342] -> [i4342, 0])) + v3057 ! [0] + rsum (rgather [2] m3058 (\\[i4344] -> [i4344, 0])), rsum (rsum (rfromList [rappend (rgather [1] (m3297 ! [0]) (\\[i3589] -> [1 + i3589])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] (m3297 ! [1]) (\\[i3595] -> [1 + i3595])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] (m3256 ! [0]) (\\[i3601] -> [1 + i3601])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] (m3256 ! [1]) (\\[i3607] -> [1 + i3607])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] (m3139 ! [0]) (\\[i3613] -> [1 + i3613])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] (m3139 ! [1]) (\\[i3619] -> [1 + i3619])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] (m3096 ! [0]) (\\[i3625] -> [1 + i3625])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] (m3096 ! [1]) (\\[i3631] -> [1 + i3631])) (rreplicate 0 (rconst 0.0))]) + rsum (rfromList [rappend (rgather [1] (m3058 ! [0]) (\\[i3637] -> [1 + i3637])) (rreplicate 1 (rconst 0.0)), rappend (rgather [2] (m3058 ! [1]) (\\[i3643] -> [1 + i3643])) (rreplicate 0 (rconst 0.0))])) + v3311 ! [0] + rsum (rgather [2] m3312 (\\[i4346] -> [i4346, 0])) + v3186 ! [0] + rsum (rgather [2] m3187 (\\[i4348] -> [i4348, 0])) + rsum (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)))) (rreplicate 1 (rconst 0.0)))) + rsum (rappend (rreplicate 0 (rconst 0.0)) (rappend (rreverse (rappend (rreplicate 1 (sconst @[] 0.0)) (rreplicate 1 (rconst 0.0)) + rappend (rreplicate 2 (sconst @[] 0.0)) (rreplicate 0 (rconst 0.0)))) (rreplicate 0 (rconst 0.0)))) + v3014 ! [0] + rsum (rgather [2] m3015 (\\[i4350] -> [i4350, 0])))) (rconst 1.0) (rreverse (rslice 0 2 v2281), rconstant (rreplicate 2 (rconst 1.1)))) in (let m4071 = rgather [2,3] (rscanDer (\\v4059 v4060 -> v4059 * v4060) (\\v4062 v4063 v4064 v4065 -> v4062 * v4065 + v4063 * v4064) (\\v4067 v4068 v4069 -> (v4069 * v4067, v4068 * v4067)) (rconstant (rreplicate 2 (rconst 1.1))) (rreplicate 2 (rslice 0 2 v2281))) (\\[i4190, i4191] -> [i4191, i4190]) ; m4085 = rgather [2,3] (rscanDer (\\v4072 v4073 -> v4072 + v4073) (\\v4076 v4077 v4078 v4079 -> v4076 + v4077) (\\v4081 v4082 v4083 -> (v4081, v4081)) (rgather [2] v2281 (\\[i4075] -> [i4075])) (rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 1.1)))))) (\\[i4192, i4193] -> [i4193, i4192]) ; m4105 = rgather [2,4] (rscanDer (\\v4086 v4087 -> (rreplicate 2 (rconst 0.1) * v4086) * v4087) (\\v4090 v4091 v4092 v4093 -> (v4090 * rreplicate 2 (rconst 0.1)) * v4093 + v4091 * (rreplicate 2 (rconst 0.1) * v4092)) (\\v4099 v4100 v4101 -> (rreplicate 2 (rconst 0.1) * (v4101 * v4099), (rreplicate 2 (rconst 0.1) * v4100) * v4099)) (rgather [2] m4071 (\\[i4089] -> [i4089, 2])) (rtranspose [1,0] m4085)) (\\[i4194, i4195] -> [i4195, i4194]) ; m4133 = rgather [2,4] (rscanZipDer (\\v4106 [v4107 @Natural @Double @[2], v4108 @Natural @Double @[2]] -> rreplicate 2 (rconst 0.1) * (v4108 * v4106)) (\\v4113 [v4114 @Natural @Double @[2], v4115 @Natural @Double @[2]] v4116 [v4117 @Natural @Double @[2], v4118 @Natural @Double @[2]] -> (v4115 * v4116 + v4113 * v4118) * rreplicate 2 (rconst 0.1)) (\\v4124 v4125 [v4126 @Natural @Double @[2], v4127 @Natural @Double @[2]] -> let v4132 = rreplicate 2 (rconst 0.1) * v4124 in (v4127 * v4132, sconst @[2] (fromList @[2] [0.0,0.0]), v4125 * v4132)) (rgather [2] v4058 (\\[i4111] -> [1 + i4111])) (rreverse (rslice 0 3 (rtranspose [1,0] m4105)), rreverse (rtranspose [1,0] m4085))) (\\[i4196, i4197] -> [3 + negate i4197, i4196]) ; m4160 = (rconstant (rreplicate 2 (rreplicate 3 (rconst 0.1))) * rgather [2,3] m4105 (\\[i4200, i4201] -> [i4200, i4201])) * rgather [2,3] m4133 (\\[i4158, i4159] -> [i4158, 1 + i4159]) ; t4161 = rgather [2,2,3] (rfromList [rgather [2,2,3] (rappend (rreverse (rscanZipDer (\\v4162 [v4163 @Natural @Double @[2], v4164 @Natural @Double @[2]] -> v4162) (\\v4167 [v4168 @Natural @Double @[2], v4169 @Natural @Double @[2]] v4170 [v4171 @Natural @Double @[2], v4172 @Natural @Double @[2]] -> v4167) (\\v4174 v4175 [v4176 @Natural @Double @[2], v4177 @Natural @Double @[2]] -> (v4174, sconst @[2] (fromList @[2] [0.0,0.0]), sconst @[2] (fromList @[2] [0.0,0.0]))) (rgather [2] m4160 (\\[i4166] -> [i4166, 1])) (rreverse (rslice 0 1 (rtranspose [1,0] m4085)), rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 1.1))))))) (rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 0.0)))))) (\\[i4204, i4205, i4203] -> [i4203, i4204]), rgather [2,2,3] (rappend (rreverse (rscanZipDer (\\v4206 [v4207 @Natural @Double @[2], v4208 @Natural @Double @[2]] -> v4206) (\\v4211 [v4212 @Natural @Double @[2], v4213 @Natural @Double @[2]] v4214 [v4215 @Natural @Double @[2], v4216 @Natural @Double @[2]] -> v4211) (\\v4218 v4219 [v4220 @Natural @Double @[2], v4221 @Natural @Double @[2]] -> (v4218, sconst @[2] (fromList @[2] [0.0,0.0]), sconst @[2] (fromList @[2] [0.0,0.0]))) (rgather [2] m4160 (\\[i4210] -> [i4210, 2])) (rreverse (rslice 0 2 (rtranspose [1,0] m4085)), rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 2 (rconst 1.1))))))) (rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 0 (rconst 0.0)))))) (\\[i4204, i4205, i4224] -> [i4224, i4204])]) (\\[i4225, i4226] -> [i4226, i4225, i4226]) in rsum (rsum (rgather [4,2] (rfromList [rgather [4,2] (rappend (rgather [1,2] t4161 (\\[i4231, i4232] -> [i4232, 0, 1 + i4231])) (rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 1 (rconst 0.0)))))) (\\[i4254, i4253] -> [rem (4 * i4253 + i4254) 2, rem (quot (4 * i4253 + i4254) 4) 2]), rgather [4,2] (rappend (rgather [2,2] t4161 (\\[i4243, i4244] -> [i4244, 1, 1 + i4243])) (rconstant (rtranspose [1,0] (rreplicate 2 (rreplicate 0 (rconst 0.0)))))) (\\[i4254, i4253] -> [rem (4 * i4253 + i4254) 2, rem (quot (4 * i4253 + i4254) 4) 2])]) (\\[i4255, i4256] -> [rem (quot (4 * i4256 + i4255) 2) 2, i4255, i4256])) + rscanZipDer (\\v4137 [v4138 @Natural @Double @[2], v4139 @Natural @Double @[2]] -> v4139 * v4137) (\\v4141 [v4142 @Natural @Double @[2], v4143 @Natural @Double @[2]] v4144 [v4145 @Natural @Double @[2], v4146 @Natural @Double @[2]] -> v4143 * v4144 + v4141 * v4146) (\\v4148 v4149 [v4150 @Natural @Double @[2], v4151 @Natural @Double @[2]] -> (v4151 * v4148, sconst @[2] (fromList @[2] [0.0,0.0]), v4149 * v4148)) (rgather [2] m4133 (\\[i4134] -> [i4134, 0])) (rreverse (rslice 0 2 (rtranspose [1,0] m4071)), rreplicate 2 (rgather [2] v2281 (\\[i4136] -> [i4136]))) ! [2])) + v4058 ! [0]"
