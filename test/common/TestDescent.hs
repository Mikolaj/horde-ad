{-# LANGUAGE DataKinds, RankNTypes, TypeFamilies #-}
module TestDescent (testTrees) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.ShapedS as OS
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (toShapedOrDummy)
import Tool.EqEpsilon
import Tool.Shared (quad)

testTrees :: [TestTree]
testTrees = [gdTestsRecord]

data ARecord a b = ARecord a b

type ARecordAA sh r = ARecord (OS.Array sh r)
                              (OS.Array sh r)

type ARecordDD sh d r = ARecord (ADVal d (OS.Array sh r))
                                (ADVal d (OS.Array sh r))

adaptFunctionRecord
  :: forall sh r d. (ADModeAndNum d r, OS.Shape sh)
  => (ARecordDD sh d r -> ADVal d r)
  -> (ADInputs d r -> ADVal d r)
adaptFunctionRecord f inputs =
  let a = atS inputs 0
      b = atS inputs 1
  in f $ ARecord a b

adaptDReverseRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> ARecordAA sh r
  -> IO (ARecordAA sh r, r)
adaptDReverseRecord dt f (ARecord a b) = do
  let initVec = V.fromList $ map Data.Array.Convert.convert [a, b]
      g = adaptFunctionRecord f
      ((_, _, _, gradient), v) =
        revOnDomains dt g (V.empty, V.empty, V.empty, initVec)
      gradientRecord = case V.toList gradient of
        [a2, b2] -> ARecord (toShapedOrDummy a2)
                            (toShapedOrDummy b2)
        _ -> error "adaptDReverseRecord"
  return (gradientRecord, v)

adaptGdSimpleRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> Int
  -> ARecordAA sh r
  -> IO (ARecordAA sh r)
adaptGdSimpleRecord gamma f n0 (ARecord a b) = do
  let initVec = V.fromList $ map Data.Array.Convert.convert [a, b]
      g = adaptFunctionRecord f
  (_, _, _, gradient) <-
    gdSimple gamma g n0 (V.empty, V.empty, V.empty, initVec)
  case V.toList gradient of
    [a2, b2] -> return $! ARecord (toShapedOrDummy a2)
                                  (toShapedOrDummy b2)
    _ -> error "adaptGdSimpleRecord"

gdShowRecord
  :: forall sh r. (HasDelta r, OS.Shape sh)
  => r
  -> (forall d. ADModeAndNum d r
      => ARecordDD sh d r -> ADVal d r)
  -> [[r]]
  -> Int
  -> IO ([r], r)
gdShowRecord gamma f initList n = do
  let initRecord = case initList of
        [a, b] -> ARecord (OS.fromList a)
                          (OS.fromList b)
        _ -> error "gdShowRecord"
  gradient <- adaptGdSimpleRecord gamma f n initRecord
  (_, v) <- adaptDReverseRecord 1 f gradient
  let ppARecord :: ARecordAA sh r -> [r]
      ppARecord (ARecord a b) = OS.toList a ++ OS.toList b
  return (ppARecord gradient, v)

fquadRecord :: forall k d r. (ADModeAndNum d r, KnownNat k)
            => ARecordDD '[k] d r -> ADVal d r
fquadRecord (ARecord x y) = quad (fromS0 (head (unravelToListS x)))
                                 (fromS0 (head (unravelToListS y)))

gdTestsRecord :: TestTree
gdTestsRecord = testGroup "Record of shaped tensors tests"
  [ testCase "0.1 30" $ do
      res <- gdShowRecord 0.1 (fquadRecord @1) [[2], [3]] 30
      res @?~ ([2.47588e-3,3.7138206e-3],5.00002 :: Float)
  , testCase "0.01 30" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 30
      res @?~ ([1.0909687,1.6364527],8.86819 :: Float)
  , testCase "0.01 300" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 300
      res @?~ ([4.665013e-3,6.9975173e-3],5.0000706 :: Float)
  , testCase "0.01 300000" $ do
      res <- gdShowRecord 0.01 (fquadRecord @1) [[2], [3]] 300000
      res @?~ ([3.5e-44,3.5e-44],5.0 :: Float)
  , testCase "0.1 30" $ do
      res <- gdShowRecord 0.1 (fquadRecord @2) [[2, 42], [3, 42]] 30
      res @?~ ([2.47588e-3,42,3.7138206e-3,42],5.00002 :: Float)
  , testCase "0.01 30" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 30
      res @?~ ([1.0909687,42,1.6364527,42],8.86819 :: Float)
  , testCase "0.01 300" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 300
      res @?~ ([4.665013e-3,42,6.9975173e-3,42],5.0000706 :: Float)
  , testCase "0.01 300000" $ do
      res <- gdShowRecord 0.01 (fquadRecord @2) [[2, 42], [3, 42]] 300000
      res @?~ ([3.5e-44,42,3.5e-44,42],5.0 :: Float)
  ]
