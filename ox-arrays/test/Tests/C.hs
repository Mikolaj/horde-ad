{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
{-# LANGUAGE TypeAbstractions #-}
#endif
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Tests.C where

import Control.Monad
import Data.Array.RankedS qualified as OR
import Data.Functor.Const
import Data.Type.Equality
import Foreign
import GHC.TypeLits

import Data.Array.Nested
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Types (fromSNat')

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property (LabelName(..), forAllT)
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

-- import Debug.Trace

import Gen
import Util


-- | Appropriate for simple different summation orders
fineTol :: Double
fineTol = 1e-8

debugCoverage :: Bool
debugCoverage = False

prop_sum_nonempty :: Property
prop_sum_nonempty = property $ genRank $ \outrank@(SNat @n) -> do
  -- Test nonempty _results_. The first dimension of the input is allowed to be 0, because then OR.rerank doesn't fail yet.
  let inrank = SNat @(n + 1)
  sh <- forAll $ genShR inrank
  -- traceM ("sh: " ++ show sh ++ " -> " ++ show (shrSize sh))
  guard (all (> 0) (shrToList $ shrTail sh))  -- only constrain the tail
  arr <- forAllT $ OR.fromVector @Double @(n + 1) (shrToList sh) <$>
           genStorables (Range.singleton (shrSize sh))
                        (\w -> fromIntegral w / fromIntegral (maxBound :: Word64))
  let rarr = rfromOrthotope inrank arr
  almostEq fineTol (rtoOrthotope (rsumOuter1Prim rarr)) (orSumOuter1 outrank arr)

prop_sum_empty :: Property
prop_sum_empty = property $ genRank $ \outrankm1@(SNat @nm1) -> do
  -- We only need to test shapes where the _result_ is empty; the rest is handled by 'random nonempty' above.
  _outrank :: SNat n <- return $ SNat @(nm1 + 1)
  let inrank = SNat @(n + 1)
  sh <- forAll $ do
    shtt <- genShR outrankm1  -- nm1
    sht <- shuffleShR (0 :$: shtt)  -- n
    n <- Gen.int (Range.linear 0 20)
    return (n :$: sht)  -- n + 1
  guard (0 `elem` (shrToList $ shrTail sh))
  -- traceM ("sh: " ++ show sh ++ " -> " ++ show (shrSize sh))
  let arr = OR.fromList @(n + 1) @Double (shrToList sh) []
  let rarr = rfromOrthotope inrank arr
  OR.toList (rtoOrthotope (rsumOuter1Prim rarr)) === []

prop_sum_lasteq1 :: Property
prop_sum_lasteq1 = property $ genRank $ \outrank@(SNat @n) -> do
  let inrank = SNat @(n + 1)
  outsh <- forAll $ genShR outrank
  guard (all (> 0) $ shrToList outsh)
  let insh = shrAppend outsh (1 :$: ZSR)
  arr <- forAllT $ OR.fromVector @Double @(n + 1) (shrToList insh) <$>
           genStorables (Range.singleton (shrSize insh))
                        (\w -> fromIntegral w / fromIntegral (maxBound :: Word64))
  let rarr = rfromOrthotope inrank arr
  almostEq fineTol (rtoOrthotope (rsumOuter1Prim rarr)) (orSumOuter1 outrank arr)

prop_sum_replicated :: Bool -> Property
prop_sum_replicated doTranspose = property $
  genRank $ \inrank1@(SNat @m) ->
  genRank $ \outrank@(SNat @nm1) -> do
    inrank2 :: SNat n <- return $ SNat @(nm1 + 1)
    (Refl :: (m <=? n) :~: True) <- case cmpNat inrank1 inrank2 of
      LTI -> return Refl  -- actually we only continue if m < n
      _ -> discard
    (sh1, sh2, sh3) <- forAll $ genReplicatedShR inrank1 inrank2
    when debugCoverage $ do
      label (LabelName ("rankdiff " ++ show (fromSNat' inrank2 - fromSNat' inrank1)))
      label (LabelName ("size sh1 10^" ++ show (floor (logBase 10 (fromIntegral (shrSize sh1) :: Double)) :: Int)))
      label (LabelName ("size sh3 10^" ++ show (floor (logBase 10 (fromIntegral (shrSize sh3) :: Double)) :: Int)))
    guard (all (> 0) $ shrToList sh3)
    arr <- forAllT $
      OR.stretch (shrToList sh3)
      . OR.reshape (shrToList sh2)
      . OR.fromVector @Double @m (shrToList sh1) <$>
               genStorables (Range.singleton (shrSize sh1))
                            (\w -> fromIntegral w / fromIntegral (maxBound :: Word64))
    arrTrans <-
      if doTranspose then do perm <- forAll $ genPermR (fromSNat' inrank2)
                             return $ OR.transpose perm arr
                     else return arr
    let rarr = rfromOrthotope inrank2 arrTrans
    almostEq 1e-8 (rtoOrthotope (rsumOuter1Prim rarr)) (orSumOuter1 outrank arrTrans)

prop_negate_with :: forall f b. Show b
                 => ((forall n. f n -> SNat n -> PropertyT IO ()) -> PropertyT IO ())
                 -> (forall n. f n -> IShR n -> Gen b)
                 -> (forall n. f n -> b -> OR.Array n Double -> OR.Array n Double)
                 -> Property
prop_negate_with genRank' genB preproc = property $
  genRank' $ \extra rank@(SNat @n) -> do
    sh <- forAll $ genShR rank
    guard (all (> 0) $ shrToList sh)
    arr <- forAllT $ OR.fromVector @Double @n (shrToList sh) <$>
             genStorables (Range.singleton (shrSize sh))
                          (\w -> fromIntegral w / fromIntegral (maxBound :: Word64))
    bval <- forAll $ genB extra sh
    let arr' = preproc extra bval arr
    annotate (show (OR.shapeL arr'))
    let rarr = rfromOrthotope rank arr'
    rtoOrthotope (negate rarr) === OR.mapA negate arr'

tests :: TestTree
tests = testGroup "C"
  [testGroup "sum"
    [testProperty "nonempty" prop_sum_nonempty
    ,testProperty "empty" prop_sum_empty
    ,testProperty "last==1" prop_sum_lasteq1
    ,testProperty "replicated" (prop_sum_replicated False)
    ,testProperty "replicated_transposed" (prop_sum_replicated True)
    ]
  ,testGroup "negate"
    [testProperty "normalised" $ prop_negate_with
        (\k -> genRank (k (Const ())))
        (\_ _ -> pure ())
        (\_ _ -> id)
    ,testProperty "slice 1D" $ prop_negate_with @((:~:) 1)
        (\k -> k Refl (SNat @1))
        (\Refl (n :$: _) -> do lo <- Gen.integral (Range.constant 0 (n-1))
                               len <- Gen.integral (Range.constant 0 (n-lo))
                               return [(lo, len)])
        (\_ -> OR.slice)
    ,testProperty "slice nD" $ prop_negate_with
        (\k -> genRank (k (Const ())))
        (\_ sh -> do let genPair n = do lo <- Gen.integral (Range.constant 0 (n-1))
                                        len <- Gen.integral (Range.constant 0 (n-lo-1))
                                        return (lo, len)
                     pairs <- mapM genPair (shrToList sh)
                     return pairs)
        (\_ -> OR.slice)
    ]
  ]
