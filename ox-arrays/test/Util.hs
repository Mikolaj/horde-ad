{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Util where

import Data.Array.RankedS qualified as OR
import Data.Kind
import GHC.TypeLits
import Hedgehog
import Hedgehog.Internal.Property (failDiff)

import Data.Array.Nested.Types (fromSNat')


-- Returns highest value that satisfies the predicate, or `lo` if none does
binarySearch :: (Num a, Eq a) => (a -> a) -> a -> a -> (a -> Bool) -> a
binarySearch div2 = \lo hi f -> case (f lo, f hi) of
  (False, _) -> lo
  (_, True) -> hi
  (_, _ ) -> go lo hi f
  where
    go lo hi f =  -- invariant: f lo && not (f hi)
      let mid = lo + div2 (hi - lo)
      in if mid `elem` [lo, hi]
           then mid
           else if f mid then go mid hi f else go lo mid f

orSumOuter1 :: (OR.Unbox a, Num a) => SNat n -> OR.Array (n + 1) a -> OR.Array n a
orSumOuter1 (sn@SNat :: SNat n) =
  let n = fromSNat' sn
  in OR.rerank @n @1 @0 (OR.scalar . OR.sumA) . OR.transpose ([1 .. n] ++ [0])

class AlmostEq f where
  type AlmostEqConstr f :: Type -> Constraint
  -- | absolute tolerance, lhs, rhs
  almostEq :: (AlmostEqConstr f a, Ord a, Show a, Fractional a, MonadTest m)
           => a -> f a -> f a -> m ()

instance AlmostEq (OR.Array n) where
  type AlmostEqConstr (OR.Array n) = OR.Unbox
  almostEq atol lhs rhs
    | OR.allA (< atol) (OR.zipWithA (\a b -> abs (a - b)) rhs lhs) =
        success
    | otherwise =
        failDiff lhs rhs
