{-# LANGUAGE ConstraintKinds, DataKinds, DeriveFunctor, DerivingStrategies,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, RankNTypes, StandaloneDeriving,
             TypeFamilyDependencies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists.
module HordeAd.Internal.SizedList
  ( SizedList(..)
  , singletonSized, snocSized, appendSized
  , headSized, tailSized, takeSized, dropSized
  , permutePrefixSized, permutePrefixList
  , unsnocSized1, lastSized, initSized
  , sizedListCompare, listToSized, sizedListToList
  , Permutation
  ) where

import Prelude

import Data.Array.Internal (valueOf)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (IsList (..))
import GHC.TypeLits
  (KnownNat, Nat, OrderingI (..), cmpNat, sameNat, type (+), type (-))

-- | Standard sized lists indexed by the GHC @Nat@ type.
--
-- Note that in GHC 9.4, @[a]@ and @SizedList@ no longer have
-- the same representation in some corner cases, so we can't
-- @unsafeCoerce@ between the two.
infixr 3 :::
data SizedList (n :: Nat) i where
  Z :: SizedList 0 i
  (:::) :: i -> SizedList n i -> SizedList (1 + n) i

deriving instance Eq i => Eq (SizedList n i)

deriving instance Ord i => Ord (SizedList n i)

-- This is pretty controversion and only lawful when OverloadedLists
-- is enabled. However, it's much more readable when tracing and debugging.
instance Show i => Show (SizedList n i) where
  showsPrec d l = showsPrec d (sizedListToList l)

deriving stock instance Functor (SizedList n)

instance Foldable (SizedList n) where
  foldr f z l = foldr f z (sizedListToList l)

instance KnownNat n => IsList (SizedList n i) where
  type Item (SizedList n i) = i
  fromList = listToSized
  toList = sizedListToList

singletonSized :: i -> SizedList 1 i
singletonSized i = i ::: Z

snocSized :: SizedList n i -> i -> SizedList (1 + n) i
snocSized Z last1 = last1 ::: Z
snocSized (i ::: ix) last1 = i ::: snocSized ix last1

appendSized :: SizedList m i -> SizedList n i -> SizedList (m + n) i
appendSized Z ix2 = ix2
appendSized (i1 ::: ix1) ix2 = i1 ::: appendSized ix1 ix2

headSized :: SizedList (1 + n) i -> i
headSized Z = error "headSized: impossible pattern needlessly required"
headSized (i ::: _ix) = i

tailSized :: SizedList (1 + n) i -> SizedList n i
tailSized Z = error "tailSized: impossible pattern needlessly required"
tailSized (_i ::: ix) = ix

takeSized :: forall len n i. KnownNat len
          => SizedList (len + n) i -> SizedList len i
takeSized ix = listToSized $ take (valueOf @len) $ sizedListToList ix

dropSized :: forall len n i. (KnownNat len, KnownNat n)
          => SizedList (len + n) i -> SizedList n i
dropSized ix = listToSized $ drop (valueOf @len) $ sizedListToList ix

unsnocSized1 :: SizedList (1 + n) i -> (SizedList n i, i)
unsnocSized1 Z = error "unsnocSized1: impossible pattern needlessly required"
unsnocSized1 (i ::: ix) = case ix of
  Z -> (Z, i)
  _ ::: _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::: init1, last1)

lastSized :: SizedList (1 + n) i -> i
lastSized Z = error "lastSized: impossible pattern needlessly required"
lastSized (i ::: Z) = i
lastSized (_i ::: ix@(_ ::: _)) = lastSized ix

initSized :: SizedList (1 + n) i -> SizedList n i
initSized Z = error "initSized: impossible pattern needlessly required"
initSized (_i ::: Z) = Z
initSized (i ::: ix@(_ ::: _)) = i ::: initSized ix

-- As in orthotope, a permutation lists indices into the list to permute.
type Permutation = [Int]

-- This permutes a prefix of the sized list of the length of the permutation.
-- The rest of the sized list is left intact.
-- Boxed vector is not that bad, because we move pointers around,
-- but don't follow them. Storable vectors wouldn't work for Ast.
permutePrefixSized :: forall n i. KnownNat n
                   => Permutation -> SizedList n i -> SizedList n i
permutePrefixSized p ix =
  if valueOf @n < length p
  then
    error "permutePrefixSized: cannot permute a list shorter than permutation"
  else (listToSized :: [i] -> SizedList n i)
       $ permutePrefixList p
       $ sizedListToList ix

permutePrefixList :: Permutation -> [i] -> [i]
permutePrefixList p l = map (l !!) p ++ drop (length p) l

-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedListCompare :: Monoid m
                 => (i -> i -> m) -> SizedList n i -> SizedList n i -> m
sizedListCompare _ Z Z = mempty
sizedListCompare f (i ::: idx) (j ::: idx') =
  f i j <> sizedListCompare f idx idx'
sizedListCompare _ _ _ =
  error "sizedListCompare: impossible pattern needlessly required"

-- Look Ma, no unsafeCoerce! This compiles only with GHC >= 9.2,
-- but the rest of our code caught up and fails with GHC 9.0 as well.
listToSized :: forall n i. KnownNat n => [i] -> SizedList n i
listToSized []
  | Just Refl <- sameNat (Proxy @n) (Proxy @0) = Z
  | otherwise = error $ "listToSized: list too short; missing "
                        ++ show (valueOf @n :: Int)
listToSized (i : is)
  -- What we really need here to make the types check out is a <= check.
  | EQI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToSized @(n - 1) is
      in i ::: sh
  | LTI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToSized @(n - 1) is
      in i ::: sh
  | otherwise =
      error $ "listToSized: list too long: "
              ++ show (length (i : is), valueOf @n :: Int)

sizedListToList :: SizedList n i -> [i]
sizedListToList Z = []
sizedListToList (i ::: is) = i : sizedListToList is
