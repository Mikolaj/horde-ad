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
  , headSized, tailSized, takeSized, dropSized, permutePrefixSized
  , unsnocSized, lastSized, initSized
  , sizedListCompare , listToSized, sizedListToList
  , Permutation
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.Exts (IsList (..))
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

-- | Standard sized lists indexed by the GHC @Nat@ type.
--
-- Strongly Worded Warning: the implementation of this datatype should never
-- be changed, even by adding a constraint or making a field strict or packed.
-- Otherwise the multiple @unsafeCoerce@ below won't work any more,
-- because they depend on the runtime representation of the datatype
-- being identical to the representation of ordinary lists.
-- Note that changes in GHC or base library may similarly break this code,
-- though there should be ample advance warning, given that many
-- programs depend on this coincidence.
infixr 3 :::
data SizedList (n :: Nat) i where
  Z :: SizedList 0 i
  (:::) :: i -> SizedList n i -> SizedList (1 + n) i

deriving instance Eq i => Eq (SizedList n i)

deriving instance Ord i => Ord (SizedList n i)

instance Show i => Show (SizedList n i) where
  showsPrec _ Z = showString "Z"
  showsPrec d (i ::: ix) = showParen (d > 3) $
    showsPrec 4 i . showString " ::: " . showsPrec 3 ix

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
takeSized ix = unsafeCoerce $ take (valueOf @len) $ unsafeCoerce ix

dropSized :: forall len n i. KnownNat len
          => SizedList (len + n) i -> SizedList n i
dropSized ix = unsafeCoerce $ drop (valueOf @len) $ unsafeCoerce ix

unsnocSized :: SizedList (1 + n) i -> (SizedList n i, i)
unsnocSized Z = error "unsnocSized: impossible pattern needlessly required"
unsnocSized (i ::: ix) = case ix of
  Z -> (Z, i)
  _ ::: _ -> let (init1, last1) = unsnocSized ix
             in (i ::: init1, last1)

lastSized :: SizedList (1 + n) i -> i
lastSized Z = error "lastSized: impossible pattern needlessly required"
lastSized (i ::: Z) = i
lastSized (_i ::: ix@(_ ::: _)) = lastSized ix

initSized :: SizedList (1 + n) i -> SizedList n i
initSized Z = error "initSized: impossible pattern needlessly required"
initSized (_i ::: Z) = Z
initSized (i ::: ix@(_ ::: _)) = i ::: initSized ix

type Permutation = [Int]

-- This permutes a prefix of the sized list of the length of the permutation.
-- The rest of the sized list is left intact.
-- Boxed vector is not that bad, because we move pointers around,
-- but don't follow them. Storable vectors wouldn't work for Ast.
permutePrefixSized :: forall n i. KnownNat n
                   => Permutation -> SizedList n i -> SizedList n i
permutePrefixSized p ix =
  if valueOf @n < length p
  then error "permutePrefixSized: cannot permute the sized list, because it's too short"
  else let l = unsafeCoerce ix
       in (unsafeCoerce :: [i] -> SizedList n i)
          $ V.toList $ Data.Vector.fromList l V.// zip p l

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

{-
-- Look Ma, no unsafeCoerce! But it compiles only with GHC >= 9.2,
-- so let's switch to it once we stop using 8.10 and 9.0.
listToSized :: forall n. KnownNat n => [Int] -> SizedList n Int
listToSized []
  | Just Refl <- sameNat (Proxy @n) (Proxy @0) = Z
  | otherwise = error "listToSized: list too short"
listToSized (i : is)
  -- What we really need here to make the types check out is a <= check.
  | EQI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToSized @(n - 1) is
      in i ::: sh
  | LTI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToSizedProxy @(n - 1) is
      in i ::: sh
  | otherwise =
      error "listToSized: list too long"
-}

listToSized :: forall n i. KnownNat n => [i] -> SizedList n i
listToSized list
  | length list == valueOf @n
  = go list unsafeCoerce
  | otherwise
  = error "listToSized: list length disagrees with context"
  where
    go :: [i] -> (forall m. SizedList m i -> r) -> r
    go [] k = k Z
    go (i : rest) k = go rest (\rest' -> k (i ::: rest'))

sizedListToList :: SizedList n i -> [i]
sizedListToList = unsafeCoerce
