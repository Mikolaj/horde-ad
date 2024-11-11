{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( Take, Drop, Last, Init
  , IndexShX
  , -- * Shaped lists (sized, where size is shape) and their permutations
    IndexSh
  , SizedListS, pattern (::$), pattern ZS
  -- , consShaped, unconsContShaped
  , singletonSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  -- , unsnocSized1, lastSized
  -- , initSized, zipSized
  , zipWith_Sized, reverseSized
  -- , sizedCompare
  , listToSized, sizedToList
  -- , shapedToSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , IndexS, pattern (:.$), pattern ZIS
  , singletonIndex, appendIndex
  , zipWith_Index
  , listToIndex, indexToList  -- indexToSized, sizedToIndex
  , shapedToIndex, ixsLengthSNat
  -- * Tensor shapes as fully encapsulated shaped lists, with operations
  , ShapeS, pattern (:$$), pattern ZSS
  , listToShape, shapeToList, takeShS, dropShS
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx

  , permutePrefixIndex
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.Functor.Const
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, Nat, type (-))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Nested
  ( IxS (..)
  , IxX
  , ListS
  , Rank
  , pattern (:.$)
  , pattern (::$)
  , pattern ZIS
  , pattern ZS
  , type (++)
  )
import Data.Array.Nested.Internal.Shape (listsToList, shsToList)

import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (IntegralF (..), valueOf)
import HordeAd.Util.SizedList qualified as SizedList

type family Take (n :: Nat) (xs :: [k]) :: [k] where
    Take 0 xs = '[]
    Take n (x ': xs) = x ': Take (n - 1) xs

type family Drop (n :: Nat) (xs :: [k]) :: [k] where
    Drop 0 xs = xs
    Drop n (x ': xs) = Drop (n - 1) xs

type family Last (xs :: [k]) where
  Last '[x] = x
  Last (x ': xs) = Last xs

type family Init (xs :: [k]) where
  Init '[x] = '[]
  Init (x ': xs) = x ': Init xs

type IndexShX (f :: Target) (sh :: [Maybe Nat]) = IxX sh (IntOf f)


-- * Shaped lists and their permutations

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh (f :: Target) (sh :: [Nat]) = IxS sh (IntOf f)

-- | Lists indexed by shapes, that is, lists of the GHC @Nat@.
type SizedListS n i = ListS n i

singletonSized :: KnownNat n => i n -> SizedListS '[n] i
singletonSized i = i ::$ ZS

appendSized :: KnownShS (sh2 ++ sh)
            => SizedListS sh2 (Const i) -> SizedListS sh (Const i)
            -> SizedListS (sh2 ++ sh) (Const i)
appendSized l1 l2 = listToSized $ sizedToList l1 ++ sizedToList l2

headSized :: SizedListS (n ': sh) i -> i n
headSized (i ::$ _ix) = i

tailSized :: SizedListS (n ': sh) i -> SizedListS sh i
tailSized (_i ::$ ix) = ix

takeSized :: forall len sh i. (KnownNat len, KnownShS (Take len sh))
          => SizedListS sh (Const i) -> SizedListS (Take len sh) (Const i)
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len sh i. (KnownNat len, KnownShS (Drop len sh))
          => SizedListS sh (Const i) -> SizedListS  (Drop len sh) (Const i)
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized
  :: (KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => SizedListS sh (Const i)
  -> (SizedListS (Take len sh) (Const i), SizedListS (Drop len sh) (Const i))
splitAt_Sized ix = (takeSized ix, dropSized ix)

{-
unsnocSized1 :: SizedListS (n ': sh) i -> (SizedListS sh i, i)
unsnocSized1 (i ::$ ix) = case ix of
  ZS -> (ZS, i)
  _ ::$ _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::$ init1, last1)
-}

-- lastSized :: SizedListS (n ': sh) i -> i
-- lastSized (i ::$ ZS) = i
-- lastSized (_i ::$ ix@(_ ::$ _)) = lastSized ix

-- initSized :: SizedListS (n ': sh) i -> SizedListS sh i
-- initSized (_i ::$ ZS) = ZS
-- initSized (i ::$ ix@(_ ::$ _)) = i ::$ initSized ix

-- zipSized :: SizedListS sh i -> SizedListS sh j -> SizedListS sh (i, j)
-- zipSized ZS ZS = ZS
-- zipSized (i ::$ irest) (j ::$ jrest) = (i, j) ::$ zipSized irest jrest

zipWith_Sized :: (i -> j -> k)
              -> SizedListS sh (Const i) -> SizedListS sh (Const j)
              -> SizedListS sh (Const k)
zipWith_Sized _ ZS ZS = ZS
zipWith_Sized f ((Const i) ::$ irest) ((Const j) ::$ jrest) =
  Const (f i j) ::$ zipWith_Sized f irest jrest

reverseSized :: KnownShS sh => SizedListS sh (Const i) -> SizedListS sh (Const i)
reverseSized = listToSized . reverse . sizedToList

{-
-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedCompare :: Monoid m
             => (i -> i -> m) -> SizedListS sh i -> SizedListS sh i -> m
sizedCompare _ ZS ZS = mempty
sizedCompare f (i ::$ idx) (j ::$ idx') =
  f i j <> sizedCompare f idx idx'
-}

listToSized :: KnownShS sh => [i] -> SizedListS sh (Const i)
listToSized = fromList

sizedToList :: SizedListS sh (Const i) -> [i]
sizedToList = listsToList

-- shapedToSized :: KnownNat (Rank sh)
--               => SizedListS sh i -> SizedList.SizedList (Rank sh) i
-- shapedToSized = SizedList.listToSized . sizedToList


-- * Tensor indexes as fully encapsulated shaped lists, with operations

type IndexS sh i = IxS sh i

pattern IndexS :: forall {sh :: [Nat]} {i}. ListS sh (Const i) -> IxS sh i
pattern IndexS l = IxS l
{-# COMPLETE IndexS #-}

-- TODO take Fin instead of i?
singletonIndex :: KnownNat n => i -> IndexS '[n] i
singletonIndex i = i :.$ ZIS

appendIndex :: KnownShS (sh2 ++ sh)
            => IndexS sh2 i -> IndexS sh i -> IndexS (sh2 ++ sh) i
appendIndex (IndexS ix1) (IndexS ix2) = IndexS $ appendSized ix1 ix2

zipWith_Index :: (i -> j -> k) -> IndexS sh i -> IndexS sh j -> IndexS sh k
zipWith_Index f (IndexS l1) (IndexS l2) = IndexS $ zipWith_Sized f l1 l2

listToIndex :: KnownShS sh => [i] -> IndexS sh i
listToIndex = fromList

indexToList :: IndexS sh i -> [i]
indexToList = Foldable.toList

-- indexToSized :: IndexS sh i -> SizedListS sh i
-- indexToSized (IndexS l) = l

-- sizedToIndex :: SizedListS sh i -> IndexS sh i
-- sizedToIndex = IndexS

shapedToIndex :: KnownNat (Rank sh)
              => IndexS sh i -> SizedList.Index (Rank sh) i
shapedToIndex = SizedList.listToIndex . indexToList

ixsLengthSNat :: IxS list i -> SNat (Rank list)
ixsLengthSNat ZIS = SNat
ixsLengthSNat (_ :.$ l) | SNat <- ixsLengthSNat l = SNat


-- * Tensor shapes as fully encapsulated shaped lists, with operations

type ShapeS sh = ShS sh

listToShape :: KnownShS sh => [Int] -> ShapeS sh
listToShape = fromList

shapeToList :: ShapeS sh -> [Int]
shapeToList = shsToList

takeShS :: forall len sh. (KnownNat len, KnownShS (Take len sh))
        => ShS sh -> ShS (Take len sh)
takeShS ix = listToShape $ take (valueOf @len) $ shapeToList ix

dropShS :: forall len sh. (KnownNat len, KnownShS (Drop len sh))
        => ShS sh -> ShS (Drop len sh)
dropShS ix = listToShape $ drop (valueOf @len) $ shapeToList ix


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall sh1 sh2 j. (KnownShS sh2, Num j)
            => (Int -> j) -> ShS (sh1 ++ sh2) -> IndexS sh1 j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 ++ sh2) -> IndexS sh3 j -> j -> j
    go _sh ZIS tensidx = fromInt (sizeT @(sh3 ++ sh2)) * tensidx
    go ((:$$) n sh) (i :.$ idx) tensidx =
      go sh idx (fromInt (sNatValue n) * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdx :: forall sh j. (Num j, IntegralF j)
              => (Int -> j) -> ShS sh -> j -> IndexS sh j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IndexS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k@SNat sh) _ | sNatValue k == 0 =
      (fromInt 0, fromInt 0 :.$ zeroOf fromInt sh)
    go ((:$$) n@SNat sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (sNatValue n)
          i = tensLin `remF` fromInt (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShS sh -> IndexS sh j
zeroOf _ ZSS = ZIS
zeroOf fromInt ((:$$) SNat sh) = fromInt 0 :.$ zeroOf fromInt sh

-- TODO: these hacks stay for now:
permutePrefixSized :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation.PermR -> SizedListS sh (Const i) -> SizedListS sh2 (Const i)
permutePrefixSized p ix =
  if length (shapeT @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList p $ sizedToList ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation.PermR -> IndexS sh i -> IndexS sh2 i
permutePrefixIndex p (IndexS ix) = IndexS $ permutePrefixSized p ix
