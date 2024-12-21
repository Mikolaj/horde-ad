{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( -- * Shaped lists (sized, where size is shape) and their permutations
  -- , consShaped, unconsContShaped
    singletonSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized, dropIxS
  -- , unsnocSized1, lastSized
  -- , initSized, zipSized
  , zipWith_Sized, reverseSized
  -- , sizedCompare
  , listToSized, sizedToList
  -- , shapedToSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , singletonIndex, appendIndex
  , zipWith_Index
  , listToIndex, indexToList  -- indexToSized, sizedToIndex
  , shapedToIndex, ixsLengthSNat
  -- * Tensor shapes as fully encapsulated shaped lists, with operations
  , listToShape, shapeToList, takeShS, dropShS, takeShX, dropShX
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx
  , permutePrefixIndex
  , ssxRank
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.Functor.Const
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, StaticShX (..), listxRank)
import Data.Array.Nested
  ( IxR
  , IxS (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListS (..)
  , Rank
  , ShS (..)
  , type (++)
  )
import Data.Array.Nested.Internal.Shape (listsToList)

import HordeAd.Core.Types
import HordeAd.Util.SizedList qualified as SizedList

-- * Shaped lists and their permutations

singletonSized :: KnownNat n => i n -> ListS '[n] i
singletonSized i = i ::$ ZS

appendSized :: KnownShS (sh2 ++ sh)
            => ListS sh2 (Const i) -> ListS sh (Const i)
            -> ListS (sh2 ++ sh) (Const i)
appendSized l1 l2 = listToSized $ sizedToList l1 ++ sizedToList l2

headSized :: ListS (n ': sh) i -> i n
headSized (i ::$ _ix) = i

tailSized :: ListS (n ': sh) i -> ListS sh i
tailSized (_i ::$ ix) = ix

takeSized :: forall len sh i. (KnownNat len, KnownShS (Take len sh))
          => ListS sh (Const i) -> ListS (Take len sh) (Const i)
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len sh i. (KnownNat len, KnownShS (Drop len sh))
          => ListS sh (Const i) -> ListS (Drop len sh) (Const i)
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized
  :: (KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => ListS sh (Const i)
  -> (ListS (Take len sh) (Const i), ListS (Drop len sh) (Const i))
splitAt_Sized ix = (takeSized ix, dropSized ix)

dropIxS :: forall len sh i. (KnownNat len, KnownShS (Drop len sh))
        => IxS sh i -> IxS (Drop len sh) i
dropIxS (IxS ix) = IxS $ dropSized ix

{-
unsnocSized1 :: ListS (n ': sh) i -> (ListS sh i, i)
unsnocSized1 (i ::$ ix) = case ix of
  ZS -> (ZS, i)
  _ ::$ _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::$ init1, last1)
-}

-- lastSized :: ListS (n ': sh) i -> i
-- lastSized (i ::$ ZS) = i
-- lastSized (_i ::$ ix@(_ ::$ _)) = lastSized ix

-- initSized :: ListS (n ': sh) i -> ListS sh i
-- initSized (_i ::$ ZS) = ZS
-- initSized (i ::$ ix@(_ ::$ _)) = i ::$ initSized ix

-- zipSized :: ListS sh i -> ListS sh j -> ListS sh (i, j)
-- zipSized ZS ZS = ZS
-- zipSized (i ::$ irest) (j ::$ jrest) = (i, j) ::$ zipSized irest jrest

zipWith_Sized :: (i -> j -> k)
              -> ListS sh (Const i) -> ListS sh (Const j)
              -> ListS sh (Const k)
zipWith_Sized _ ZS ZS = ZS
zipWith_Sized f ((Const i) ::$ irest) ((Const j) ::$ jrest) =
  Const (f i j) ::$ zipWith_Sized f irest jrest

reverseSized :: KnownShS sh => ListS sh (Const i) -> ListS sh (Const i)
reverseSized = listToSized . reverse . sizedToList

{-
-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedCompare :: Monoid m
             => (i -> i -> m) -> ListS sh i -> ListS sh i -> m
sizedCompare _ ZS ZS = mempty
sizedCompare f (i ::$ idx) (j ::$ idx') =
  f i j <> sizedCompare f idx idx'
-}

listToSized :: KnownShS sh => [i] -> ListS sh (Const i)
listToSized = fromList

sizedToList :: ListS sh (Const i) -> [i]
sizedToList = listsToList

-- shapedToSized :: KnownNat (Rank sh)
--               => ListS sh i -> ListR (Rank sh) i
-- shapedToSized = SizedList.listToSized . sizedToList


-- * Tensor indexes as fully encapsulated shaped lists, with operations

-- TODO take Fin instead of i?
singletonIndex :: KnownNat n => i -> IxS '[n] i
singletonIndex i = i :.$ ZIS

appendIndex :: KnownShS (sh2 ++ sh)
            => IxS sh2 i -> IxS sh i -> IxS (sh2 ++ sh) i
appendIndex (IxS ix1) (IxS ix2) = IxS $ appendSized ix1 ix2

zipWith_Index :: (i -> j -> k) -> IxS sh i -> IxS sh j -> IxS sh k
zipWith_Index f (IxS l1) (IxS l2) = IxS $ zipWith_Sized f l1 l2

listToIndex :: KnownShS sh => [i] -> IxS sh i
listToIndex = fromList

indexToList :: IxS sh i -> [i]
indexToList = Foldable.toList

-- indexToSized :: IxS sh i -> ListS sh i
-- indexToSized (IxS l) = l

-- sizedToIndex :: ListS sh i -> IxS sh i
-- sizedToIndex = IxS

shapedToIndex :: KnownNat (Rank sh)
              => IxS sh i -> IxR (Rank sh) i
shapedToIndex = SizedList.listToIndex . indexToList

ixsLengthSNat :: IxS list i -> SNat (Rank list)
ixsLengthSNat ZIS = SNat
ixsLengthSNat (_ :.$ l) | SNat <- ixsLengthSNat l = SNat


-- * Tensor shapes as fully encapsulated shaped lists, with operations

listToShape :: KnownShS sh => [Int] -> ShS sh
listToShape = fromList

shapeToList :: KnownShS sh => ShS sh -> [Int]
shapeToList = toList

takeShS :: forall len sh. (KnownNat len, KnownShS sh, KnownShS (Take len sh))
        => ShS sh -> ShS (Take len sh)
takeShS ix = fromList $ take (valueOf @len) $ toList ix

dropShS :: forall len sh. (KnownNat len, KnownShS sh, KnownShS (Drop len sh))
        => ShS sh -> ShS (Drop len sh)
dropShS ix = fromList $ drop (valueOf @len) $ toList ix

takeShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
takeShX ix = fromList $ take (valueOf @len) $ toList ix

dropShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
dropShX ix = fromList $ drop (valueOf @len) $ toList ix


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall sh1 sh2 j. (KnownShS sh2, Num j)
            => (Int -> j) -> ShS (sh1 ++ sh2) -> IxS sh1 j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 ++ sh2) -> IxS sh3 j -> j -> j
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
              => (Int -> j) -> ShS sh -> j -> IxS sh j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IxS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k@SNat sh) _ | sNatValue k == 0 =
      (fromInt 0, fromInt 0 :.$ zeroOf fromInt sh)
    go ((:$$) n@SNat sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (sNatValue n)
          i = tensLin `remF` fromInt (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShS sh -> IxS sh j
zeroOf _ ZSS = ZIS
zeroOf fromInt ((:$$) SNat sh) = fromInt 0 :.$ zeroOf fromInt sh

-- TODO: these hacks stay for now:
permutePrefixSized :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation.PermR -> ListS sh (Const i) -> ListS sh2 (Const i)
permutePrefixSized p ix =
  if length (shapeT @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList p $ sizedToList ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation.PermR -> IxS sh i -> IxS sh2 i
permutePrefixIndex p (IxS ix) = IxS $ permutePrefixSized p ix

ssxRank :: StaticShX sh -> SNat (Rank sh)
ssxRank (StaticShX l) = listxRank l
