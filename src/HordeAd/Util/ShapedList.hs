{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( -- * Shaped lists (sized, where size is shape) and their permutations
    takeSized, dropSized, splitAt_Sized, dropIxS
  , zipSized, zipWith_Sized, reverseSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , zipIndex, zipWith_Index
  , shapedToIndex, ixsLengthSNat
    -- * Tensor shapes as fully encapsulated shaped lists, with operations
  , takeShS, dropShS, takeShX, dropShX
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx
  , permutePrefixIndex
  , ssxRank, ixsRank
  , listsTakeLen, listsDropLen, shsDropLen
  ) where

import Prelude

import Data.Coerce (coerce)
import Data.Functor.Const
import Data.Type.Equality (gcastWith, (:~:))
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation (DropLen, TakeLen)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, StaticShX (..), listxRank)
import Data.Array.Mixed.Types (fromSNat', unsafeCoerceRefl)
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
import Data.Array.Nested.Internal.Shape
  (listsDropLenPerm, listsRank, shsLength, shsRank)

import HordeAd.Core.Types
import HordeAd.Util.SizedList qualified as SizedList

-- * Shaped lists and their permutations

takeSized :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Take len sh))
          => ListS sh (Const i) -> ListS (Take len sh) (Const i)
takeSized ix = fromList $ take (valueOf @len) $ toList ix

dropSized :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
          => ListS sh (Const i) -> ListS (Drop len sh) (Const i)
dropSized ix = fromList $ drop (valueOf @len) $ toList ix

splitAt_Sized
  :: (KnownShS sh, KnownNat len, KnownShS (Drop len sh), KnownShS (Take len sh))
  => ListS sh (Const i)
  -> (ListS (Take len sh) (Const i), ListS (Drop len sh) (Const i))
splitAt_Sized ix = (takeSized ix, dropSized ix)

dropIxS :: forall len sh i. (KnownShS sh, KnownNat len, KnownShS (Drop len sh))
        => IxS sh i -> IxS (Drop len sh) i
dropIxS (IxS ix) = IxS $ dropSized ix

-- lastSized :: ListS (n ': sh) i -> i
-- lastSized (i ::$ ZS) = i
-- lastSized (_i ::$ ix@(_ ::$ _)) = lastSized ix

-- initSized :: ListS (n ': sh) i -> ListS sh i
-- initSized (_i ::$ ZS) = ZS
-- initSized (i ::$ ix@(_ ::$ _)) = i ::$ initSized ix

zipSized :: ListS sh (Const i) -> ListS sh (Const j) -> ListS sh (Const (i, j))
zipSized ZS ZS = ZS
zipSized (Const i ::$ irest) (Const j ::$ jrest) =
  Const (i, j) ::$ zipSized irest jrest

zipWith_Sized :: (i -> j -> k)
              -> ListS sh (Const i) -> ListS sh (Const j)
              -> ListS sh (Const k)
zipWith_Sized _ ZS ZS = ZS
zipWith_Sized f (Const i ::$ irest) (Const j ::$ jrest) =
  Const (f i j) ::$ zipWith_Sized f irest jrest

reverseSized :: KnownShS sh => ListS sh (Const i) -> ListS sh (Const i)
reverseSized = fromList . reverse . toList

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

-- * Tensor indexes as fully encapsulated shaped lists, with operations

zipIndex :: IxS sh i -> IxS sh j -> IxS sh (i, j)
zipIndex (IxS l1) (IxS l2) = IxS $ zipSized l1 l2

zipWith_Index :: (i -> j -> k) -> IxS sh i -> IxS sh j -> IxS sh k
zipWith_Index f (IxS l1) (IxS l2) = IxS $ zipWith_Sized f l1 l2

shapedToIndex :: (KnownShS sh, KnownNat (Rank sh))
              => IxS sh i -> IxR (Rank sh) i
shapedToIndex = fromList . toList

ixsLengthSNat :: IxS list i -> SNat (Rank list)
ixsLengthSNat ZIS = SNat
ixsLengthSNat (_ :.$ l) | SNat <- ixsLengthSNat l = SNat


-- * Tensor shapes as fully encapsulated shaped lists, with operations

-- TODO
takeShS :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Take len sh)
takeShS sh0 = fromList2 $ take (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Take len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "takeShS: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "takeShS: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

-- TODO
dropShS :: forall len sh. (KnownNat len, KnownShS sh)
        => ShS sh -> ShS (Drop len sh)
dropShS sh0 = fromList2 $ drop (valueOf @len) $ toList sh0
 where
  fromList2 topl = ShS (go (knownShS @sh) $ replicate (valueOf @len) (-1) ++ topl)
    where  -- TODO: induction over (unary) SNat?
      go :: forall sh'. ShS sh' -> [Int] -> ListS (Drop len sh') SNat
      go _ [] = gcastWith (unsafeCoerceRefl :: len :~: 0) $ gcastWith (unsafeCoerceRefl :: sh' :~: '[]) ZS
      go (sn :$$ sh) (i : is)
        | i == -1 = unsafeCoerce $ go sh is
        | i == fromSNat' sn = unsafeCoerce $ sn ::$ go sh is
        | otherwise = error $ "dropShS: Value does not match typing (type says "
                                ++ show (fromSNat' sn) ++ ", list contains " ++ show i ++ ")"
      go _ _ = error $ "dropShS: Mismatched list length (type says "
                         ++ show (shsLength (knownShS @sh)) ++ ", list has length "
                         ++ show (length topl) ++ ")"

takeShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Take len sh))
        => IShX sh -> IShX (Take len sh)
takeShX sh0 = fromList $ take (valueOf @len) $ toList sh0

dropShX :: forall len sh. (KnownNat len, KnownShX sh, KnownShX (Drop len sh))
        => IShX sh -> IShX (Drop len sh)
dropShX sh0 = fromList $ drop (valueOf @len) $ toList sh0


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
  if sNatValue (shsRank $ knownShS @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else fromList $ SizedList.permutePrefixList p $ toList ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation.PermR -> IxS sh i -> IxS sh2 i
permutePrefixIndex p (IxS ix) = IxS $ permutePrefixSized p ix

ssxRank :: StaticShX sh -> SNat (Rank sh)
ssxRank (StaticShX l) = listxRank l

ixsRank :: IxS sh i -> SNat (Rank sh)
ixsRank (IxS l) = listsRank l

listsTakeLen :: forall f g sh1 sh2.
                ListS sh1 f -> ListS sh2 g -> ListS (TakeLen sh1 sh2) g
listsTakeLen ZS _ = ZS
listsTakeLen (_ ::$ sh1) (n ::$ sh2) = n ::$ listsTakeLen sh1 sh2
listsTakeLen (_ ::$ _) ZS = error "listsTakeLen: list too short"

listsDropLen :: forall f g sh1 sh2.
                ListS sh1 f -> ListS sh2 g -> ListS (DropLen sh1 sh2) g
listsDropLen ZS sh = sh
listsDropLen (_ ::$ sh1) (_ ::$ sh2) = listsDropLen sh1 sh2
listsDropLen (_ ::$ _) ZS = error "listsDropLen: list too short"

shsDropLen :: Permutation.Perm is -> ShS sh -> ShS (DropLen is sh)
shsDropLen = coerce (listsDropLenPerm @SNat)
