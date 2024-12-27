{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( -- * Shaped lists (sized, where size is shape) and their permutations
    zipSized, zipWith_Sized, reverseSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , zipIndex, zipWith_Index
  , shapedToIndex, ixsLengthSNat
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx
  , permutePrefixIndex
  ) where

import Prelude

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
