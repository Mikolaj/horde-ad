{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( -- * Shaped lists (sized, where size is shape) and their permutations
    IntSh, IndexSh
  , SizedListS, pattern (::$), pattern ZS
  -- , consShaped, unconsContShaped
  , singletonSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  -- , unsnocSized1, lastSized
  -- , initSized, zipSized
  , zipWith_Sized, reverseSized
  , Permutation  -- ^ re-exported from "SizedList"
  -- , sizedCompare
  , listToSized, sizedToList
  -- , shapedToSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , IndexS, pattern (:.$), pattern ZIS
  , consIndex, unconsContIndex
  , singletonIndex, appendIndex
  , zipWith_Index
  , listToIndex, indexToList  -- indexToSized, sizedToIndex
  , shapedToIndex, ixsLengthSNat
  -- * Tensor shapes as fully encapsulated shaped lists, with operations
  , ShapeS, pattern (:$$), pattern ZSS
  , ShapedNat, shapedNat, unShapedNat
  , listToShape, shapeToList, takeShS, dropShS
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx

  , permutePrefixIndex
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
import           GHC.Exts (IsList (..))
import           GHC.TypeLits (KnownNat, Nat, type (*))

import qualified Data.Array.Mixed.Permutation as Permutation
import qualified Data.Array.Mixed.Shape as X
import qualified Data.Array.Mixed.Types as X
import           Data.Array.Nested
  (IxS (..), ListS, pattern (:.$), pattern (::$), pattern ZIS, pattern ZS)
import           Data.Array.Nested.Internal.Shape (listsToList, shsToList)

import           HordeAd.Core.Types
import           HordeAd.Util.SizedList (Permutation)
import qualified HordeAd.Util.SizedList as SizedList

-- * Shaped lists and their permutations

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IntSh (f :: TensorType ty) (n :: Nat) = ShapedNat n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh (f :: TensorType ty) (sh :: [Nat]) = IndexS sh (IntOf f)

-- | Lists indexed by shapes, that is, lists of the GHC @Nat@.
type SizedListS n i = ListS n i

-- TODO: use SNat instead of ShapedNat for ShS? or Fin for IxS? but what here?
-- outdated: -- TODO: should we actually replace ::$ with that in the external API?
-- consShaped :: ShapedNat n i -> SizedListS sh i -> SizedListS (n ': sh) i
-- consShaped (ShapedNat i) l = i ::$ l

-- unconsContShaped :: (ShapedNat n i -> k) -> SizedListS (n ': sh) i -> k
-- unconsContShaped f (i ::$ _) = f (ShapedNat i)

singletonSized :: KnownNat n => i n -> SizedListS '[n] i
singletonSized i = i ::$ ZS

appendSized :: KnownShS (sh2 X.++ sh)
            => SizedListS sh2 (Const i) -> SizedListS sh (Const i)
            -> SizedListS (sh2 X.++ sh) (Const i)
appendSized l1 l2 = listToSized $ sizedToList l1 ++ sizedToList l2

headSized :: SizedListS (n ': sh) i -> i n
headSized (i ::$ _ix) = i

tailSized :: SizedListS (n ': sh) i -> SizedListS sh i
tailSized (_i ::$ ix) = ix

takeSized :: forall len sh i. (KnownNat len, KnownShS (Sh.Take len sh))
          => SizedListS sh (Const i) -> SizedListS (Sh.Take len sh) (Const i)
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len sh i. (KnownNat len, KnownShS (Sh.Drop len sh))
          => SizedListS sh (Const i) -> SizedListS  (Sh.Drop len sh) (Const i)
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized
  :: (KnownNat len, KnownShS (Sh.Drop len sh), KnownShS (Sh.Take len sh))
  => SizedListS sh (Const i)
  -> (SizedListS (Sh.Take len sh) (Const i), SizedListS (Sh.Drop len sh) (Const i))
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

-- shapedToSized :: KnownNat (X.Rank sh)
--               => SizedListS sh i -> SizedList.SizedList (X.Rank sh) i
-- shapedToSized = SizedList.listToSized . sizedToList


-- * Tensor indexes as fully encapsulated shaped lists, with operations

type IndexS sh i = IxS sh i

pattern IndexS :: forall {sh :: [Nat]} {i}. ListS sh (Const i) -> IxS sh i
pattern IndexS l = IxS l
{-# COMPLETE IndexS #-}

consIndex :: KnownNat n => ShapedNat n i -> IndexS sh i -> IndexS (n ': sh) i
consIndex (ShapedNat i) l = i :.$ l

unconsContIndex :: (ShapedNat n i -> k) -> IndexS (n ': sh) i -> k
unconsContIndex f (i :.$ _) = f (ShapedNat i)

-- TODO take Fin instead of i?
singletonIndex :: KnownNat n => i -> IndexS '[n] i
singletonIndex i = i :.$ ZIS

appendIndex :: KnownShS (sh2 X.++ sh)
            => IndexS sh2 i -> IndexS sh i -> IndexS (sh2 X.++ sh) i
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

shapedToIndex :: KnownNat (X.Rank sh)
              => IndexS sh i -> SizedList.Index (X.Rank sh) i
shapedToIndex = SizedList.listToIndex . indexToList

ixsLengthSNat :: IxS list i -> SNat (X.Rank list)
ixsLengthSNat ZIS = SNat
ixsLengthSNat (_ :.$ l) | SNat <- ixsLengthSNat l = SNat


-- * Tensor shapes as fully encapsulated shaped lists, with operations

type ShapeS sh = ShS sh

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type role ShapedNat nominal representational
newtype ShapedNat (n :: Nat) a = ShapedNat {unShapedNat :: a}

deriving stock instance Functor (ShapedNat n)

-- TODO: actually check or wrap a check for later, based on a mechanism
-- provided by @a@ somehow
shapedNat :: forall n a. a -> ShapedNat n a
shapedNat = ShapedNat

listToShape :: KnownShS sh => [Int] -> ShapeS sh
listToShape = fromList

shapeToList :: ShapeS sh -> [Int]
shapeToList = shsToList

takeShS :: forall len sh. (KnownNat len, KnownShS (Sh.Take len sh))
        => ShS sh -> ShS (Sh.Take len sh)
takeShS ix = listToShape $ take (valueOf @len) $ shapeToList ix

dropShS :: forall len sh. (KnownNat len, KnownShS (Sh.Drop len sh))
        => ShS sh -> ShS (Sh.Drop len sh)
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
            => (Int -> j) -> ShS (sh1 X.++ sh2) -> IndexS sh1 j
            -> ShapedNat (Sh.Size sh1 * Sh.Size sh2) j
toLinearIdx fromInt = \sh idx -> shapedNat $ go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 X.++ sh2) -> IndexS sh3 j -> j -> j
    go _sh ZIS tensidx = fromInt (sizeT @(sh3 X.++ sh2)) * tensidx
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
fromLinearIdx :: forall sh j. Integral j
              => (Int -> j) -> ShS sh -> ShapedNat (Sh.Size sh) j
              -> IndexS sh j
fromLinearIdx fromInt = \sh (ShapedNat lin) -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IndexS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k@SNat sh) _ | sNatValue k == 0 =
      (fromInt 0, fromInt 0 :.$ zeroOf fromInt sh)
    go ((:$$) n@SNat sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` fromInt (sNatValue n)
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShS sh -> IndexS sh j
zeroOf _ ZSS = ZIS
zeroOf fromInt ((:$$) SNat sh) = fromInt 0 :.$ zeroOf fromInt sh

-- TODO: these hacks stay for now:
permutePrefixSized :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation -> SizedListS sh (Const i) -> SizedListS sh2 (Const i)
permutePrefixSized p ix =
  if length (shapeT @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList p $ sizedToList ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall sh sh2 i. (KnownShS sh, KnownShS sh2)
                   => Permutation -> IndexS sh i -> IndexS sh2 i
permutePrefixIndex p (IndexS ix) = IndexS $ permutePrefixSized p ix
