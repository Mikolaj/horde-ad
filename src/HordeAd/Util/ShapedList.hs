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
  , consShaped, unconsContShaped
  , singletonSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  , unsnocSized1, lastSized, initSized, zipSized, zipWith_Sized, reverseSized
  , Permutation  -- ^ re-exported from "SizedList"
  , backpermutePrefixSized, backpermutePrefixSizedT
  , permutePrefixSized, permutePrefixSizedT
  , sizedCompare, listToSized, sizedToList
  , shapedToSized
    -- * Tensor indexes as fully encapsulated shaped lists, with operations
  , IndexS, pattern (:.$), pattern ZIS
  , consIndex, unconsContIndex
  , singletonIndex, appendIndex
  , zipWith_Index
  , backpermutePrefixIndex, backpermutePrefixIndexT
  , permutePrefixIndex, permutePrefixIndexT
  , listToIndex, indexToList, indexToSized, sizedToIndex, shapedToIndex
  -- * Tensor shapes as fully encapsulated shaped lists, with operations
  , ShapeS, pattern (:$$), pattern ZSS
  , ShapedNat, shapedNat, unShapedNat
  , listToShape, shapeToList
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           GHC.Exts (IsList (..))
import           GHC.TypeLits (KnownNat, Nat, type (*))

import qualified Data.Array.Mixed as X
import           Data.Array.Nested
  (IxS (..), ListS, pattern (:.$), pattern (::$), pattern ZIS, pattern ZS)

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

{-
-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (SizedListS sh i) where
  showsPrec d l = showsPrec d (sizedToList l)
-}

instance KnownShape sh => IsList (SizedListS sh i) where
  type Item (SizedListS sh i) = i
  fromList = listToSized
  toList = sizedToList

-- TODO: should we actually replace ::$ with that in the external API?
consShaped :: ShapedNat n i -> SizedListS sh i -> SizedListS (n ': sh) i
consShaped (ShapedNat i) l = i ::$ l

unconsContShaped :: (ShapedNat n i -> k) -> SizedListS (n ': sh) i -> k
unconsContShaped f (i ::$ _) = f (ShapedNat i)

singletonSized :: i -> SizedListS '[n] i
singletonSized i = i ::$ ZS

appendSized :: KnownShape (sh2 X.++ sh)
            => SizedListS sh2 i -> SizedListS sh i
            -> SizedListS (sh2 X.++ sh) i
appendSized l1 l2 = listToSized $ sizedToList l1 ++ sizedToList l2

headSized :: SizedListS (n ': sh) i -> i
headSized (i ::$ _ix) = i

tailSized :: SizedListS (n ': sh) i -> SizedListS sh i
tailSized (_i ::$ ix) = ix

takeSized :: forall len sh i. (KnownNat len, KnownShape (Sh.Take len sh))
          => SizedListS sh i -> SizedListS (Sh.Take len sh) i
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len sh i. (KnownNat len, KnownShape (Sh.Drop len sh))
          => SizedListS sh i -> SizedListS  (Sh.Drop len sh) i
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized
  :: (KnownNat len, KnownShape (Sh.Drop len sh), KnownShape (Sh.Take len sh))
  => SizedListS sh i
  -> (SizedListS (Sh.Take len sh) i, SizedListS (Sh.Drop len sh) i)
splitAt_Sized ix = (takeSized ix, dropSized ix)

unsnocSized1 :: SizedListS (n ': sh) i -> (SizedListS sh i, i)
unsnocSized1 (i ::$ ix) = case ix of
  ZS -> (ZS, i)
  _ ::$ _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::$ init1, last1)

lastSized :: SizedListS (n ': sh) i -> i
lastSized (i ::$ ZS) = i
lastSized (_i ::$ ix@(_ ::$ _)) = lastSized ix

initSized :: SizedListS (n ': sh) i -> SizedListS sh i
initSized (_i ::$ ZS) = ZS
initSized (i ::$ ix@(_ ::$ _)) = i ::$ initSized ix

zipSized :: SizedListS sh i -> SizedListS sh j -> SizedListS sh (i, j)
zipSized ZS ZS = ZS
zipSized (i ::$ irest) (j ::$ jrest) = (i, j) ::$ zipSized irest jrest

zipWith_Sized :: (i -> j -> k) -> SizedListS sh i -> SizedListS sh j
              -> SizedListS sh k
zipWith_Sized _ ZS ZS = ZS
zipWith_Sized f (i ::$ irest) (j ::$ jrest) =
  f i j ::$ zipWith_Sized f irest jrest

reverseSized :: KnownShape sh => SizedListS sh i -> SizedListS sh i
reverseSized = listToSized . reverse . sizedToList

-- This permutes a prefix of the sized list of the length of the permutation.
-- The rest of the sized list is left intact.
backpermutePrefixSized :: forall sh sh2 i. (KnownShape sh, KnownShape sh2)
                       => Permutation -> SizedListS sh i -> SizedListS sh2 i
backpermutePrefixSized p ix =
  if length (shapeT @sh) < length p
  then error "backpermutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.backpermutePrefixList p $ sizedToList ix

backpermutePrefixSizedT
  :: forall perm sh i.
     (KnownShape perm, KnownShape sh, KnownShape (Sh.Permute perm sh))
  => SizedListS sh i -> SizedListS (Sh.Permute perm sh) i
backpermutePrefixSizedT ix =
  if length (shapeT @sh) < length (shapeT @perm)
  then error "backpermutePrefixShaped: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.backpermutePrefixList (shapeT @perm)
                   $ sizedToList ix

permutePrefixSized :: forall sh sh2 i. (KnownShape sh, KnownShape sh2)
                   => Permutation -> SizedListS sh i -> SizedListS sh2 i
permutePrefixSized p ix =
  if length (shapeT @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList p $ sizedToList ix

permutePrefixSizedT
  :: forall perm sh i. (KnownShape perm, KnownShape sh)
  => SizedListS (Sh.Permute perm sh) i -> SizedListS sh i
permutePrefixSizedT ix =
  if length (shapeT @sh) < length (shapeT @perm)
  then error "permutePrefixShaped: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList (shapeT @perm)
                   $ sizedToList ix

-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedCompare :: Monoid m
                 => (i -> i -> m) -> SizedListS sh i -> SizedListS sh i -> m
sizedCompare _ ZS ZS = mempty
sizedCompare f (i ::$ idx) (j ::$ idx') =
  f i j <> sizedCompare f idx idx'

listToSized :: KnownShape sh => [i] -> SizedListS sh i
listToSized l = tupleToShape l knownShape
 where
  tupleToShape :: [i] -> ShS sh1 -> SizedListS sh1 i
  tupleToShape = \cases
    [] ZSS -> ZS
    _ ZSS -> error $ "listToSized: input list too long; spurious "
                     ++ show (length l)
    [] ks@(_ :$$ _) -> error $ "listToSized: input list too short; missing "
                               ++ show (length (shSToList ks))
    (i : is) (_hd :$$ tl) -> -- @i@ can be, e.g., variables, so we can't assert,
                             -- but this should morally hold, after valuation:
                             -- assert (i <= sNatValue hd) $
                             i ::$ tupleToShape is tl

sizedToList :: SizedListS sh i -> [i]
sizedToList ZS = []
sizedToList (i ::$ is) = i : sizedToList is

shapedToSized :: KnownNat (Sh.Rank sh)
                  => SizedListS sh i -> SizedList.SizedList (Sh.Rank sh) i
shapedToSized = SizedList.listToSized . sizedToList


-- * Tensor indexes as fully encapsulated shaped lists, with operations

type IndexS sh i = IxS sh i

pattern IndexS :: forall {sh :: [Nat]} {i}. ListS sh i -> IxS sh i
pattern IndexS l = IxS l
{-# COMPLETE IndexS #-}

{-
-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (IndexS sh i) where
  showsPrec d (IndexS l) = showsPrec d l
-}

instance KnownShape sh => IsList (IndexS sh i) where
  type Item (IndexS sh i) = i
  fromList = listToIndex
  toList = indexToList

consIndex :: ShapedNat n i -> IndexS sh i -> IndexS (n ': sh) i
consIndex (ShapedNat i) l = i :.$ l

unconsContIndex :: (ShapedNat n i -> k) -> IndexS (n ': sh) i -> k
unconsContIndex f (i :.$ _) = f (ShapedNat i)

singletonIndex :: i -> IndexS '[n] i
singletonIndex = IndexS . singletonSized

appendIndex :: KnownShape (sh2 X.++ sh)
            => IndexS sh2 i -> IndexS sh i -> IndexS (sh2 X.++ sh) i
appendIndex (IndexS ix1) (IndexS ix2) = IndexS $ appendSized ix1 ix2

backpermutePrefixIndex :: forall sh sh2 i. (KnownShape sh, KnownShape sh2)
                       => Permutation -> IndexS sh i -> IndexS sh2 i
backpermutePrefixIndex p (IndexS ix) = IndexS $ backpermutePrefixSized p ix

backpermutePrefixIndexT
  :: forall perm sh i.
     (KnownShape perm, KnownShape sh, KnownShape (Sh.Permute perm sh))
  => IndexS sh i -> IndexS (Sh.Permute perm sh) i
backpermutePrefixIndexT (IndexS ix) = IndexS $ backpermutePrefixSizedT @perm ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall sh sh2 i. (KnownShape sh, KnownShape sh2)
                   => Permutation -> IndexS sh i -> IndexS sh2 i
permutePrefixIndex p (IndexS ix) = IndexS $ permutePrefixSized p ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndexT :: forall perm sh i. (KnownShape perm, KnownShape sh)
                    => IndexS (Sh.Permute perm sh) i -> IndexS sh i
permutePrefixIndexT (IndexS ix) = IndexS $ permutePrefixSizedT @perm ix

zipWith_Index :: (i -> j -> k) -> IndexS sh i -> IndexS sh j -> IndexS sh k
zipWith_Index f (IndexS l1) (IndexS l2) = IndexS $ zipWith_Sized f l1 l2

listToIndex :: KnownShape sh => [i] -> IndexS sh i
listToIndex = IndexS . listToSized

indexToList :: IndexS sh i -> [i]
indexToList (IndexS l) = sizedToList l

indexToSized :: IndexS sh i -> SizedListS sh i
indexToSized (IndexS l) = l

sizedToIndex :: SizedListS sh i -> IndexS sh i
sizedToIndex = IndexS

shapedToIndex :: KnownNat (Sh.Rank sh)
              => IndexS sh i -> SizedList.Index (Sh.Rank sh) i
shapedToIndex = SizedList.listToIndex . indexToList


-- * Tensor shapes as fully encapsulated shaped lists, with operations

type ShapeS sh = ShS sh

{-
-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (ShapeS sh) where
  showsPrec d (ShapeS l) = showsPrec d l
-}

instance KnownShape sh => IsList (ShapeS sh) where
  type Item (ShapeS sh) = Int
  fromList = listToShape
  toList = shapeToList

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

listToShape :: KnownShape sh => [Int] -> ShapeS sh
listToShape l = tupleToShape l knownShape
 where
  tupleToShape :: [Int] -> ShS sh1 -> ShapeS sh1
  tupleToShape = \cases
    [] ZSS -> ZSS
    _ ZSS -> error $ "listToShape: input list too long; spurious "
                     ++ show (length l)
    [] ks@(_ :$$ _) -> error $ "listToShape: input list too short; missing "
                               ++ show (length (shSToList ks))
    (i : is) (hd :$$ tl) -> assert (i == sNatValue hd) $
                            hd :$$ tupleToShape is tl

shapeToList :: ShapeS sh -> [Int]
shapeToList ZSS = []
shapeToList (i :$$ is) = sNatValue i : shapeToList is

-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall sh1 sh2 j. (KnownShape sh2, Num j)
            => ShS (sh1 X.++ sh2) -> IndexS sh1 j
            -> ShapedNat (Sh.Size sh1 * Sh.Size sh2) j
toLinearIdx = \sh idx -> shapedNat $ go sh idx 0
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3. ShS (sh3 X.++ sh2) -> IndexS sh3 j -> j -> j
    go _sh ZIS tensidx = fromIntegral (sizeT @(sh3 X.++ sh2)) * tensidx
    go ((:$$) n sh) (i :.$ idx) tensidx =
      go sh idx (sNatValue n * tensidx + i)
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
              => ShS sh -> ShapedNat (Sh.Size sh) j -> IndexS sh j
fromLinearIdx = \sh (ShapedNat lin) -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShS sh1 -> j -> (j, IndexS sh1 j)
    go ZSS n = (n, ZIS)
    go ((:$$) k@SNat sh) _ | sNatValue k == (0 :: Int) =
      (0, 0 :.$ zeroOf sh)
    go ((:$$) n@SNat sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` sNatValue n
      in (tensLin', i :.$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => ShS sh -> IndexS sh j
zeroOf ZSS = ZIS
zeroOf ((:$$) SNat sh) = 0 :.$ zeroOf sh
