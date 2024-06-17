{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( -- * Sized lists and their permutations
    IndexOf
  , SizedList, pattern (:::), pattern ZR
  , singletonSized, snocSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  , unsnocSized1, lastSized, initSized, zipSized, zipWith_Sized, reverseSized
  , permInverse
  , backpermutePrefixList, permutePrefixList
  , sizedCompare, listToSized, sizedToList
    -- * Tensor indexes as fully encapsulated sized lists, with operations
  , Index, pattern (:.:), pattern ZIR
  , singletonIndex, snocIndex, appendIndex
  , headIndex, tailIndex, takeIndex, dropIndex, splitAt_Index, splitAtInt_Index
  , unsnocIndex1, lastIndex, initIndex, zipIndex, zipWith_Index
  , listToIndex, indexToList, indexToSized, sizedToIndex
    -- * Tensor shapes as fully encapsulated sized lists, with operations
  , Shape, pattern (:$:), pattern ZSR, IShR
  , singletonShape, appendShape
  , tailShape, takeShape, dropShape, splitAt_Shape
  , lastShape, initShape
  , lengthShape, sizeShape, flattenShape
  , listToShape, shapeToList
  , withListShape, withListSh
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx, zeroOf
  ) where

import Prelude

import           Control.Arrow (first)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import qualified Data.Foldable as Foldable
import           Data.List (foldl', sort)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.Exts (IsList (..))
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Shape as X
import           Data.Array.Nested
  ( IxR (..)
  , ListR (..)
  , ShR (..)
  , pattern (:.:)
  , pattern (:::)
  , pattern ZIR
  , pattern ZR
  )

import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (IntegralF (..))

-- * Sized lists and their permutations

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :.: ZIR).
type IndexOf (f :: TensorType ty) n = Index n (IntOf f)

-- | Standard strict sized lists indexed by the GHC @Nat@ type.
--
-- Note that in GHC 9.4, @[a]@ and our strict @SizedList@ no longer have
-- the same representation in some corner cases, so we can't
-- @unsafeCoerce@ between the two.
-- Wise men say it's because \"coercing @data T = MkT a@ to @data T2 a= MkT2 !a@
-- is no longer working in 9.4\" and we have @StrictData@ set in .cabal file.
-- We could unset @StrictData@ for this file and recover the shared
-- representation, but for as long as we don't have performance problems,
-- let's avoid @unsafeCoerce@ anyway. The list being strict should be
-- more performant, too, given that it's always short (the size of
-- tensor rank) and usually eventually needed. We could still (in GHC 9.4
-- at least) coerce the strict @SizedList@ to @[i]@, but not the other
-- way around.

type SizedList n i = ListR n i

singletonSized :: i -> SizedList 1 i
singletonSized i = i ::: ZR

snocSized :: KnownNat n => SizedList n i -> i -> SizedList (1 + n) i
snocSized ZR last1 = last1 ::: ZR
snocSized (i ::: ix) last1 = i ::: snocSized ix last1

appendSized :: KnownNat n
            => SizedList m i -> SizedList n i -> SizedList (m + n) i
appendSized ZR ix2 = ix2
appendSized (i1 ::: ix1) ix2 = i1 ::: appendSized ix1 ix2

headSized :: SizedList (1 + n) i -> i
headSized ZR = error "headSized: impossible pattern needlessly required"
headSized (i ::: _ix) = i

tailSized :: SizedList (1 + n) i -> SizedList n i
tailSized ZR = error "tailSized: impossible pattern needlessly required"
tailSized (_i ::: ix) = ix

takeSized :: forall len n i. KnownNat len
          => SizedList (len + n) i -> SizedList len i
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len n i. (KnownNat len, KnownNat n)
          => SizedList (len + n) i -> SizedList n i
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized :: (KnownNat m, KnownNat n)
              => SizedList (m + n) i -> (SizedList m i, SizedList n i)
splitAt_Sized ix = (takeSized ix, dropSized ix)

unsnocSized1 :: SizedList (1 + n) i -> (SizedList n i, i)
unsnocSized1 ZR = error "unsnocSized1: impossible pattern needlessly required"
unsnocSized1 (i ::: ix) = case ix of
  ZR -> (ZR, i)
  _ ::: _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::: init1, last1)

lastSized :: SizedList (1 + n) i -> i
lastSized ZR = error "lastSized: impossible pattern needlessly required"
lastSized (i ::: ZR) = i
lastSized (_i ::: ix@(_ ::: _)) = lastSized ix

initSized :: SizedList (1 + n) i -> SizedList n i
initSized ZR = error "initSized: impossible pattern needlessly required"
initSized (_i ::: ZR) = ZR
initSized (i ::: ix@(_ ::: _)) = i ::: initSized ix

zipSized :: SizedList n i -> SizedList n j -> SizedList n (i, j)
zipSized ZR ZR = ZR
zipSized (i ::: irest) (j ::: jrest) = (i, j) ::: zipSized irest jrest
zipSized _ _ = error "zipSized: impossible pattern needlessly required"

zipWith_Sized :: (i -> j -> k) -> SizedList n i -> SizedList n j
              -> SizedList n k
zipWith_Sized _ ZR ZR = ZR
zipWith_Sized f (i ::: irest) (j ::: jrest) =
  f i j ::: zipWith_Sized f irest jrest
zipWith_Sized _ _ _ =
  error "zipWith_Sized: impossible pattern needlessly required"

reverseSized :: SizedList n i -> SizedList n i
reverseSized l = go l ZR
 where
  -- This constraint is mistakenly reported by GHC 9.4 as redundant:
  go :: KnownNat n => SizedList m i -> SizedList n i -> SizedList (m + n) i
  go ZR acc = acc
  go (x ::: xs) acc = go xs (x ::: acc)

-- | As in orthotope, we usually backpermute, in which case a permutation lists
-- indices into the list to permute. However, we use the same type for
-- an occasional forward permutation.
type PermR = [Int]

permInverse :: PermR -> PermR
permInverse perm = map snd $ sort $ zip perm [0 .. length perm - 1]

backpermutePrefixList :: PermR -> [i] -> [i]
backpermutePrefixList p l = map (l !!) p ++ drop (length p) l

-- Boxed vector is not that bad, because we move pointers around,
-- but don't follow them. Storable vectors wouldn't work for Ast.
permutePrefixList :: PermR -> [i] -> [i]
permutePrefixList p l = V.toList $ Data.Vector.fromList l V.// zip p l

-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedCompare :: Monoid m
                 => (i -> i -> m) -> SizedList n i -> SizedList n i -> m
sizedCompare _ ZR ZR = mempty
sizedCompare f (i ::: idx) (j ::: idx') =
  f i j <> sizedCompare f idx idx'
sizedCompare _ _ _ =
  error "sizedCompare: impossible pattern needlessly required"

-- Look Ma, no unsafeCoerce! This compiles only with GHC >= 9.2,
-- but the rest of our code caught up and fails with GHC 9.0 as well.
listToSized :: forall n i. KnownNat n => [i] -> SizedList n i
listToSized = fromList

sizedToList :: SizedList n i -> [i]
sizedToList = Foldable.toList


-- * Tensor indexes as fully encapsulated sized lists, with operations

-- | An index in an n-dimensional array represented as a sized list.
-- The slowest-moving index is at the head position;
-- thus the index 'i :.: j :.: Z' represents 'a[i][j]' in traditional C notation.
--
-- Since we don't have type-level shape information in this variant,
-- we don't assume the indexes are legal, meaning non-negative and bound
-- by some shape. Consequently, there are no runtime checks for that
-- until we we actually attempt projecting. In case that the values
-- are terms, there is no absolute corrcetness criterion anyway,
-- because the eventual integer value depends on a variable valuation.
type Index n i = IxR n i

singletonIndex :: i -> Index 1 i
singletonIndex = IxR . singletonSized

snocIndex :: KnownNat n => Index n i -> i -> Index (1 + n) i
snocIndex (IxR ix) i = IxR $ snocSized ix i

appendIndex :: KnownNat n => Index m i -> Index n i -> Index (m + n) i
appendIndex (IxR ix1) (IxR ix2) = IxR $ appendSized ix1 ix2

headIndex :: Index (1 + n) i -> i
headIndex (IxR ix) = headSized ix

tailIndex :: Index (1 + n) i -> Index n i
tailIndex (IxR ix) = IxR $ tailSized ix

takeIndex :: forall m n i. KnownNat m
          => Index (m + n) i -> Index m i
takeIndex (IxR ix) = IxR $ takeSized ix

dropIndex :: forall m n i. (KnownNat m, KnownNat n)
          => Index (m + n) i -> Index n i
dropIndex (IxR ix) = IxR $ dropSized ix

splitAt_Index :: (KnownNat m, KnownNat n)
              => Index (m + n) i -> (Index m i, Index n i)
splitAt_Index ix = (takeIndex ix, dropIndex ix)

-- TODO: simplify the type machinery; e.g., would p ~ m + n help?
splitAtInt_Index :: forall m n i. (KnownNat m, KnownNat n)
                 => Int -> Index (m + n) i -> (Index m i, Index n i)
splitAtInt_Index j ix =
  if j < 0
  then error "splitAtInt_Index: negative index"
  else case someNatVal $ toInteger j of
    Just (SomeNat proxy) -> case sameNat (Proxy @m) proxy of
      Just Refl -> splitAt_Index ix
      _ -> error "splitAtInt_Index: index differs to what expected from context"
    Nothing -> error "splitAtInt_Index: impossible someNatVal error"

unsnocIndex1 :: Index (1 + n) i -> (Index n i, i)
unsnocIndex1 (IxR ix) = first IxR $ unsnocSized1 ix

lastIndex :: Index (1 + n) i -> i
lastIndex (IxR ix) = lastSized ix

initIndex :: Index (1 + n) i -> Index n i
initIndex (IxR ix) = IxR $ initSized ix

zipIndex :: Index n i -> Index n j -> Index n (i, j)
zipIndex (IxR l1) (IxR l2) = IxR $ zipSized l1 l2

zipWith_Index :: (i -> j -> k) -> Index n i -> Index n j -> Index n k
zipWith_Index f (IxR l1) (IxR l2) = IxR $ zipWith_Sized f l1 l2

listToIndex :: KnownNat n => [i] -> Index n i
listToIndex = fromList

indexToList :: Index n i -> [i]
indexToList = Foldable.toList

indexToSized :: Index n i -> SizedList n i
indexToSized (IxR l) = l

sizedToIndex :: SizedList n i -> Index n i
sizedToIndex = IxR


-- * Tensor shapes as fully encapsulated sized lists, with operations

-- | The shape of an n-dimensional array represented as a sized list.
-- The order of dimensions corresponds to that in @Index@.
type Shape n i = ShR n i

-- This type is user facing so we warn similarly as for IndexOf.
-- | This is a shape of a tensor, which implies the numbers are non-negative.
--
-- Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[4]@ and @(4 :$: ZIR).
type IShR n = Shape n Int

singletonShape :: i -> Shape 1 i
singletonShape = ShR . singletonSized

appendShape :: KnownNat n => Shape m i -> Shape n i -> Shape (m + n) i
appendShape (ShR ix1) (ShR ix2) = ShR $ appendSized ix1 ix2

tailShape :: Shape (1 + n) i -> Shape n i
tailShape (ShR ix) = ShR $ tailSized ix

takeShape :: forall m n i. KnownNat m
          => Shape (m + n) i -> Shape m i
takeShape (ShR ix) = ShR $ takeSized ix

dropShape :: forall m n i. (KnownNat m, KnownNat n)
          => Shape (m + n) i -> Shape n i
dropShape (ShR ix) = ShR $ dropSized ix

splitAt_Shape :: (KnownNat m, KnownNat n)
              => Shape (m + n) i -> (Shape m i, Shape n i)
splitAt_Shape ix = (takeShape ix, dropShape ix)

lastShape :: Shape (1 + n) i -> i
lastShape (ShR ix) = lastSized ix

initShape :: Shape (1 + n) i -> Shape n i
initShape (ShR ix) = ShR $ initSized ix

lengthShape :: forall n i. KnownNat n => Shape n i -> Int
lengthShape _ = valueOf @n

-- | The number of elements in an array of this shape
sizeShape :: (Num i, Integral i) => Shape n i -> Int
sizeShape ZSR = 1
sizeShape (n :$: sh) = fromIntegral n * sizeShape sh

flattenShape :: (Num i, Integral i) => Shape n i -> Shape 1 i
flattenShape = singletonShape . fromIntegral . sizeShape

-- Warning: do not pass a list of strides to this function.
listToShape :: KnownNat n => [i] -> Shape n i
listToShape = fromList

shapeToList :: Shape n i -> [i]
shapeToList = Foldable.toList

-- Both shape representations denote the same shape.
withListShape
  :: [i]
  -> (forall n. KnownNat n => Shape n i -> a)
  -> a
withListShape shList f =
  case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) -> f $ listToShape @n shList
    _ -> error "withListShape: impossible someNatVal error"

-- All three shape representations denote the same shape.
withListSh
  :: KnownShS sh
  => Proxy sh
  -> (forall n. (KnownNat n, X.Rank sh ~ n)
      => IShR n -> a)
  -> a
withListSh (Proxy @sh) f =
  let shList = shapeT @sh
  in case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) ->
      gcastWith (unsafeCoerce Refl :: X.Rank sh :~: n) $
      f $ listToShape @n shList
    _ -> error "withListSh: impossible someNatVal error"


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
--
-- Warning: @fromInteger@ of type @j@ cannot be used.
toLinearIdx :: forall m n j. Num j
            => (Int -> j) -> Shape (m + n) Int -> Index m j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: Shape (m1 + n) Int -> Index m1 j -> j -> j
    go sh ZIR tensidx = fromInt (sizeShape sh) * tensidx
    go (n :$: sh) (i :.: idx) tensidx = go sh idx (fromInt (fromIntegral n) * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
--
-- Warning: @fromInteger@ of type @j@ cannot be used.
fromLinearIdx :: forall n j. (Num j, IntegralF j)
              => (Int -> j) -> Shape n Int -> j -> Index n j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: Shape n1 Int -> j -> (j, Index n1 j)
    go ZSR n = (n, ZIR)
    go (k :$: sh) _ | signum k == 0 =
      (fromInt 0, fromInt 0 :.: zeroOf fromInt sh)
    go (n :$: sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt (fromIntegral n)
          i = tensLin `remF` fromInt (fromIntegral n)
      in (tensLin', i :.: idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> Shape n i -> Index n j
zeroOf _ ZSR = ZIR
zeroOf fromInt (_ :$: sh) = fromInt 0 :.: zeroOf fromInt sh
