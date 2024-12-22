{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @GHC.Nat@-indexed lists, tensors shapes and indexes.
module HordeAd.Util.SizedList
  ( -- * Sized lists and their permutations
    singletonSized, snocSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  , unsnocSized1, lastSized, initSized, zipSized, zipWith_Sized, reverseSized
  , permInverse
  , backpermutePrefixList, permutePrefixList
  , sizedCompare
    -- * Tensor indexes as fully encapsulated sized lists, with operations
  , singletonIndex, snocIndex
  , headIndex, tailIndex, takeIndex, dropIndex, splitAt_Index, splitAtInt_Index
  , unsnocIndex1, lastIndex, initIndex, zipIndex, zipWith_Index
    -- * Tensor shapes as fully encapsulated sized lists, with operations
  , singletonShape
  , tailShape, takeShape, dropShape, splitAt_Shape
  , lastShape, initShape
  , lengthShape, sizeShape, flattenShape
  , withListShape, withListSh
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx, zeroOf
  ) where

import Prelude

import Control.Arrow (first)
import Data.List (sort)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested
  ( IShR
  , IxR (..)
  , KnownShS (..)
  , ListR (..)
  , Rank
  , ShR (..)
  , pattern (:.:)
  , pattern (:::)
  , pattern ZIR
  , pattern ZR
  )

import HordeAd.Core.Types

-- * Sized lists and their permutations

-- | Standard strict sized lists indexed by the GHC @Nat@ type.
--
-- Note that in GHC 9.4, @[a]@ and our strict @ListR@ no longer have
-- the same representation in some corner cases, so we can't
-- @unsafeCoerce@ between the two.
-- Wise men say it's because \"coercing @data T = MkT a@ to @data T2 a= MkT2 !a@
-- is no longer working in 9.4\" and we have @StrictData@ set in .cabal file.
-- We could unset @StrictData@ for this file and recover the shared
-- representation, but for as long as we don't have performance problems,
-- let's avoid @unsafeCoerce@ anyway. The list being strict should be
-- more performant, too, given that it's always short (the size of
-- tensor rank) and usually eventually needed. We could still (in GHC 9.4
-- at least) coerce the strict @ListR@ to @[i]@, but not the other
-- way around.

singletonSized :: i -> ListR 1 i
singletonSized i = i ::: ZR

snocSized :: KnownNat n => ListR n i -> i -> ListR (1 + n) i
snocSized ZR last1 = last1 ::: ZR
snocSized (i ::: ix) last1 = i ::: snocSized ix last1

headSized :: ListR (1 + n) i -> i
headSized ZR = error "headSized: impossible pattern needlessly required"
headSized (i ::: _ix) = i

tailSized :: ListR (1 + n) i -> ListR n i
tailSized ZR = error "tailSized: impossible pattern needlessly required"
tailSized (_i ::: ix) = ix

takeSized :: forall len n i. (KnownNat n, KnownNat len)
          => ListR (len + n) i -> ListR len i
takeSized ix = fromList $ take (valueOf @len) $ toList ix

dropSized :: forall len n i. (KnownNat len, KnownNat n)
          => ListR (len + n) i -> ListR n i
dropSized ix = fromList $ drop (valueOf @len) $ toList ix

splitAt_Sized :: (KnownNat m, KnownNat n)
              => ListR (m + n) i -> (ListR m i, ListR n i)
splitAt_Sized ix = (takeSized ix, dropSized ix)

unsnocSized1 :: ListR (1 + n) i -> (ListR n i, i)
unsnocSized1 ZR = error "unsnocSized1: impossible pattern needlessly required"
unsnocSized1 (i ::: ix) = case ix of
  ZR -> (ZR, i)
  _ ::: _ -> let (init1, last1) = unsnocSized1 ix
             in (i ::: init1, last1)

lastSized :: ListR (1 + n) i -> i
lastSized ZR = error "lastSized: impossible pattern needlessly required"
lastSized (i ::: ZR) = i
lastSized (_i ::: ix@(_ ::: _)) = lastSized ix

initSized :: ListR (1 + n) i -> ListR n i
initSized ZR = error "initSized: impossible pattern needlessly required"
initSized (_i ::: ZR) = ZR
initSized (i ::: ix@(_ ::: _)) = i ::: initSized ix

zipSized :: ListR n i -> ListR n j -> ListR n (i, j)
zipSized ZR ZR = ZR
zipSized (i ::: irest) (j ::: jrest) = (i, j) ::: zipSized irest jrest
zipSized _ _ = error "zipSized: impossible pattern needlessly required"

zipWith_Sized :: (i -> j -> k) -> ListR n i -> ListR n j
              -> ListR n k
zipWith_Sized _ ZR ZR = ZR
zipWith_Sized f (i ::: irest) (j ::: jrest) =
  f i j ::: zipWith_Sized f irest jrest
zipWith_Sized _ _ _ =
  error "zipWith_Sized: impossible pattern needlessly required"

reverseSized :: ListR n i -> ListR n i
reverseSized l = go l ZR
 where
  -- This constraint is mistakenly reported by GHC 9.4 as redundant:
  go :: KnownNat n => ListR m i -> ListR n i -> ListR (m + n) i
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
                 => (i -> i -> m) -> ListR n i -> ListR n i -> m
sizedCompare _ ZR ZR = mempty
sizedCompare f (i ::: idx) (j ::: idx') =
  f i j <> sizedCompare f idx idx'
sizedCompare _ _ _ =
  error "sizedCompare: impossible pattern needlessly required"


-- * Tensor indexes as fully encapsulated sized lists, with operations

-- TODO: make sure this is covered in ox-arrays:
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

singletonIndex :: i -> IxR 1 i
singletonIndex = IxR . singletonSized

snocIndex :: KnownNat n => IxR n i -> i -> IxR (1 + n) i
snocIndex (IxR ix) i = IxR $ snocSized ix i

headIndex :: IxR (1 + n) i -> i
headIndex (IxR ix) = headSized ix

tailIndex :: IxR (1 + n) i -> IxR n i
tailIndex (IxR ix) = IxR $ tailSized ix

takeIndex :: forall m n i. (KnownNat m, KnownNat n)
          => IxR (m + n) i -> IxR m i
takeIndex (IxR ix) = IxR $ takeSized ix

dropIndex :: forall m n i. (KnownNat m, KnownNat n)
          => IxR (m + n) i -> IxR n i
dropIndex (IxR ix) = IxR $ dropSized ix

splitAt_Index :: (KnownNat m, KnownNat n)
              => IxR (m + n) i -> (IxR m i, IxR n i)
splitAt_Index ix = (takeIndex ix, dropIndex ix)

-- TODO: simplify the type machinery; e.g., would p ~ m + n help?
splitAtInt_Index :: forall m n i. (KnownNat m, KnownNat n)
                 => Int -> IxR (m + n) i -> (IxR m i, IxR n i)
splitAtInt_Index j ix =
  if j < 0
  then error "splitAtInt_Index: negative index"
  else case someNatVal $ toInteger j of
    Just (SomeNat proxy) -> case sameNat (Proxy @m) proxy of
      Just Refl -> splitAt_Index ix
      _ -> error "splitAtInt_Index: index differs to what expected from context"
    Nothing -> error "splitAtInt_Index: impossible someNatVal error"

unsnocIndex1 :: IxR (1 + n) i -> (IxR n i, i)
unsnocIndex1 (IxR ix) = first IxR $ unsnocSized1 ix

lastIndex :: IxR (1 + n) i -> i
lastIndex (IxR ix) = lastSized ix

initIndex :: IxR (1 + n) i -> IxR n i
initIndex (IxR ix) = IxR $ initSized ix

zipIndex :: IxR n i -> IxR n j -> IxR n (i, j)
zipIndex (IxR l1) (IxR l2) = IxR $ zipSized l1 l2

zipWith_Index :: (i -> j -> k) -> IxR n i -> IxR n j -> IxR n k
zipWith_Index f (IxR l1) (IxR l2) = IxR $ zipWith_Sized f l1 l2


-- * Tensor shapes as fully encapsulated sized lists, with operations

singletonShape :: i -> ShR 1 i
singletonShape = ShR . singletonSized

tailShape :: ShR (1 + n) i -> ShR n i
tailShape (ShR ix) = ShR $ tailSized ix

takeShape :: forall m n i. (KnownNat n, KnownNat m)
          => ShR (m + n) i -> ShR m i
takeShape (ShR ix) = ShR $ takeSized ix

dropShape :: forall m n i. (KnownNat m, KnownNat n)
          => ShR (m + n) i -> ShR n i
dropShape (ShR ix) = ShR $ dropSized ix

splitAt_Shape :: (KnownNat m, KnownNat n)
              => ShR (m + n) i -> (ShR m i, ShR n i)
splitAt_Shape ix = (takeShape ix, dropShape ix)

lastShape :: ShR (1 + n) i -> i
lastShape (ShR ix) = lastSized ix

initShape :: ShR (1 + n) i -> ShR n i
initShape (ShR ix) = ShR $ initSized ix

lengthShape :: forall n i. KnownNat n => ShR n i -> Int
lengthShape _ = valueOf @n

-- | The number of elements in an array of this shape
sizeShape :: Integral i => ShR n i -> Int
sizeShape ZSR = 1
sizeShape (n :$: sh) = fromIntegral n * sizeShape sh

flattenShape :: Integral i => ShR n i -> ShR 1 i
flattenShape = singletonShape . fromIntegral . sizeShape

-- Both shape representations denote the same shape.
withListShape
  :: forall i a.
     [i]
  -> (forall n. KnownNat n => ShR n i -> a)
  -> a
withListShape shList f =
  case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) -> f $ (fromList shList :: ShR n i)
    _ -> error "withListShape: impossible someNatVal error"

-- All three shape representations denote the same shape.
withListSh
  :: KnownShS sh
  => Proxy sh
  -> (forall n. (KnownNat n, Rank sh ~ n)
      => IShR n -> a)
  -> a
withListSh (Proxy @sh) f =
  let shList = shapeT @sh
  in case someNatVal $ toInteger (length shList) of
    Just (SomeNat @n _) ->
      gcastWith (unsafeCoerce Refl :: Rank sh :~: n) $
      f $ fromList shList
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
            => (Int -> j) -> ShR (m + n) Int -> IxR m j -> j
toLinearIdx fromInt = \sh idx -> go sh idx (fromInt 0)
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: ShR (m1 + n) Int -> IxR m1 j -> j -> j
    go sh ZIR tensidx = fromInt (sizeShape sh) * tensidx
    go (n :$: sh) (i :.: idx) tensidx = go sh idx (fromInt n * tensidx + i)
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
              => (Int -> j) -> ShR n Int -> j -> IxR n j
fromLinearIdx fromInt = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShR n1 Int -> j -> (j, IxR n1 j)
    go ZSR n = (n, ZIR)
    go (k :$: sh) _ | signum k == 0 =
      (fromInt 0, fromInt 0 :.: zeroOf fromInt sh)
    go (n :$: sh) lin =
      let (tensLin, idxInTens) = go sh lin
          tensLin' = tensLin `quotF` fromInt n
          i = tensLin `remF` fromInt n
      in (tensLin', i :.: idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => (Int -> j) -> ShR n i -> IxR n j
zeroOf _ ZSR = ZIR
zeroOf fromInt (_ :$: sh) = fromInt 0 :.: zeroOf fromInt sh
