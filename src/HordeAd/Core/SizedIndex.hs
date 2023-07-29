{-# LANGUAGE DerivingStrategies, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Sized indexes and shapes for tensors.
module HordeAd.Core.SizedIndex
  ( -- * Concrete type synonyms to be used in many other modules
    ShapeInt, Permutation
    -- * Tensor indexes as fully encapsulated sized lists, with operations
  , Index, pattern (:.), pattern ZI
  , singletonIndex, snocIndex, appendIndex
  , headIndex, tailIndex, takeIndex, dropIndex, splitAt_Index, splitAtInt_Index
  , unsnocIndex1, lastIndex, initIndex, zipIndex, zipWith_Index
  , backpermutePrefixIndex, permutePrefixIndex
  , listToIndex, indexToList, indexToSizedList, sizedListToIndex
    -- * Tensor shapes as fully encapsulated sized lists, with operations
  , Shape, pattern (:$), pattern ZS
  , singletonShape, appendShape, tailShape, takeShape, dropShape
  , splitAt_Shape, lastShape, initShape, lengthShape, sizeShape, flattenShape
  , backpermutePrefixShape
  , listShapeToShape, shapeToList
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx, zeroOf
  ) where

import Prelude

import Control.Arrow (first)
import Data.Array.Internal (valueOf)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))

import HordeAd.Core.SizedList

-- * Concrete type synonyms to be used in many other modules

-- This type is user facing so we warn similarly as for IndexOf.
-- | This is a shape of a tensor, which implies the numbers are non-negative.
--
-- Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[4]@ and @(4 :$ ZI).
type ShapeInt n = Shape n Int


-- * Tensor indexes as fully encapsulated sized lists, with operations

-- | An index in an n-dimensional array represented as a sized list.
-- The slowest-moving index is at the head position;
-- thus the index 'i :. j :. Z' represents 'a[i][j]' in traditional C notation.
--
-- Since we don't have type-level shape information in this variant,
-- we don't assume the indexes are legal, meaning non-negative and bound
-- by some shape. Consequently, there are no runtime checks for that
-- until we we actually attempt projecting. In case that the values
-- are terms, there is no absolute corrcetness criterion anyway,
-- because the eventual integer value depends on a variable valuation.
newtype Index n i = Index (SizedList n i)
  deriving (Eq, Ord)

-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (Index n i) where
  showsPrec d (Index l) = showsPrec d l

pattern ZI :: forall n i. () => n ~ 0 => Index n i
pattern ZI = Index Z

infixr 3 :.
pattern (:.) :: forall n1 i. KnownNat n1 => forall n. (KnownNat n, (1 + n) ~ n1)
             => i -> Index n i -> Index n1 i
pattern i :. sh <- (unconsIndex -> Just (UnconsIndexRes sh i))
  where i :. (Index sh) = Index (i ::: sh)
{-# COMPLETE ZI, (:.) #-}

data UnconsIndexRes i n1 =
  forall n. n1 ~ (1 + n) => UnconsIndexRes (Index n i) i
unconsIndex :: Index n1 i -> Maybe (UnconsIndexRes i n1)
unconsIndex (Index sh) = case sh of
  i ::: sh' -> Just (UnconsIndexRes (Index sh') i)
  Z -> Nothing

deriving newtype instance Functor (Index n)

instance Foldable (Index n) where
  foldr f z l = foldr f z (indexToList l)

instance KnownNat n => IsList (Index n i) where
  type Item (Index n i) = i
  fromList = listToIndex
  toList = indexToList

singletonIndex :: i -> Index 1 i
singletonIndex = Index . singletonSized

snocIndex :: KnownNat n => Index n i -> i -> Index (1 + n) i
snocIndex (Index ix) i = Index $ snocSized ix i

appendIndex :: KnownNat n => Index m i -> Index n i -> Index (m + n) i
appendIndex (Index ix1) (Index ix2) = Index $ appendSized ix1 ix2

headIndex :: Index (1 + n) i -> i
headIndex (Index ix) = headSized ix

tailIndex :: Index (1 + n) i -> Index n i
tailIndex (Index ix) = Index $ tailSized ix

takeIndex :: forall m n i. KnownNat m
          => Index (m + n) i -> Index m i
takeIndex (Index ix) = Index $ takeSized ix

dropIndex :: forall m n i. (KnownNat m, KnownNat n)
          => Index (m + n) i -> Index n i
dropIndex (Index ix) = Index $ dropSized ix

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
unsnocIndex1 (Index ix) = first Index $ unsnocSized1 ix

lastIndex :: Index (1 + n) i -> i
lastIndex (Index ix) = lastSized ix

initIndex :: Index (1 + n) i -> Index n i
initIndex (Index ix) = Index $ initSized ix

zipIndex :: Index n i -> Index n j -> Index n (i, j)
zipIndex (Index l1) (Index l2) = Index $ zipSized l1 l2

zipWith_Index :: (i -> j -> k) -> Index n i -> Index n j -> Index n k
zipWith_Index f (Index l1) (Index l2) = Index $ zipWith_Sized f l1 l2

backpermutePrefixIndex :: forall n i. KnownNat n
                       => Permutation -> Index n i -> Index n i
backpermutePrefixIndex p (Index ix) = Index $ backpermutePrefixSized p ix

-- Inverse permutation of indexes corresponds to normal permutation
-- of the shape of the projected tensor.
permutePrefixIndex :: forall n i. KnownNat n
                   => Permutation -> Index n i -> Index n i
permutePrefixIndex p (Index ix) = Index $ permutePrefixSized p ix

listToIndex :: KnownNat n => [i] -> Index n i
listToIndex = Index . listToSized

indexToList :: Index n i -> [i]
indexToList (Index l) = sizedListToList l

indexToSizedList :: Index n i -> SizedList n i
indexToSizedList (Index l) = l

sizedListToIndex :: SizedList n i -> Index n i
sizedListToIndex = Index


-- * Tensor shapes as fully encapsulated sized lists, with operations

-- | The shape of an n-dimensional array represented as a sized list.
-- The order of dimensions corresponds to that in @Index@.
newtype Shape n i = Shape (SizedList n i)
  deriving Eq

-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (Shape n i) where
  showsPrec d (Shape l) = showsPrec d l

pattern ZS :: forall n i. () => n ~ 0 => Shape n i
pattern ZS = Shape Z

infixr 3 :$
pattern (:$) :: forall n1 i. KnownNat n1 => forall n. (KnownNat n, (1 + n) ~ n1)
             => i -> Shape n i -> Shape n1 i
pattern i :$ sh <- (unconsShape -> Just (UnconsShapeRes sh i))
  where i :$ (Shape sh) = Shape (i ::: sh)
{-# COMPLETE ZS, (:$) #-}

data UnconsShapeRes i n1 =
  forall n. n1 ~ (1 + n) => UnconsShapeRes (Shape n i) i
unconsShape :: Shape n1 i -> Maybe (UnconsShapeRes i n1)
unconsShape (Shape sh) = case sh of
  i ::: sh' -> Just (UnconsShapeRes (Shape sh') i)
  Z -> Nothing

deriving newtype instance Functor (Shape n)

instance Foldable (Shape n) where
  foldr f z l = foldr f z (shapeToList l)

instance KnownNat n => IsList (Shape n i) where
  type Item (Shape n i) = i
  fromList = listShapeToShape
  toList = shapeToList

singletonShape :: i -> Shape 1 i
singletonShape = Shape . singletonSized

appendShape :: KnownNat n => Shape m i -> Shape n i -> Shape (m + n) i
appendShape (Shape ix1) (Shape ix2) = Shape $ appendSized ix1 ix2

tailShape :: Shape (1 + n) i -> Shape n i
tailShape (Shape ix) = Shape $ tailSized ix

takeShape :: forall m n i. KnownNat m
          => Shape (m + n) i -> Shape m i
takeShape (Shape ix) = Shape $ takeSized ix

dropShape :: forall m n i. (KnownNat m, KnownNat n)
          => Shape (m + n) i -> Shape n i
dropShape (Shape ix) = Shape $ dropSized ix

splitAt_Shape :: (KnownNat m, KnownNat n)
              => Shape (m + n) i -> (Shape m i, Shape n i)
splitAt_Shape ix = (takeShape ix, dropShape ix)

lastShape :: Shape (1 + n) i -> i
lastShape (Shape ix) = lastSized ix

initShape :: Shape (1 + n) i -> Shape n i
initShape (Shape ix) = Shape $ initSized ix

lengthShape :: forall n i. KnownNat n => Shape n i -> Int
lengthShape _ = valueOf @n

-- | The number of elements in an array of this shape
sizeShape :: (Num i, KnownNat n) => Shape n i -> i
sizeShape ZS = 1
sizeShape (n :$ sh) = n * sizeShape sh

flattenShape :: (Num i, KnownNat n) => Shape n i -> Shape 1 i
flattenShape = singletonShape . sizeShape

backpermutePrefixShape :: forall n i. KnownNat n
                       => Permutation -> Shape n i -> Shape n i
backpermutePrefixShape p (Shape is) = Shape $ backpermutePrefixSized p is

-- Warning: do not pass a list of strides to this function.
listShapeToShape :: KnownNat n => [i] -> Shape n i
listShapeToShape = Shape . listToSized

shapeToList :: Shape n i -> [i]
shapeToList (Shape l) = sizedListToList l


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall m n i j. (Integral i, Num j, KnownNat m, KnownNat n)
            => Shape (m + n) i -> Index m j -> j
toLinearIdx = \sh idx -> go sh idx 0
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: (KnownNat m1, KnownNat n1)
       => Shape (m1 + n1) i -> Index m1 j -> j -> j
    go sh ZI tensidx = fromIntegral (sizeShape sh) * tensidx
    go (n :$ sh) (i :. idx) tensidx = go sh idx (fromIntegral n * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdx :: forall n i j. (Integral i, Integral j, KnownNat n)
              => Shape n i -> j -> Index n j
fromLinearIdx = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: KnownNat n1 => Shape n1 i -> j -> (j, Index n1 j)
    go ZS n = (n, ZI)
    go (0 :$ sh) _ =
      (0, 0 :. zeroOf sh)
    go (n :$ sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` fromIntegral n
      in (tensLin', i :. idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: (Num j, KnownNat n) => Shape n i -> Index n j
zeroOf ZS = ZI
zeroOf (_ :$ sh) = 0 :. zeroOf sh
