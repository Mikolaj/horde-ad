{-# LANGUAGE ConstraintKinds, DataKinds, DeriveFunctor, DerivingStrategies,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, RankNTypes, StandaloneDeriving,
             TypeFamilyDependencies, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Sized indexes and shapes for tensors.
module HordeAd.Core.SizedIndex
  ( -- * Concrete type synonyms to be used in many other modules
    IndexInt, ShapeInt, Permutation
    -- * Tensor indexes as fully encapsulated sized lists, with operations
  , Index, pattern (:.), pattern ZI
  , singletonIndex, snocIndex, appendIndex
  , headIndex, tailIndex, takeIndex, dropIndex, permutePrefixIndex
  , unsnocIndex, lastIndex, initIndex
  , listToIndex, indexToList
    -- * Tensor shapes as fully encapsulated sized lists, with operations
  , Shape, pattern (:$), pattern ZS
  , singletonShape, tailShape, takeShape, dropShape, permutePrefixShape
  , shapeSize, flattenShape
  , listShapeToShape, shapeToList
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx, zeroOf
  ) where

import Prelude

import Control.Arrow (first)
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, type (+))
import Text.Show.Functions ()

import HordeAd.Internal.OrthotopeOrphanInstances ()
import HordeAd.Internal.SizedList

-- * Concrete type synonyms to be used in many other modules

type IndexInt n = Index n Int

type ShapeInt n = Shape n Int


-- * Tensor indexes as fully encapsulated sized lists, with operations

-- | An index in an n-dimensional array represented as a sized list.
-- The slowest-moving index is at the head position;
-- thus the index 'i :. j :. Z' represents 'a[i][j]' in traditional C notation.
newtype Index n i = Index (SizedList n i)
  deriving Show

pattern ZI :: forall n i. () => n ~ 0 => Index n i
pattern ZI = Index Z

infixr 3 :.
pattern (:.) :: forall n1 i. forall n. (1 + n) ~ n1
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

deriving stock instance Functor (Index n)

instance Foldable (Index n) where
  foldr f z l = foldr f z (indexToList l)

instance KnownNat n => IsList (Index n i) where
  type Item (Index n i) = i
  fromList = listToIndex
  toList = indexToList

singletonIndex :: i -> Index 1 i
singletonIndex = Index . singletonSized

snocIndex :: Index n i -> i -> Index (1 + n) i
snocIndex (Index ix) i = Index $ snocSized ix i

appendIndex :: Index m i -> Index n i -> Index (m + n) i
appendIndex (Index ix1) (Index ix2) = Index $ appendSized ix1 ix2

headIndex :: Index (1 + n) i -> i
headIndex (Index ix) = headSized ix

tailIndex :: Index (1 + n) i -> Index n i
tailIndex (Index ix) = Index $ tailSized ix

takeIndex :: forall m n i. KnownNat m
          => Index (m + n) i -> Index m i
takeIndex (Index ix) = Index $ takeSized ix

dropIndex :: forall m n i. KnownNat m
          => Index (m + n) i -> Index n i
dropIndex (Index ix) = Index $ dropSized ix

unsnocIndex :: Index (1 + n) i -> (Index n i, i)
unsnocIndex (Index ix) = first Index $ unsnocSized ix

lastIndex :: Index (1 + n) i -> i
lastIndex (Index ix) = lastSized ix

initIndex :: Index (1 + n) i -> Index n i
initIndex (Index ix) = Index $ initSized ix

permutePrefixIndex :: forall n i. KnownNat n
                   => Permutation -> Index n i -> Index n i
permutePrefixIndex p (Index ix) = Index $ permutePrefixSized p ix

{-
-- Look Ma, no unsafeCoerce! But it compiles only with GHC >= 9.2,
-- so let's switch to it once we stop using 8.10 and 9.0.
listToIndex :: forall n. KnownNat n => [Int] -> Index n Int
listToIndex []
  | Just Refl <- sameNat (Proxy @n) (Proxy @0) = ZI
  | otherwise = error "listToIndex: list too short"
listToIndex (i : is)
  -- What we really need here to make the types check out is a <= check.
  | EQI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToIndex @(n - 1) is
      in i :. sh
  | LTI <- cmpNat (Proxy @1) (Proxy @n) =
      let sh = listToIndexProxy @(n - 1) is
      in i :. sh
  | otherwise =
      error "listToIndex: list too long"
-}

listToIndex :: KnownNat n => [i] -> Index n i
listToIndex = Index . listToSized

indexToList :: Index n i -> [i]
indexToList (Index l) = sizedListToList l


-- * Tensor shapes as fully encapsulated sized lists, with operations

-- | The shape of an n-dimensional array represented as a sized list.
-- The order of dimensions corresponds to that in @Index@.
newtype Shape n i = Shape (SizedList n i)
  deriving Show

pattern ZS :: forall n i. () => n ~ 0 => Shape n i
pattern ZS = Shape Z

infixr 3 :$
pattern (:$) :: forall n1 i. forall n. (1 + n) ~ n1
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

deriving stock instance Functor (Shape n)

instance Foldable (Shape n) where
  foldr f z l = foldr f z (shapeToList l)

instance KnownNat n => IsList (Shape n i) where
  type Item (Shape n i) = i
  fromList = listShapeToShape
  toList = shapeToList

singletonShape :: i -> Shape 1 i
singletonShape = Shape . singletonSized

tailShape :: Shape (1 + n) i -> Shape n i
tailShape (Shape ix) = Shape $ tailSized ix

takeShape :: forall m n i. KnownNat m
          => Shape (m + n) i -> Shape m i
takeShape (Shape ix) = Shape $ takeSized ix

dropShape :: forall m n i. KnownNat m
          => Shape (m + n) i -> Shape n i
dropShape (Shape ix) = Shape $ dropSized ix

permutePrefixShape :: forall n i. KnownNat n
                   => Permutation -> Shape n i -> Shape n i
permutePrefixShape p (Shape ix) = Shape $ permutePrefixSized p ix

-- | The number of elements in an array of this shape
shapeSize :: Num i => Shape n i -> i
shapeSize ZS = 1
shapeSize (n :$ sh) = n * shapeSize sh

flattenShape :: Num i => Shape n i -> Shape 1 i
flattenShape = singletonShape . shapeSize

-- Warning: do not pass a list of strides to this function.
listShapeToShape :: KnownNat n => [i] -> Shape n i
listShapeToShape = Shape . listToSized

shapeToList :: Shape n i -> [i]
shapeToList (Shape l) = sizedListToList l


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
toLinearIdx :: forall m n i. Num i => Shape (m + n) i -> Index m i -> i
toLinearIdx = \sh idx -> snd (go sh idx)
  where
    -- Returns (shape size, linear index)
    go :: forall m1 n1. Shape (m1 + n1) i -> Index m1 i -> (i, i)
    go sh ZI = (shapeSize sh, 0)
    go (n :$ sh) (i :. idx) =
      let (restsize, lin) = go sh idx
      in (n * restsize, i * restsize + lin)
    go _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
fromLinearIdx :: Integral i => Shape n i -> i -> Index n i
fromLinearIdx = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: Integral i => Shape n i -> i -> (i, Index n i)
    go ZS n = (n, ZI)
    go (n :$ sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` n
      in (tensLin', i :. idxInTens)

-- | The zero index in this shape (not dependent on the actual integers)
zeroOf :: Num i => Shape n i -> Index n i
zeroOf ZS = ZI
zeroOf (_ :$ sh) = 0 :. zeroOf sh
