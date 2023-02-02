{-# LANGUAGE ConstraintKinds, DataKinds, DeriveFunctor, DerivingStrategies,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, RankNTypes, StandaloneDeriving,
             TypeFamilyDependencies, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Internal.SizedIndex
  ( -- * Concrete type synonyms to be used in many other modules
    IndexInt, ShapeInt,  Permutation
    -- * GHC.Nat-indexed lists as array indexes, with operations
  , Index(..)
  , singletonIndex, headIndex, tailIndex, takeIndex, dropIndex
  , idxCompare , listToIndex, indexToList
    -- * Shapes as fully encapsulated indexes, with operations
  , Shape, pattern (:$), pattern ZS
  , singletonShape, tailShape, takeShape, dropShape, permutePrefixShape
  , shapeSize, flattenShape
  , listShapeToShape, shapeToList
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx, zeroOf
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Concrete type synonyms to be used in many other modules

type IndexInt n = Index n Int

type ShapeInt n = Shape n Int

type Permutation = [Int]


-- * GHC.Nat-indexed lists as array indexes, with operations

-- | An index in an n-dimensional array. The slowest-moving index is at the
-- head position; thus the index 'i :. j :. Z' represents 'a[i][j]' in
-- traditional C notation.
--
-- Strongly Worded Warning: the implementation of this datatype should never
-- be changed, even by adding a constraint or making a field strict or packed.
-- Otherwise the multiple @unsafeCoerce@ below won't work any more,
-- because they depend on the runtime representation of the datatype
-- being identical to the representation of ordinary lists.
-- Note that changes in GHC or base library may similarly break this code,
-- though there should be ample advance warning, given that many
-- programs depend on this coincidence.
infixr 3 :.
data Index (n :: Nat) i where
  Z :: Index 0 i
  (:.) :: i -> Index n i -> Index (1 + n) i

deriving stock instance Functor (Index n)

instance Show i => Show (Index n i) where
  showsPrec _ Z = showString "Z"
  showsPrec d (i :. ix) = showParen (d > 3) $
    showsPrec 4 i . showString " :. " . showsPrec 3 ix

singletonIndex :: i -> Index 1 i
singletonIndex i = i :. Z

headIndex :: Index (1 + n) i -> i
headIndex Z = error "headIndex: impossible pattern needlessly required"
headIndex (i :. _ix) = i

tailIndex :: Index (1 + n) i -> Index n i
tailIndex Z = error "tailIndex: impossible pattern needlessly required"
tailIndex (_i :. ix) = ix

takeIndex :: forall len n i. KnownNat len
          => Index (len + n) i -> Index n i
takeIndex ix = unsafeCoerce $ take (valueOf @len) $ unsafeCoerce ix

dropIndex :: forall len n i. KnownNat len
          => Index (len + n) i -> Index n i
dropIndex ix = unsafeCoerce $ drop (valueOf @len) $ unsafeCoerce ix

-- This permutes a prefix of the index of the length of the permutation.
-- The rest of the index is left intact.
permutePrefixIndex :: forall n. KnownNat n
                   => Permutation -> Index n Int -> Index n Int
permutePrefixIndex p ix =
  if valueOf @n < length p
  then error "permutePrefixIndex: cannot permute index, because it's too short"
  else let l = unsafeCoerce ix
       in (unsafeCoerce :: [Int] -> Index n Int)
          $ V.toList $ VS.fromList l V.// zip p l

-- | Pairwise comparison of two index values. The comparison function is invoked
-- once for each rank on the corresponding pair of indices.
idxCompare :: Monoid m => (i -> i -> m) -> Index n i -> Index n i -> m
idxCompare _ Z Z = mempty
idxCompare f (i :. idx) (j :. idx') = f i j <> idxCompare f idx idx'
idxCompare _ _ _ = error "idxCompare: impossible pattern needlessly required"

{-
-- Look Ma, no unsafeCoerce! But it compiles only with GHC >= 9.2,
-- so let's switch to it once we stop using 8.10 and 9.0.
listToIndex :: forall n. KnownNat n => [Int] -> Index n Int
listToIndex []
  | Just Refl <- sameNat (Proxy @n) (Proxy @0) = Z
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

listToIndex :: forall n i. KnownNat n => [i] -> Index n i
listToIndex list
  | length list == valueOf @n
  = go list unsafeCoerce
  | otherwise
  = error "listToIndex: list length disagrees with context"
  where
    go :: [i] -> (forall m. Index m i -> r) -> r
    go [] k = k Z
    go (i : rest) k = go rest (\rest' -> k (i :. rest'))

indexToList :: Index n i -> [i]
indexToList = unsafeCoerce


-- * Shapes as fully encapsulated indexes, with operations

-- | The shape of an n-dimensional array. Represented by an index to not
-- duplicate representations and convert easily between each. It seems unlikely
-- enough to make mistakes even with this dumb wrapper, so it might be fine.
newtype Shape n i = Shape (Index n i)
  deriving (Show)

-- NO IDEA why @() =>@ is required, but typing of Ast fails without it.
pattern ZS :: forall n i. () => n ~ 0 => Shape n i
pattern ZS = Shape Z

infixr 3 :$
pattern (:$) :: forall n1 i. forall n. (1 + n) ~ n1
             => i -> Shape n i -> Shape n1 i
pattern i :$ sh <- (unconsShape -> Just (UnconsShapeRes sh i Dict))
  where i :$ (Shape sh) = Shape (i :. sh)
{-# COMPLETE ZS, (:$) #-}

data Dict c where
  Dict :: c => Dict c
data UnconsShapeRes i n1 =
  forall n. UnconsShapeRes (Shape n i) i (Dict (n1 ~ (1 + n)))
unconsShape :: Shape n1 i -> Maybe (UnconsShapeRes i n1)
unconsShape (Shape sh) = case sh of
  i :. sh' -> Just (UnconsShapeRes (Shape sh') i Dict)
  Z -> Nothing

singletonShape :: i -> Shape 1 i
singletonShape = Shape . singletonIndex

tailShape :: Shape (1 + n) i -> Shape n i
tailShape (Shape ix) = Shape $ tailIndex ix

takeShape :: forall len n i. KnownNat len
          => Shape (len + n) i -> Shape n i
takeShape (Shape ix) = Shape $ takeIndex ix

dropShape :: forall len n i. KnownNat len
          => Shape (len + n) i -> Shape n i
dropShape (Shape ix) = Shape $ dropIndex ix

permutePrefixShape :: KnownNat n => Permutation -> Shape n Int -> Shape n Int
permutePrefixShape p (Shape ix) = Shape $ permutePrefixIndex p ix

-- | The number of elements in an array of this shape
shapeSize :: Num i => Shape n i -> i
shapeSize ZS = 1
shapeSize (n :$ sh) = n * shapeSize sh

flattenShape :: Num i => Shape n i -> Shape 1 i
flattenShape = singletonShape . shapeSize

-- Warning: do not pass a list of strides to this function.
listShapeToShape :: forall n i. KnownNat n => [i] -> Shape n i
listShapeToShape = Shape . listToIndex

shapeToList :: Shape n i -> [i]
shapeToList (Shape l) = indexToList l


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer
toLinearIdx :: Num i => Shape n i -> Index n i -> i
toLinearIdx = \sh idx -> snd (go sh idx)
  where
    -- Returns (shape size, linear index)
    go :: Num i => Shape n i -> Index n i -> (i, i)
    go (Shape Z) Z = (1, 0)
    go (Shape (n :. sh)) (i :. idx) =
      let (restsize, lin) = go (Shape sh) idx
      in (n * restsize, i * restsize + lin)
    go _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index
fromLinearIdx :: Integral i => Shape n i -> i -> Index n i
fromLinearIdx = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: Integral i => Shape n i -> i -> (i, Index n i)
    go (Shape Z) n = (n, Z)
    go (Shape (n :. sh)) lin =
      let (tensLin, idxInTens) = go (Shape sh) lin
          (tensLin', i) = tensLin `quotRem` n
      in (tensLin', i :. idxInTens)

-- | The zero index in this shape (not dependent on the actual integers)
zeroOf :: Num i => Shape n i -> Index n i
zeroOf (Shape Z) = Z
zeroOf (Shape (_ :. sh)) = 0 :. zeroOf (Shape sh)
