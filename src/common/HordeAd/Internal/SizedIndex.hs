{-# LANGUAGE ConstraintKinds, DataKinds, DeriveFunctor, DerivingStrategies,
             FlexibleInstances, GADTs, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, RankNTypes, StandaloneDeriving,
             TypeFamilyDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Internal.SizedIndex
  ( IndexInt, ShapeInt,  Permutation
  , Index(Z), pattern (:.)
  , tailIndex, takeIndex, dropIndex
  , Shape(..)
  , singletonShape, (@$), tailShape, takeShape, dropShape, permutePrefixShape
  , shapeSize, toLinearIdx, fromLinearIdx, zeroOf, idxCompare
  , listShapeToIndex
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Text.Show.Functions ()
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- Concrete type synonyms to be used in many other modules

type IndexInt n = Index n Int

type ShapeInt n = Shape n Int

type Permutation = [Int]


-- * GHC.Nat-indexed lists as indexes and shapes, originally by Tom Smeding

-- | An index in an n-dimensional array. The fastest-moving index is at the
-- last position; thus the index 'Z :. i :. j' represents 'a[i][j]' in
-- traditional C notation.
data Index (n :: Nat) i where
  Z :: Index 0 i
  S :: i -> Index n i -> Index (1 + n) i

deriving stock instance Functor (Index n)

instance Show i => Show (Index n i) where
  showsPrec _ Z = showString "Z"
  showsPrec d (idx :. i) = showParen (d > 3) $
    showsPrec 3 idx . showString " :. " . showsPrec 4 i

-- I'm afraid, I can't do the unsafeCoerces below with this order
-- of argument in :., can I? So I need this instead:
pattern (:.) :: forall n1 i. forall n. n1 ~ (1 + n)
             => Index n i -> i -> Index n1 i
pattern (:.) is i = S i is
{-# COMPLETE Z, (:.) #-}
infixl 3 :.
-- This fixity is stolen from Accelerate:
--   https://hackage.haskell.org/package/accelerate-1.3.0.0/docs/Data-Array-Accelerate.html#t::.

tailIndex :: Index (1 + n) i -> Index n i
tailIndex Z = error "tailIndex: impossible pattern needlessly required"
tailIndex (is :. _i) = is

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

-- | The shape of an n-dimensional array. Represented by an index to not
-- duplicate representations and convert easily between each. It seems unlikely
-- enough to make mistakes even with this dumb wrapper, so it might be fine.
newtype Shape n i = Shape (Index n i)
  deriving Show

-- It seems that function names can't start with colon. That's too bad.
-- Also, I can't make pattern synonym of out that because newtype is in the way.
-- Or can I if I defined two pattern synonyms?
infixl 3 @$
(@$) :: Shape n i -> i -> Shape (1 + n) i
Shape sh @$ s = Shape (sh :. s)

singletonShape :: i -> Shape 1 i
singletonShape i = Shape $ Z :. i

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
shapeSize :: Shape n Int -> Int
shapeSize (Shape Z) = 1
shapeSize (Shape (sh :. i)) = shapeSize (Shape sh) * i

toLinearIdx :: Shape n Int -> Index n Int -> Int
toLinearIdx (Shape Z) Z = 0
toLinearIdx (Shape (sh :. n)) (idx :. i) = n * toLinearIdx (Shape sh) idx + i
toLinearIdx _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index
fromLinearIdx :: Integral i => Shape n i -> i -> Index n i
fromLinearIdx (Shape Z) 0 = Z
fromLinearIdx (Shape Z) _ = error "Index out of range"
fromLinearIdx (Shape (sh :. n)) idx =
  let (idx', i) = idx `quotRem` n
  in fromLinearIdx (Shape sh) idx' :. i

-- | The zero index in this shape (not dependent on the actual integers)
zeroOf :: Num i => Shape n i -> Index n i
zeroOf (Shape Z) = Z
zeroOf (Shape (sh :. _)) = zeroOf (Shape sh) :. 0

-- | Pairwise comparison of two index values. The comparison function is invoked
-- once for each rank on the corresponding pair of indices.
idxCompare :: Monoid m => (Int -> Int -> m) -> Index n Int -> Index n Int -> m
idxCompare _ Z Z = mempty
idxCompare f (idx :. i) (idx' :. j) = f i j <> idxCompare f idx idx'
idxCompare _ _ _ = error "idxCompare: impossible pattern needlessly required"

-- Warning: do not pass a list of strides to this function.
listShapeToIndex :: forall n i. KnownNat n => [i] -> Shape n i
listShapeToIndex list
  | length list == valueOf @n
  = go list (Shape . unsafeCoerce)
  | otherwise
  = error "listShapeToIndex: list length disagrees with context"
  where
    go :: [i] -> (forall m. Index m i -> r) -> r
    go [] k = k Z
    go (i : rest) k = go rest (\rest' -> k (rest' :. i))
