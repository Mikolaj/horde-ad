{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | @[Nat]@-indexed lists.
module HordeAd.Core.ShapedList
  ( ShapedList(..)
  , snocSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  , backpermutePrefixSized, permutePrefixSized, backpermutePrefixList
  , unsnocSized1, lastSized, initSized, zipSized, zipWith_Sized, reverseSized
  , sizedListCompare, listToSized, sizedListToList
  , Permutation
  , fromLinearIdx
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.Exts (IsList (..))
import           GHC.TypeLits (KnownNat, Nat, SomeNat (..), someNatVal)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Internal.SizedList (Permutation)

-- | Strict lists indexed by shapes, that is, lists of the GHC @Nat@.
infixr 3 :$:
data ShapedList (sh :: [Nat]) i where
  ZSH :: ShapedList '[] i
  (:$:) :: (KnownNat n, OS.Shape sh)
        => i -> ShapedList sh i -> ShapedList (n ': sh) i

deriving instance Eq i => Eq (ShapedList sh i)

deriving instance Ord i => Ord (ShapedList sh i)

-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (ShapedList sh i) where
  showsPrec d l = showsPrec d (sizedListToList l)

deriving stock instance Functor (ShapedList sh)

instance Foldable (ShapedList sh) where
  foldr f z l = foldr f z (sizedListToList l)

instance OS.Shape sh => IsList (ShapedList sh i) where
  type Item (ShapedList sh i) = i
  fromList = listToSized
  toList = sizedListToList

snocSized :: KnownNat n => ShapedList sh i -> i -> ShapedList (n ': sh) i
snocSized ZSH last1 = last1 :$: ZSH
snocSized (i :$: ix) last1 = i :$: snocSized ix last1

appendSized :: OS.Shape (sh2 OS.++ sh)
            => ShapedList sh2 i -> ShapedList sh i
            -> ShapedList (sh2 OS.++ sh) i
appendSized l1 l2 = listToSized $ sizedListToList l1 ++ sizedListToList l2

headSized :: ShapedList (n ': sh) i -> i
headSized (i :$: _ix) = i

tailSized :: ShapedList (n ': sh) i -> ShapedList sh i
tailSized (_i :$: ix) = ix

takeSized :: forall len sh i. (KnownNat len, OS.Shape (OS.Take len sh))
          => ShapedList sh i -> ShapedList (OS.Take len sh) i
takeSized ix = listToSized $ take (valueOf @len) $ sizedListToList ix

dropSized :: forall len sh i. (KnownNat len, OS.Shape (OS.Drop len sh))
          => ShapedList sh i -> ShapedList  (OS.Drop len sh) i
dropSized ix = listToSized $ drop (valueOf @len) $ sizedListToList ix

splitAt_Sized
  :: (KnownNat len, OS.Shape (OS.Drop len sh), OS.Shape (OS.Take len sh))
  => ShapedList sh i
  -> (ShapedList (OS.Take len sh) i, ShapedList (OS.Drop len sh) i)
splitAt_Sized ix = (takeSized ix, dropSized ix)

unsnocSized1 :: ShapedList (n ': sh) i -> (ShapedList sh i, i)
unsnocSized1 (i :$: ix) = case ix of
  ZSH -> (ZSH, i)
  _ :$: _ -> let (init1, last1) = unsnocSized1 ix
             in (i :$: init1, last1)

lastSized :: ShapedList (n ': sh) i -> i
lastSized (i :$: ZSH) = i
lastSized (_i :$: ix@(_ :$: _)) = lastSized ix

initSized :: ShapedList (n ': sh) i -> ShapedList sh i
initSized (_i :$: ZSH) = ZSH
initSized (i :$: ix@(_ :$: _)) = i :$: initSized ix

zipSized :: ShapedList sh i -> ShapedList sh j -> ShapedList sh (i, j)
zipSized ZSH ZSH = ZSH
zipSized (i :$: irest) (j :$: jrest) = (i, j) :$: zipSized irest jrest

zipWith_Sized :: (i -> j -> k) -> ShapedList sh i -> ShapedList sh j
              -> ShapedList sh k
zipWith_Sized _ ZSH ZSH = ZSH
zipWith_Sized f (i :$: irest) (j :$: jrest) =
  f i j :$: zipWith_Sized f irest jrest

reverseSized :: OS.Shape sh => ShapedList sh i -> ShapedList sh i
reverseSized = listToSized . reverse . sizedListToList

-- This permutes a prefix of the sized list of the length of the permutation.
-- The rest of the sized list is left intact.
backpermutePrefixSized :: forall sh i. (OS.Shape sh, KnownNat (OS.Rank sh))
                       => Permutation -> ShapedList sh i -> ShapedList sh i
backpermutePrefixSized p ix =
  if valueOf @(OS.Rank sh) < length p
  then error "backpermutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ backpermutePrefixList p $ sizedListToList ix

backpermutePrefixList :: Permutation -> [i] -> [i]
backpermutePrefixList p l = map (l !!) p ++ drop (length p) l

permutePrefixSized :: forall sh i. (OS.Shape sh, KnownNat (OS.Rank sh))
                   => Permutation -> ShapedList sh i -> ShapedList sh i
permutePrefixSized p ix =
  if valueOf @(OS.Rank sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ permutePrefixList p $ sizedListToList ix

-- Boxed vector is not that bad, because we move pointers around,
-- but don't follow them. Storable vectors wouldn't work for Ast.
permutePrefixList :: Permutation -> [i] -> [i]
permutePrefixList p l = V.toList $ Data.Vector.fromList l V.// zip p l

-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedListCompare :: Monoid m
                 => (i -> i -> m) -> ShapedList sh i -> ShapedList sh i -> m
sizedListCompare _ ZSH ZSH = mempty
sizedListCompare f (i :$: idx) (j :$: idx') =
  f i j <> sizedListCompare f idx idx'

-- We avoid @KnownNat (OS.Rank sh)@ constraint (that would propagate
-- to countless other functions) by performing runtime checks
-- not using types but using methods of class @OS.Shape@.
-- This forces us to use @unsafeCoerce@, but we'd need it anyway,
-- unless we started using proper singletons or something similar.
listToSized :: forall sh i. OS.Shape sh
            => [i] -> ShapedList sh i
listToSized [] = case OS.shapeT @sh of
  [] -> unsafeCoerce ZSH
  _ -> error $ "listToSized: input list too short; missing "
               ++ show (OS.sizeT @sh :: Int)
listToSized (i : is) = case OS.shapeT @sh of
  [] -> error $ "listToSized: input list too long; spurious "
                ++ show (length (i : is))
  n : rest -> OS.withShapeP rest $ \(_proxy :: Proxy rest) ->
    case someNatVal $ toInteger n of
      Just (SomeNat (_proxyN :: Proxy n)) ->
        -- rest ~ OS.Drop 1 sh
        let sh = listToSized @rest is
        in gcastWith (unsafeCoerce Refl :: sh :~: n ': rest)
           $ i :$: sh
      Nothing -> error "listToSized: impossible someNatVal error"

sizedListToList :: ShapedList sh i -> [i]
sizedListToList ZSH = []
sizedListToList (i :$: is) = i : sizedListToList is

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdx :: forall sh i j. (Integral i, Integral j)
              => ShapedList sh i -> j -> ShapedList sh j
fromLinearIdx = \sh lin -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: ShapedList sh1 i -> j -> (j, ShapedList sh1 j)
    go ZSH n = (n, ZSH)
    go (0 :$: sh) _ =
      (0, 0 :$: zeroOf sh)
    go (n :$: sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` fromIntegral n
      in (tensLin', i :$: idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => ShapedList sh i -> ShapedList sh j
zeroOf ZSH = ZSH
zeroOf (_ :$: sh) = 0 :$: zeroOf sh
