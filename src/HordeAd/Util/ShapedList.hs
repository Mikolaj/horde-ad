{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | @[Nat]@-indexed lists to be used as is for lists of tensor variables,
-- tensor shapes and tensor indexes.
module HordeAd.Util.ShapedList
  ( -- * Shaped lists (sized, where size is shape) and their permutations
    SizedListS(..)
  , consShaped, unconsContShaped
  , singletonSized, snocSized, appendSized
  , headSized, tailSized, takeSized, dropSized, splitAt_Sized
  , unsnocSized1, lastSized, initSized, zipSized, zipWith_Sized, reverseSized
  , Permutation  -- ^ re-exported from "SizedList"
  , backpermutePrefixShaped, backpermutePrefixSized
  , permutePrefixShaped, permutePrefixSized
  , sizedCompare, listToSized, sizedToList
  , shapedToSized, shapedToIndex
    -- * Tensor indexes as fully encapsulated sized lists, with operations
  , IndexS
  -- * Tensor shapes as fully encapsulated sized lists, with operations
  , ShapedNat, shapedNat, unShapedNat
  , ShapeS, ShapeIntS, shapeIntSFromT
    -- * Operations involving both indexes and shapes
  , toLinearIdx, fromLinearIdx
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           GHC.Exts (IsList (..))
import           GHC.TypeLits
  (KnownNat, Nat, SomeNat (..), someNatVal, type (*))
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Util.SizedList (Permutation)
import qualified HordeAd.Util.SizedList as SizedList

-- * Shaped lists and their permutations

-- | Strict lists indexed by shapes, that is, lists of the GHC @Nat@.
infixr 3 ::$
type role SizedListS nominal representational
data SizedListS (sh :: [Nat]) i where
  ZS :: SizedListS '[] i
  (::$) :: (KnownNat n, Sh.Shape sh)
        => i -> SizedListS sh i -> SizedListS (n ': sh) i

deriving instance Eq i => Eq (SizedListS sh i)

deriving instance Ord i => Ord (SizedListS sh i)

-- This is only lawful when OverloadedLists is enabled.
-- However, it's much more readable when tracing and debugging.
instance Show i => Show (SizedListS sh i) where
  showsPrec d l = showsPrec d (sizedToList l)

deriving stock instance Functor (SizedListS sh)

instance Foldable (SizedListS sh) where
  foldr f z l = foldr f z (sizedToList l)

instance Sh.Shape sh => IsList (SizedListS sh i) where
  type Item (SizedListS sh i) = i
  fromList = listToSized
  toList = sizedToList

-- TODO: should we actually replace ::$ with that in the external API?
consShaped :: (KnownNat n, Sh.Shape sh)
           => ShapedNat n i -> SizedListS sh i -> SizedListS (n ': sh) i
consShaped (ShapedNat i) l = i ::$ l

unconsContShaped :: (ShapedNat n i -> k) -> SizedListS (n ': sh) i -> k
unconsContShaped f (i ::$ _) = f (ShapedNat i)

singletonSized :: KnownNat n => i -> SizedListS '[n] i
singletonSized i = i ::$ ZS

snocSized :: KnownNat n => SizedListS sh i -> i -> SizedListS (n ': sh) i
snocSized ZS last1 = last1 ::$ ZS
snocSized (i ::$ ix) last1 = i ::$ snocSized ix last1

appendSized :: Sh.Shape (sh2 Sh.++ sh)
            => SizedListS sh2 i -> SizedListS sh i
            -> SizedListS (sh2 Sh.++ sh) i
appendSized l1 l2 = listToSized $ sizedToList l1 ++ sizedToList l2

headSized :: SizedListS (n ': sh) i -> i
headSized (i ::$ _ix) = i

tailSized :: SizedListS (n ': sh) i -> SizedListS sh i
tailSized (_i ::$ ix) = ix

takeSized :: forall len sh i. (KnownNat len, Sh.Shape (Sh.Take len sh))
          => SizedListS sh i -> SizedListS (Sh.Take len sh) i
takeSized ix = listToSized $ take (valueOf @len) $ sizedToList ix

dropSized :: forall len sh i. (KnownNat len, Sh.Shape (Sh.Drop len sh))
          => SizedListS sh i -> SizedListS  (Sh.Drop len sh) i
dropSized ix = listToSized $ drop (valueOf @len) $ sizedToList ix

splitAt_Sized
  :: (KnownNat len, Sh.Shape (Sh.Drop len sh), Sh.Shape (Sh.Take len sh))
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

reverseSized :: Sh.Shape sh => SizedListS sh i -> SizedListS sh i
reverseSized = listToSized . reverse . sizedToList

backpermutePrefixShaped
  :: forall perm sh i.
     (Sh.Shape perm, Sh.Shape sh, Sh.Shape (Sh.Permute perm sh))
  => SizedListS sh i -> SizedListS (Sh.Permute perm sh) i
backpermutePrefixShaped ix =
  if length (Sh.shapeT @sh) < length (Sh.shapeT @perm)
  then error "backpermutePrefixShaped: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.backpermutePrefixList (Sh.shapeT @perm)
                   $ sizedToList ix

-- This permutes a prefix of the sized list of the length of the permutation.
-- The rest of the sized list is left intact.
backpermutePrefixSized :: forall sh sh2 i. (Sh.Shape sh, Sh.Shape sh2)
                       => Permutation -> SizedListS sh i -> SizedListS sh2 i
backpermutePrefixSized p ix =
  if length (Sh.shapeT @sh) < length p
  then error "backpermutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.backpermutePrefixList p $ sizedToList ix

permutePrefixShaped
  :: forall perm sh i. (Sh.Shape perm, Sh.Shape sh)
  => SizedListS (Sh.Permute perm sh) i -> SizedListS sh i
permutePrefixShaped ix =
  if length (Sh.shapeT @sh) < length (Sh.shapeT @perm)
  then error "permutePrefixShaped: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList (Sh.shapeT @perm)
                   $ sizedToList ix

permutePrefixSized :: forall sh sh2 i. (Sh.Shape sh, Sh.Shape sh2)
                   => Permutation -> SizedListS sh i -> SizedListS sh2 i
permutePrefixSized p ix =
  if length (Sh.shapeT @sh) < length p
  then error "permutePrefixSized: cannot permute a list shorter than permutation"
  else listToSized $ SizedList.permutePrefixList p $ sizedToList ix

-- | Pairwise comparison of two sized list values.
-- The comparison function is invoked once for each rank
-- on the corresponding pair of indices.
sizedCompare :: Monoid m
                 => (i -> i -> m) -> SizedListS sh i -> SizedListS sh i -> m
sizedCompare _ ZS ZS = mempty
sizedCompare f (i ::$ idx) (j ::$ idx') =
  f i j <> sizedCompare f idx idx'

-- We avoid @KnownNat (Sh.Rank sh)@ constraint (that would propagate
-- to countless other functions) by performing runtime checks
-- not using types but using methods of class @Sh.Shape@.
-- This forces us to use @unsafeCoerce@, but we'd need it anyway,
-- unless we started using proper singletons or something similar.
listToSized :: forall sh i. Sh.Shape sh
            => [i] -> SizedListS sh i
listToSized [] = case Sh.shapeT @sh of
  [] -> gcastWith (unsafeCoerce Refl :: sh :~: '[])
        ZS
  _ -> error $ "listToSized: input list too short; missing "
               ++ show (Sh.sizeT @sh :: Int)
listToSized (i : is) = case Sh.shapeT @sh of
  [] -> error $ "listToSized: input list too long; spurious "
                ++ show (length (i : is))
  nInt : restList -> Sh.withShapeP restList $ \(Proxy @rest) ->
    case someNatVal $ toInteger nInt of
      Just (SomeNat (Proxy @n)) ->
        -- rest ~ Sh.Drop 1 sh
        let sh = listToSized @rest is
        in gcastWith (unsafeCoerce Refl :: sh :~: n ': rest)
           $ i ::$ sh
               -- TODO: actually check i < n or wrap a check for later,
               -- based on a mechanism provided by @i@ somehow
      Nothing -> error "listToSized: impossible someNatVal error"

sizedToList :: SizedListS sh i -> [i]
sizedToList ZS = []
sizedToList (i ::$ is) = i : sizedToList is

shapedToSized :: KnownNat (Sh.Rank sh)
                  => SizedListS sh i -> SizedList.SizedList (Sh.Rank sh) i
shapedToSized = SizedList.listToSized . sizedToList

shapedToIndex :: KnownNat (Sh.Rank sh)
                  => SizedListS sh i -> SizedList.Index (Sh.Rank sh) i
shapedToIndex = SizedList.listToIndex . sizedToList


-- * Tensor indexes as fully encapsulated sized lists, with operations

type IndexS = SizedListS


-- * Tensor shapes as fully encapsulated sized lists, with operations

type ShapeS = SizedListS

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type role ShapedNat nominal representational
newtype ShapedNat (n :: Nat) a = ShapedNat {unShapedNat :: a}

-- TODO: actually check or wrap a check for later, based on a mechanism
-- provided by @a@ somehow
shapedNat :: forall n a. a -> ShapedNat n a
shapedNat = ShapedNat

-- TODO: ensure this can't be subverted:
-- | These are singletons. The integers inside are equal to the type-level
-- dimensions.
type ShapeIntS (sh :: [Nat]) = ShapeS sh Int

shapeIntSFromT :: forall sh. Sh.Shape sh => ShapeIntS sh
shapeIntSFromT = listToSized $ Sh.shapeT @sh


-- * Operations involving both indexes and shapes

-- | Given a multidimensional index, get the corresponding linear
-- index into the buffer. Note that the index doesn't need to be pointing
-- at a scalar. It may point at the start of a larger tensor instead.
--
-- If any of the dimensions is 0 or if rank is 0, the result will be 0,
-- which is fine, that's pointing at the start of the empty buffer.
-- Note that the resulting 0 may be a complex term.
toLinearIdx :: forall sh1 sh2 i j. (Sh.Shape sh2, Integral i, Num j)
            => SizedListS (sh1 Sh.++ sh2) i -> SizedListS sh1 j
            -> ShapedNat (Sh.Size sh1 * Sh.Size sh2) j
toLinearIdx = \sh idx -> shapedNat $ go sh idx 0
  where
    -- Additional argument: index, in the @m - m1@ dimensional array so far,
    -- of the @m - m1 + n@ dimensional tensor pointed to by the current
    -- @m - m1@ dimensional index prefix.
    go :: forall sh3.
          SizedListS (sh3 Sh.++ sh2) i -> SizedListS sh3 j -> j -> j
    go _sh ZS tensidx = fromIntegral (Sh.sizeT @(sh3 Sh.++ sh2)) * tensidx
    go (n ::$ sh) (i ::$ idx) tensidx = go sh idx (fromIntegral n * tensidx + i)
    go _ _ _ = error "toLinearIdx: impossible pattern needlessly required"

-- | Given a linear index into the buffer, get the corresponding
-- multidimensional index. Here we require an index pointing at a scalar.
--
-- If any of the dimensions is 0, the linear index has to be 0
-- (which we can't assert, because j may be a term and so == lies)
-- and a fake index with correct length but lots of zeroes is produced,
-- because it doesn't matter, because it's going to point at the start
-- of the empty buffer anyway.
fromLinearIdx :: forall sh i j. (Integral i, Integral j)
              => SizedListS sh i -> ShapedNat (Sh.Size sh) j -> SizedListS sh j
fromLinearIdx = \sh (ShapedNat lin) -> snd (go sh lin)
  where
    -- Returns (linear index into array of sub-tensors,
    -- multi-index within sub-tensor).
    go :: SizedListS sh1 i -> j -> (j, SizedListS sh1 j)
    go ZS n = (n, ZS)
    go (0 ::$ sh) _ =
      (0, 0 ::$ zeroOf sh)
    go (n ::$ sh) lin =
      let (tensLin, idxInTens) = go sh lin
          (tensLin', i) = tensLin `quotRem` fromIntegral n
      in (tensLin', i ::$ idxInTens)

-- | The zero index in this shape (not dependent on the actual integers).
zeroOf :: Num j => SizedListS sh i -> SizedListS sh j
zeroOf ZS = ZS
zeroOf (_ ::$ sh) = 0 ::$ zeroOf sh
