{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Nested.Mixed where

import Prelude hiding (mconcat)

import Control.DeepSeq (NFData(..))
import Control.Monad (forM_, when)
import Control.Monad.ST
import Data.Array.RankedS qualified as S
import Data.Bifunctor (bimap)
import Data.Coerce
import Data.Foldable (toList)
import Data.Int
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Data.Proxy
import Data.Type.Equality
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Foreign.C.Types (CInt)
import Foreign.Storable (Storable)
import GHC.Float qualified (expm1, log1mexp, log1p, log1pexp)
import GHC.Generics (Generic)
import GHC.TypeLits

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Types
import Data.Array.Strided.Orthotope
import Data.Array.XArray (XArray(..))
import Data.Array.XArray qualified as X
import Data.Bag


-- TODO:
--   sumAllPrim :: (PrimElt a, NumElt a) => Mixed sh a -> a
--   rminIndex1 :: Ranked (n + 1) a -> Ranked n Int
--   gather/scatter-like things (most generally, the higher-order variants: accelerate's backpermute/permute)
--   After benchmarking: matmul and matvec



-- Invariant in the API
-- ====================
--
-- In the underlying XArray, there is some shape for elements of an empty
-- array. For example, for this array:
--
--   arr :: Ranked I3 (Ranked I2 Int, Ranked I1 Float)
--   rshape arr == 0 :.: 0 :.: 0 :.: ZIR
--
-- the two underlying XArrays have a shape, and those shapes might be anything.
-- The invariant is that these element shapes are unobservable in the API.
-- (This is possible because you ought to not be able to get to such an element
-- without indexing out of bounds.)
--
-- Note, though, that the converse situation may arise: the outer array might
-- be nonempty but then the inner arrays might. This is fine, an invariant only
-- applies if the _outer_ array is empty.
--
-- TODO: can we enforce that the elements of an empty (nested) array have
-- all-zero shape?
--   -> no, because mlift and also any kind of internals probing from outsiders


-- Primitive element types
-- =======================
--
-- There are a few primitive element types; arrays containing elements of such
-- type are a newtype over an XArray, which it itself a newtype over a Vector.
-- Unfortunately, the setup of the library requires us to list these primitive
-- element types multiple times; to aid in extending the list, all these lists
-- have been marked with [PRIMITIVE ELEMENT TYPES LIST].
--
-- NOTE: if you add PRIMITIVE types, be sure to also add NumElt and IntElt
-- instances for them!


-- | Wrapper type used as a tag to attach instances on. The instances on arrays
-- of @'Primitive' a@ are more polymorphic than the direct instances for arrays
-- of scalars; this means that if @orthotope@ supports an element type @T@ that
-- this library does not (directly), it may just work if you use an array of
-- @'Primitive' T@ instead.
newtype Primitive a = Primitive a
  deriving (Show)

-- | Element types that are primitive; arrays of these types are just a newtype
-- wrapper over an array.
class (Storable a, Elt a) => PrimElt a where
  fromPrimitive :: Mixed sh (Primitive a) -> Mixed sh a
  toPrimitive :: Mixed sh a -> Mixed sh (Primitive a)

  default fromPrimitive :: Coercible (Mixed sh a) (Mixed sh (Primitive a)) => Mixed sh (Primitive a) -> Mixed sh a
  fromPrimitive = coerce

  default toPrimitive :: Coercible (Mixed sh (Primitive a)) (Mixed sh a) => Mixed sh a -> Mixed sh (Primitive a)
  toPrimitive = coerce

-- [PRIMITIVE ELEMENT TYPES LIST]
instance PrimElt Bool
instance PrimElt Int
instance PrimElt Int64
instance PrimElt Int32
instance PrimElt Int16
instance PrimElt Int8
instance PrimElt CInt
instance PrimElt Float
instance PrimElt Double
instance PrimElt ()


-- | Mixed arrays: some dimensions are size-typed, some are not. Distributes
-- over product-typed elements using a data family so that the full array is
-- always in struct-of-arrays format.
--
-- Built on top of 'XArray' which is built on top of @orthotope@, meaning that
-- dimension permutations (e.g. 'mtranspose') are typically free.
--
-- Many of the methods for working on 'Mixed' arrays come from the 'Elt' type
-- class.
type Mixed :: [Maybe Nat] -> Type -> Type
data family Mixed sh a
-- NOTE: When opening up the Mixed abstraction, you might see dimension sizes
-- that you're not supposed to see. In particular, you might see (nonempty)
-- sizes of the elements of an empty array, which is information that should
-- ostensibly not exist; the full array is still empty.

#ifdef OXAR_DEFAULT_SHOW_INSTANCES
#define ANDSHOW , Show
#else
#define ANDSHOW
#endif

data instance Mixed sh (Primitive a) = M_Primitive !(IShX sh) !(XArray sh a)
  deriving (Eq, Ord, Generic ANDSHOW)

-- [PRIMITIVE ELEMENT TYPES LIST]
newtype instance Mixed sh Bool = M_Bool (Mixed sh (Primitive Bool)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Int = M_Int (Mixed sh (Primitive Int)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Int64 = M_Int64 (Mixed sh (Primitive Int64)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Int32 = M_Int32 (Mixed sh (Primitive Int32)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Int16 = M_Int16 (Mixed sh (Primitive Int16)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Int8 = M_Int8 (Mixed sh (Primitive Int8)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh CInt = M_CInt (Mixed sh (Primitive CInt)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Float = M_Float (Mixed sh (Primitive Float)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh Double = M_Double (Mixed sh (Primitive Double)) deriving (Eq, Ord, Generic ANDSHOW)
newtype instance Mixed sh () = M_Nil (Mixed sh (Primitive ())) deriving (Eq, Ord, Generic ANDSHOW)  -- no content, orthotope optimises this (via Vector)
-- etc.

data instance Mixed sh (a, b) = M_Tup2 !(Mixed sh a) !(Mixed sh b) deriving (Generic)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance (Show (Mixed sh a), Show (Mixed sh b)) => Show (Mixed sh (a, b))
#endif
-- etc., larger tuples (perhaps use generics to allow arbitrary product types)

deriving instance (Eq (Mixed sh a), Eq (Mixed sh b)) => Eq (Mixed sh (a, b))
deriving instance (Ord (Mixed sh a), Ord (Mixed sh b)) => Ord (Mixed sh (a, b))

data instance Mixed sh1 (Mixed sh2 a) = M_Nest !(IShX sh1) !(Mixed (sh1 ++ sh2) a) deriving (Generic)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance (Show (Mixed (sh1 ++ sh2) a)) => Show (Mixed sh1 (Mixed sh2 a))
#endif

deriving instance Eq (Mixed (sh1 ++ sh2) a) => Eq (Mixed sh1 (Mixed sh2 a))
deriving instance Ord (Mixed (sh1 ++ sh2) a) => Ord (Mixed sh1 (Mixed sh2 a))


-- | Internal helper data family mirroring 'Mixed' that consists of mutable
-- vectors instead of 'XArray's.
type MixedVecs :: Type -> [Maybe Nat] -> Type -> Type
data family MixedVecs s sh a

newtype instance MixedVecs s sh (Primitive a) = MV_Primitive (VS.MVector s a)

-- [PRIMITIVE ELEMENT TYPES LIST]
newtype instance MixedVecs s sh Bool = MV_Bool (VS.MVector s Bool)
newtype instance MixedVecs s sh Int = MV_Int (VS.MVector s Int)
newtype instance MixedVecs s sh Int64 = MV_Int64 (VS.MVector s Int64)
newtype instance MixedVecs s sh Int32 = MV_Int32 (VS.MVector s Int32)
newtype instance MixedVecs s sh Int16 = MV_Int16 (VS.MVector s Int16)
newtype instance MixedVecs s sh Int8 = MV_Int8 (VS.MVector s Int8)
newtype instance MixedVecs s sh CInt = MV_CInt (VS.MVector s CInt)
newtype instance MixedVecs s sh Double = MV_Double (VS.MVector s Double)
newtype instance MixedVecs s sh Float = MV_Float (VS.MVector s Float)
newtype instance MixedVecs s sh () = MV_Nil (VS.MVector s ())  -- no content, MVector optimises this
-- etc.

data instance MixedVecs s sh (a, b) = MV_Tup2 !(MixedVecs s sh a) !(MixedVecs s sh b)
-- etc.

data instance MixedVecs s sh1 (Mixed sh2 a) = MV_Nest !(IShX sh2) !(MixedVecs s (sh1 ++ sh2) a)


showsMixedArray :: (Show a, Elt a)
                => String  -- ^ fromList prefix: e.g. @rfromListLinear [2,3]@
                -> String  -- ^ replicate prefix: e.g. @rreplicate [2,3]@
                -> Int -> Mixed sh a -> ShowS
showsMixedArray fromlistPrefix replicatePrefix d arr =
  showParen (d > 10) $
    -- TODO: to avoid ambiguity, we should type-apply the shape to mfromListLinear here
    case mtoListLinear arr of
      hd : _ : _
        | all (all (== 0) . take (shxLength (mshape arr))) (marrayStrides arr) ->
            showString replicatePrefix . showString " " . showsPrec 11 hd
      _ ->
       showString fromlistPrefix . showString " " . shows (mtoListLinear arr)

#ifndef OXAR_DEFAULT_SHOW_INSTANCES
instance (Show a, Elt a) => Show (Mixed sh a) where
  showsPrec d arr =
    let sh = show (shxToList (mshape arr))
    in showsMixedArray ("mfromListLinear " ++ sh) ("mreplicate " ++ sh) d arr
#endif

instance Elt a => NFData (Mixed sh a) where
  rnf = mrnf


{-# INLINE mliftNumElt1 #-}
mliftNumElt1 :: (PrimElt a, PrimElt b)
             => (SNat (Rank sh) -> S.Array (Rank sh) a -> S.Array (Rank sh) b)
             -> Mixed sh a -> Mixed sh b
mliftNumElt1 f (toPrimitive -> M_Primitive sh (XArray arr)) = fromPrimitive $ M_Primitive sh (XArray (f (shxRank sh) arr))

{-# INLINE mliftNumElt2 #-}
mliftNumElt2 :: (PrimElt a, PrimElt b, PrimElt c)
             => (SNat (Rank sh) -> S.Array (Rank sh) a -> S.Array (Rank sh) b -> S.Array (Rank sh) c)
             -> Mixed sh a -> Mixed sh b -> Mixed sh c
mliftNumElt2 f (toPrimitive -> M_Primitive sh1 (XArray arr1)) (toPrimitive -> M_Primitive sh2 (XArray arr2))
  | sh1 == sh2 = fromPrimitive $ M_Primitive sh1 (XArray (f (shxRank sh1) arr1 arr2))
  | otherwise = error $ "Data.Array.Nested: Shapes unequal in elementwise Num operation: " ++ show sh1 ++ " vs " ++ show sh2

instance (NumElt a, PrimElt a) => Num (Mixed sh a) where
  (+) = mliftNumElt2 (liftO2 . numEltAdd)
  (-) = mliftNumElt2 (liftO2 . numEltSub)
  (*) = mliftNumElt2 (liftO2 . numEltMul)
  negate = mliftNumElt1 (liftO1 . numEltNeg)
  abs = mliftNumElt1 (liftO1 . numEltAbs)
  signum = mliftNumElt1 (liftO1 . numEltSignum)
  -- TODO: THIS IS BAD, WE NEED TO REMOVE THIS
  fromInteger = error "Data.Array.Nested.fromInteger: Cannot implement fromInteger, use mreplicatePrim"

instance (FloatElt a, PrimElt a) => Fractional (Mixed sh a) where
  fromRational _ = error "Data.Array.Nested.fromRational: No singletons available, use explicit mreplicatePrim"
  recip = mliftNumElt1 (liftO1 . floatEltRecip)
  (/) = mliftNumElt2 (liftO2 . floatEltDiv)

instance (FloatElt a, PrimElt a) => Floating (Mixed sh a) where
  pi = error "Data.Array.Nested.pi: No singletons available, use explicit mreplicatePrim"
  exp = mliftNumElt1 (liftO1 . floatEltExp)
  log = mliftNumElt1 (liftO1 . floatEltLog)
  sqrt = mliftNumElt1 (liftO1 . floatEltSqrt)

  (**) = mliftNumElt2 (liftO2 . floatEltPow)
  logBase = mliftNumElt2 (liftO2 . floatEltLogbase)

  sin = mliftNumElt1 (liftO1 . floatEltSin)
  cos = mliftNumElt1 (liftO1 . floatEltCos)
  tan = mliftNumElt1 (liftO1 . floatEltTan)
  asin = mliftNumElt1 (liftO1 . floatEltAsin)
  acos = mliftNumElt1 (liftO1 . floatEltAcos)
  atan = mliftNumElt1 (liftO1 . floatEltAtan)
  sinh = mliftNumElt1 (liftO1 . floatEltSinh)
  cosh = mliftNumElt1 (liftO1 . floatEltCosh)
  tanh = mliftNumElt1 (liftO1 . floatEltTanh)
  asinh = mliftNumElt1 (liftO1 . floatEltAsinh)
  acosh = mliftNumElt1 (liftO1 . floatEltAcosh)
  atanh = mliftNumElt1 (liftO1 . floatEltAtanh)
  log1p = mliftNumElt1 (liftO1 . floatEltLog1p)
  expm1 = mliftNumElt1 (liftO1 . floatEltExpm1)
  log1pexp = mliftNumElt1 (liftO1 . floatEltLog1pexp)
  log1mexp = mliftNumElt1 (liftO1 . floatEltLog1mexp)

mquotArray, mremArray :: (IntElt a, PrimElt a) => Mixed sh a -> Mixed sh a -> Mixed sh a
mquotArray = mliftNumElt2 (liftO2 . intEltQuot)
mremArray = mliftNumElt2 (liftO2 . intEltRem)

matan2Array :: (FloatElt a, PrimElt a) => Mixed sh a -> Mixed sh a -> Mixed sh a
matan2Array = mliftNumElt2 (liftO2 . floatEltAtan2)

-- | Allowable element types in a mixed array, and by extension in a 'Ranked' or
-- 'Shaped' array. Note the polymorphic instance for 'Elt' of @'Primitive'
-- a@; see the documentation for 'Primitive' for more details.
class Elt a where
  -- ====== PUBLIC METHODS ====== --

  mshape :: Mixed sh a -> IShX sh
  mindex :: Mixed sh a -> IIxX sh -> a
  mindexPartial :: forall sh sh'. Mixed (sh ++ sh') a -> IIxX sh -> Mixed sh' a
  mscalar :: a -> Mixed '[] a

  -- | See 'mfromListOuter'. If the list does not have the given length, a
  -- runtime error is thrown. 'mfromListPrimSN' is faster if applicable.
  mfromListOuterSN :: forall sh n. SNat n -> NonEmpty (Mixed sh a) -> Mixed (Just n  : sh) a

  mtoListOuter :: Mixed (n : sh) a -> [Mixed sh a]

  -- | Note: this library makes no particular guarantees about the shapes of
  -- arrays "inside" an empty array. With 'mlift', 'mlift2' and 'mliftL' you can see the
  -- full 'XArray' and as such you can distinguish different empty arrays by
  -- the "shapes" of their elements. This information is meaningless, so you
  -- should not use it.
  mlift :: forall sh1 sh2.
           StaticShX sh2
        -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b)
        -> Mixed sh1 a -> Mixed sh2 a

  -- | See the documentation for 'mlift'.
  mlift2 :: forall sh1 sh2 sh3.
            StaticShX sh3
         -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b -> XArray (sh3 ++ sh') b)
         -> Mixed sh1 a -> Mixed sh2 a -> Mixed sh3 a

  -- TODO: mliftL is currently unused.
  -- | All arrays in the input must have equal shapes, including subarrays
  -- inside their elements.
  mliftL :: forall sh1 sh2.
            StaticShX sh2
         -> (forall sh' b. Storable b => StaticShX sh' -> NonEmpty (XArray (sh1 ++ sh') b) -> NonEmpty (XArray (sh2 ++ sh') b))
         -> NonEmpty (Mixed sh1 a) -> NonEmpty (Mixed sh2 a)

  mcastPartial :: forall sh1 sh2 sh'. Rank sh1 ~ Rank sh2
               => StaticShX sh1 -> StaticShX sh2 -> Proxy sh' -> Mixed (sh1 ++ sh') a -> Mixed (sh2 ++ sh') a

  mtranspose :: forall is sh. (IsPermutation is, Rank is <= Rank sh)
             => Perm is -> Mixed sh a -> Mixed (PermutePrefix is sh) a

  -- | All arrays in the input must have equal shapes, including subarrays
  -- inside their elements.
  mconcat :: NonEmpty (Mixed (Nothing : sh) a) -> Mixed (Nothing : sh) a

  mrnf :: Mixed sh a -> ()

  -- ====== PRIVATE METHODS ====== --

  -- | Tree giving the shape of every array component.
  type ShapeTree a

  mshapeTree :: a -> ShapeTree a

  mshapeTreeEq :: Proxy a -> ShapeTree a -> ShapeTree a -> Bool

  mshapeTreeIsEmpty :: Proxy a -> ShapeTree a -> Bool

  mshowShapeTree :: Proxy a -> ShapeTree a -> String

  -- | Returns the stride vector of each underlying component array making up
  -- this mixed array.
  marrayStrides :: Mixed sh a -> Bag [Int]

  -- | Given a linear index and a value, write the value at
  -- that index in the vectors.
  mvecsWriteLinear :: Int -> a -> MixedVecs s sh a -> ST s ()

  -- | Given a linear index and a value, write the value at
  -- that index in the vectors.
  mvecsWritePartialLinear :: Proxy sh -> Int -> Mixed sh' a -> MixedVecs s (sh ++ sh') a -> ST s ()

  -- | Given the shape of this array, finalise the vectors into 'XArray's.
  mvecsFreeze :: IShX sh -> MixedVecs s sh a -> ST s (Mixed sh a)

  -- | 'mvecsFreeze' but without copying the mutable vectors before freezing
  -- them. If the mutable vectors are mutated after this function, referential
  -- transparency is broken.
  mvecsUnsafeFreeze :: IShX sh -> MixedVecs s sh a -> ST s (Mixed sh a)

-- | Element types for which we have evidence of the (static part of the) shape
-- in a type class constraint. Compare the instance contexts of the instances
-- of this class with those of 'Elt': some instances have an additional
-- "known-shape" constraint.
--
-- This class is (currently) only required for `memptyArray` and 'mgenerate'.
class Elt a => KnownElt a where
  -- | Create an empty array. The given shape must have size zero; this may or may not be checked.
  memptyArrayUnsafe :: IShX sh -> Mixed sh a

  -- | Create uninitialised vectors for this array type, given the shape of
  -- this vector and an example for the contents.
  mvecsUnsafeNew :: IShX sh -> a -> ST s (MixedVecs s sh a)

  -- | Create initialised vectors for this array type, given the shape of
  -- this vector and the chosen element.
  mvecsReplicate :: IShX sh -> a -> ST s (MixedVecs s sh a)

  mvecsNewEmpty :: Proxy a -> ST s (MixedVecs s sh a)


-- Arrays of scalars are basically just arrays of scalars.
instance Storable a => Elt (Primitive a) where
  -- Somehow, INLINE here can increase allocation with GHC 9.14.1.
  -- Maybe that happens in void instances such as @Primitive ()@.
  {-# INLINEABLE mshape #-}
  mshape (M_Primitive sh _) = sh
  {-# INLINEABLE mindex #-}
  mindex (M_Primitive _ a) i = Primitive (X.index a i)
  {-# INLINEABLE mindexPartial #-}
  mindexPartial (M_Primitive sh a) i = M_Primitive (shxDropIx i sh) (X.indexPartial a i)
  mscalar (Primitive x) = M_Primitive ZSX (X.scalar x)
  mfromListOuterSN sn l@(arr1 :| _) =
    let sh = SKnown sn :$% mshape arr1
    in M_Primitive sh (X.fromListOuter (ssxFromShX sh) (map (\(M_Primitive _ a) -> a) (toList l)))
  mtoListOuter (M_Primitive sh arr) = map (M_Primitive (shxTail sh)) (X.toListOuter arr)

  {-# INLINE mlift #-}
  mlift :: forall sh1 sh2.
           StaticShX sh2
        -> (StaticShX '[] -> XArray (sh1 ++ '[]) a -> XArray (sh2 ++ '[]) a)
        -> Mixed sh1 (Primitive a) -> Mixed sh2 (Primitive a)
  mlift ssh2 f (M_Primitive _ a)
    | Refl <- lemAppNil @sh1
    , Refl <- lemAppNil @sh2
    , let result = f ZKX a
    = M_Primitive (X.shape ssh2 result) result

  {-# INLINE mlift2 #-}
  mlift2 :: forall sh1 sh2 sh3.
            StaticShX sh3
         -> (StaticShX '[] -> XArray (sh1 ++ '[]) a -> XArray (sh2 ++ '[]) a -> XArray (sh3 ++ '[]) a)
         -> Mixed sh1 (Primitive a) -> Mixed sh2 (Primitive a) -> Mixed sh3 (Primitive a)
  mlift2 ssh3 f (M_Primitive _ a) (M_Primitive _ b)
    | Refl <- lemAppNil @sh1
    , Refl <- lemAppNil @sh2
    , Refl <- lemAppNil @sh3
    , let result = f ZKX a b
    = M_Primitive (X.shape ssh3 result) result

  {-# INLINE mliftL #-}
  mliftL :: forall sh1 sh2.
            StaticShX sh2
         -> (forall sh' b. Storable b => StaticShX sh' -> NonEmpty (XArray (sh1 ++ sh') b) -> NonEmpty (XArray (sh2 ++ sh') b))
         -> NonEmpty (Mixed sh1 (Primitive a)) -> NonEmpty (Mixed sh2 (Primitive a))
  mliftL ssh2 f l
    | Refl <- lemAppNil @sh1
    , Refl <- lemAppNil @sh2
    = fmap (\arr -> M_Primitive (X.shape ssh2 arr) arr) $
        f ZKX (fmap (\(M_Primitive _ arr) -> arr) l)

  mcastPartial :: forall sh1 sh2 sh'. Rank sh1 ~ Rank sh2
               => StaticShX sh1 -> StaticShX sh2 -> Proxy sh' -> Mixed (sh1 ++ sh') (Primitive a) -> Mixed (sh2 ++ sh') (Primitive a)
  mcastPartial ssh1 ssh2 _ (M_Primitive sh1' arr) =
    let (sh1, sh') = shxSplitApp (Proxy @sh') ssh1 sh1'
        sh2 = shxCast' ssh2 sh1
    in M_Primitive (shxAppend sh2 sh') (X.cast ssh1 sh2 (ssxFromShX sh') arr)

  mtranspose perm (M_Primitive sh arr) =
    M_Primitive (shxPermutePrefix perm sh)
                (X.transpose (ssxFromShX sh) perm arr)

  mconcat :: forall sh. NonEmpty (Mixed (Nothing : sh) (Primitive a)) -> Mixed (Nothing : sh) (Primitive a)
  mconcat l@(M_Primitive (_ :$% sh) _ :| _) =
    let result = X.concat (ssxFromShX sh) (fmap (\(M_Primitive _ arr) -> arr) l)
    in M_Primitive (X.shape (SUnknown () :!% ssxFromShX sh) result) result

  mrnf (M_Primitive sh a) = rnf sh `seq` rnf a

  type ShapeTree (Primitive a) = ()
  mshapeTree _ = ()
  mshapeTreeEq _ () () = True
  mshapeTreeIsEmpty _ () = False
  mshowShapeTree _ () = "()"
  marrayStrides (M_Primitive _ arr) = BOne (X.arrayStrides arr)
  mvecsWriteLinear i (Primitive x) (MV_Primitive v) = VSM.write v i x

  -- TODO: this use of toVector is suboptimal
  mvecsWritePartialLinear
    :: forall sh' sh s.
       Proxy sh -> Int -> Mixed sh' (Primitive a) -> MixedVecs s (sh ++ sh') (Primitive a) -> ST s ()
  mvecsWritePartialLinear _ i (M_Primitive sh' arr) (MV_Primitive v) = do
    let arrsh = X.shape (ssxFromShX sh') arr
        offset = i * shxSize arrsh
    VS.copy (VSM.slice offset (shxSize arrsh) v) (X.toVector arr)

  mvecsFreeze sh (MV_Primitive v) = M_Primitive sh . X.fromVector sh <$> VS.freeze v
  mvecsUnsafeFreeze sh (MV_Primitive v) = M_Primitive sh . X.fromVector sh <$> VS.unsafeFreeze v

-- [PRIMITIVE ELEMENT TYPES LIST]
deriving via Primitive Bool instance Elt Bool
deriving via Primitive Int instance Elt Int
deriving via Primitive Int64 instance Elt Int64
deriving via Primitive Int32 instance Elt Int32
deriving via Primitive Int16 instance Elt Int16
deriving via Primitive Int8 instance Elt Int8
deriving via Primitive CInt instance Elt CInt
deriving via Primitive Double instance Elt Double
deriving via Primitive Float instance Elt Float
deriving via Primitive () instance Elt ()

instance Storable a => KnownElt (Primitive a) where
  memptyArrayUnsafe sh = M_Primitive sh (X.empty sh)
  mvecsUnsafeNew sh _ = MV_Primitive <$> VSM.unsafeNew (shxSize sh)
  mvecsReplicate sh (Primitive a) = MV_Primitive <$> VSM.replicate (shxSize sh) a
  mvecsNewEmpty _ = MV_Primitive <$> VSM.unsafeNew 0

-- [PRIMITIVE ELEMENT TYPES LIST]
deriving via Primitive Bool instance KnownElt Bool
deriving via Primitive Int instance KnownElt Int
deriving via Primitive Int64 instance KnownElt Int64
deriving via Primitive Int32 instance KnownElt Int32
deriving via Primitive Int16 instance KnownElt Int16
deriving via Primitive Int8 instance KnownElt Int8
deriving via Primitive CInt instance KnownElt CInt
deriving via Primitive Double instance KnownElt Double
deriving via Primitive Float instance KnownElt Float
deriving via Primitive () instance KnownElt ()

-- Arrays of pairs are pairs of arrays.
instance (Elt a, Elt b) => Elt (a, b) where
  {-# INLINEABLE mshape #-}
  mshape (M_Tup2 a _) = mshape a
  {-# INLINEABLE mindex #-}
  mindex (M_Tup2 a b) i = (mindex a i, mindex b i)
  {-# INLINEABLE mindexPartial #-}
  mindexPartial (M_Tup2 a b) i = M_Tup2 (mindexPartial a i) (mindexPartial b i)
  mscalar (x, y) = M_Tup2 (mscalar x) (mscalar y)
  mfromListOuterSN sn l =
    M_Tup2 (mfromListOuterSN sn ((\(M_Tup2 x _) -> x) <$> l))
           (mfromListOuterSN sn ((\(M_Tup2 _ y) -> y) <$> l))
  mtoListOuter (M_Tup2 a b) = zipWith M_Tup2 (mtoListOuter a) (mtoListOuter b)
  {-# INLINE mlift #-}
  mlift ssh2 f (M_Tup2 a b) = M_Tup2 (mlift ssh2 f a) (mlift ssh2 f b)
  {-# INLINE mlift2 #-}
  mlift2 ssh3 f (M_Tup2 a b) (M_Tup2 x y) = M_Tup2 (mlift2 ssh3 f a x) (mlift2 ssh3 f b y)
  {-# INLINE mliftL #-}
  mliftL ssh2 f =
    let unzipT2l [] = ([], [])
        unzipT2l (M_Tup2 a b : l) = let (l1, l2) = unzipT2l l in (a : l1, b : l2)
        unzipT2 (M_Tup2 a b :| l) = let (l1, l2) = unzipT2l l in (a :| l1, b :| l2)
    in uncurry (NE.zipWith M_Tup2) . bimap (mliftL ssh2 f) (mliftL ssh2 f) . unzipT2

  mcastPartial ssh1 sh2 psh' (M_Tup2 a b) =
    M_Tup2 (mcastPartial ssh1 sh2 psh' a) (mcastPartial ssh1 sh2 psh' b)

  mtranspose perm (M_Tup2 a b) = M_Tup2 (mtranspose perm a) (mtranspose perm b)
  mconcat =
    let unzipT2l [] = ([], [])
        unzipT2l (M_Tup2 a b : l) = let (l1, l2) = unzipT2l l in (a : l1, b : l2)
        unzipT2 (M_Tup2 a b :| l) = let (l1, l2) = unzipT2l l in (a :| l1, b :| l2)
    in uncurry M_Tup2 . bimap mconcat mconcat . unzipT2

  mrnf (M_Tup2 a b) = mrnf a `seq` mrnf b

  type ShapeTree (a, b) = (ShapeTree a, ShapeTree b)
  mshapeTree (x, y) = (mshapeTree x, mshapeTree y)
  mshapeTreeEq _ (t1, t2) (t1', t2') = mshapeTreeEq (Proxy @a) t1 t1' && mshapeTreeEq (Proxy @b) t2 t2'
  mshapeTreeIsEmpty _ (t1, t2) = mshapeTreeIsEmpty (Proxy @a) t1 && mshapeTreeIsEmpty (Proxy @b) t2
  mshowShapeTree _ (t1, t2) = "(" ++ mshowShapeTree (Proxy @a) t1 ++ ", " ++ mshowShapeTree (Proxy @b) t2 ++ ")"
  marrayStrides (M_Tup2 a b) = marrayStrides a <> marrayStrides b
  mvecsWriteLinear i (x, y) (MV_Tup2 a b) = do
    mvecsWriteLinear i x a
    mvecsWriteLinear i y b
  mvecsWritePartialLinear proxy i (M_Tup2 x y) (MV_Tup2 a b) = do
    mvecsWritePartialLinear proxy i x a
    mvecsWritePartialLinear proxy i y b
  mvecsFreeze sh (MV_Tup2 a b) = M_Tup2 <$> mvecsFreeze sh a <*> mvecsFreeze sh b
  mvecsUnsafeFreeze sh (MV_Tup2 a b) = M_Tup2 <$> mvecsUnsafeFreeze sh a <*> mvecsUnsafeFreeze sh b

instance (KnownElt a, KnownElt b) => KnownElt (a, b) where
  memptyArrayUnsafe sh = M_Tup2 (memptyArrayUnsafe sh) (memptyArrayUnsafe sh)
  mvecsUnsafeNew sh (x, y) = MV_Tup2 <$> mvecsUnsafeNew sh x <*> mvecsUnsafeNew sh y
  mvecsReplicate sh (x, y) = MV_Tup2 <$> mvecsReplicate sh x <*> mvecsReplicate sh y
  mvecsNewEmpty _ = MV_Tup2 <$> mvecsNewEmpty (Proxy @a) <*> mvecsNewEmpty (Proxy @b)

-- Arrays of arrays are just arrays, but with more dimensions.
instance Elt a => Elt (Mixed sh' a) where
  -- TODO: this is quadratic in the nesting depth because it repeatedly
  -- truncates the shape vector to one a little shorter. Fix with a
  -- moverlongShape method, a prefix of which is mshape.
  {-# INLINEABLE mshape #-}
  mshape :: forall sh. Mixed sh (Mixed sh' a) -> IShX sh
  mshape (M_Nest sh arr)
    = shxTakeSh (Proxy @sh') sh (mshape arr)

  {-# INLINEABLE mindex #-}
  mindex :: Mixed sh (Mixed sh' a) -> IIxX sh -> Mixed sh' a
  mindex (M_Nest _ arr) = mindexPartial arr

  {-# INLINEABLE mindexPartial #-}
  mindexPartial :: forall sh1 sh2.
                   Mixed (sh1 ++ sh2) (Mixed sh' a) -> IIxX sh1 -> Mixed sh2 (Mixed sh' a)
  mindexPartial (M_Nest sh arr) i
    | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @sh2) (Proxy @sh')
    = M_Nest (shxDropIx i sh) (mindexPartial @a @sh1 @(sh2 ++ sh') arr i)

  mscalar = M_Nest ZSX

  mfromListOuterSN sn l@(arr :| _) =
    M_Nest (SKnown sn :$% mshape arr)
           (mfromListOuterSN sn ((\(M_Nest _ a) -> a) <$> l))

  mtoListOuter (M_Nest sh arr) = map (M_Nest (shxTail sh)) (mtoListOuter arr)

  {-# INLINE mlift #-}
  mlift :: forall sh1 sh2.
           StaticShX sh2
        -> (forall shT b. Storable b => StaticShX shT -> XArray (sh1 ++ shT) b -> XArray (sh2 ++ shT) b)
        -> Mixed sh1 (Mixed sh' a) -> Mixed sh2 (Mixed sh' a)
  mlift ssh2 f (M_Nest sh1 arr) =
    let result = mlift (ssxAppend ssh2 ssh') f' arr
        sh2 = shxTakeSSX (Proxy @sh') ssh2 (mshape result)
    in M_Nest sh2 result
    where
      ssh' = ssxFromShX (shxDropSh @sh1 @sh' sh1 (mshape arr))

      f' :: forall shT b. Storable b => StaticShX shT -> XArray ((sh1 ++ sh') ++ shT) b -> XArray ((sh2 ++ sh') ++ shT) b
      f' sshT
        | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @sh') (Proxy @shT)
        , Refl <- lemAppAssoc (Proxy @sh2) (Proxy @sh') (Proxy @shT)
        = f (ssxAppend ssh' sshT)

  {-# INLINE mlift2 #-}
  mlift2 :: forall sh1 sh2 sh3.
            StaticShX sh3
         -> (forall shT b. Storable b => StaticShX shT -> XArray (sh1 ++ shT) b -> XArray (sh2 ++ shT) b -> XArray (sh3 ++ shT) b)
         -> Mixed sh1 (Mixed sh' a) -> Mixed sh2 (Mixed sh' a) -> Mixed sh3 (Mixed sh' a)
  mlift2 ssh3 f (M_Nest sh1 arr1) (M_Nest _ arr2) =
    let result = mlift2 (ssxAppend ssh3 ssh') f' arr1 arr2
        sh3 = shxTakeSSX (Proxy @sh') ssh3 (mshape result)
    in M_Nest sh3 result
    where
      ssh' = ssxFromShX (shxDropSh @sh1 @sh' sh1 (mshape arr1))

      f' :: forall shT b. Storable b => StaticShX shT -> XArray ((sh1 ++ sh') ++ shT) b -> XArray ((sh2 ++ sh') ++ shT) b -> XArray ((sh3 ++ sh') ++ shT) b
      f' sshT
        | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @sh') (Proxy @shT)
        , Refl <- lemAppAssoc (Proxy @sh2) (Proxy @sh') (Proxy @shT)
        , Refl <- lemAppAssoc (Proxy @sh3) (Proxy @sh') (Proxy @shT)
        = f (ssxAppend ssh' sshT)

  {-# INLINE mliftL #-}
  mliftL :: forall sh1 sh2.
            StaticShX sh2
         -> (forall shT b. Storable b => StaticShX shT -> NonEmpty (XArray (sh1 ++ shT) b) -> NonEmpty (XArray (sh2 ++ shT) b))
         -> NonEmpty (Mixed sh1 (Mixed sh' a)) -> NonEmpty (Mixed sh2 (Mixed sh' a))
  mliftL ssh2 f l@(M_Nest sh1 arr1 :| _) =
    let result = mliftL (ssxAppend ssh2 ssh') f' (fmap (\(M_Nest _ arr) -> arr) l)
        sh2 = shxTakeSSX (Proxy @sh') ssh2 (mshape (NE.head result))
    in fmap (M_Nest sh2) result
    where
      ssh' = ssxFromShX (shxDropSh @sh1 @sh' sh1 (mshape arr1))

      f' :: forall shT b. Storable b => StaticShX shT -> NonEmpty (XArray ((sh1 ++ sh') ++ shT) b) -> NonEmpty (XArray ((sh2 ++ sh') ++ shT) b)
      f' sshT
        | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @sh') (Proxy @shT)
        , Refl <- lemAppAssoc (Proxy @sh2) (Proxy @sh') (Proxy @shT)
        = f (ssxAppend ssh' sshT)

  mcastPartial :: forall sh1 sh2 shT. Rank sh1 ~ Rank sh2
               => StaticShX sh1 -> StaticShX sh2 -> Proxy shT -> Mixed (sh1 ++ shT) (Mixed sh' a) -> Mixed (sh2 ++ shT) (Mixed sh' a)
  mcastPartial ssh1 ssh2 _ (M_Nest sh1T arr)
    | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @shT) (Proxy @sh')
    , Refl <- lemAppAssoc (Proxy @sh2) (Proxy @shT) (Proxy @sh')
    = let (sh1, shT) = shxSplitApp (Proxy @shT) ssh1 sh1T
          sh2 = shxCast' ssh2 sh1
      in M_Nest (shxAppend sh2 shT) (mcastPartial ssh1 ssh2 (Proxy @(shT ++ sh')) arr)

  mtranspose :: forall is sh. (IsPermutation is, Rank is <= Rank sh)
             => Perm is -> Mixed sh (Mixed sh' a)
             -> Mixed (PermutePrefix is sh) (Mixed sh' a)
  mtranspose perm (M_Nest sh arr)
    | let sh' = shxDropSh @sh @sh' sh (mshape arr)
    , Refl <- lemRankApp (ssxFromShX sh) (ssxFromShX sh')
    , Refl <- lemLeqPlus (Proxy @(Rank is)) (Proxy @(Rank sh)) (Proxy @(Rank sh'))
    , Refl <- lemAppAssoc (Proxy @(Permute is (TakeLen is (sh ++ sh')))) (Proxy @(DropLen is sh)) (Proxy @sh')
    , Refl <- lemDropLenApp (Proxy @is) (Proxy @sh) (Proxy @sh')
    , Refl <- lemTakeLenApp (Proxy @is) (Proxy @sh) (Proxy @sh')
    = M_Nest (shxPermutePrefix perm sh)
             (mtranspose perm arr)

  mconcat :: NonEmpty (Mixed (Nothing : sh) (Mixed sh' a)) -> Mixed (Nothing : sh) (Mixed sh' a)
  mconcat l@(M_Nest sh1 _ :| _) =
    let result = mconcat (fmap (\(M_Nest _ arr) -> arr) l)
    in M_Nest (shxTakeSh (Proxy @sh') sh1 (mshape result)) result

  mrnf (M_Nest sh arr) = rnf sh `seq` mrnf arr

  type ShapeTree (Mixed sh' a) = (IShX sh', ShapeTree a)

  mshapeTree :: Mixed sh' a -> ShapeTree (Mixed sh' a)
  mshapeTree arr = (mshape arr, mshapeTree (mindex arr (ixxZero (ssxFromShX (mshape arr)))))

  mshapeTreeEq _ (sh1, t1) (sh2, t2) = sh1 == sh2 && mshapeTreeEq (Proxy @a) t1 t2

  -- the array is empty if either there are no subarrays, or the subarrays themselves are empty
  mshapeTreeIsEmpty _ (sh, t) = shxSize sh == 0 || mshapeTreeIsEmpty (Proxy @a) t

  mshowShapeTree _ (sh, t) = "(" ++ show sh ++ ", " ++ mshowShapeTree (Proxy @a) t ++ ")"

  marrayStrides (M_Nest _ arr) = marrayStrides arr

  mvecsWriteLinear :: forall s sh. Int -> Mixed sh' a -> MixedVecs s sh (Mixed sh' a) -> ST s ()
  mvecsWriteLinear idx val (MV_Nest _ vecs) = mvecsWritePartialLinear (Proxy @sh) idx val vecs

  mvecsWritePartialLinear
    :: forall sh1 sh2 s.
       Proxy sh1 -> Int -> Mixed sh2 (Mixed sh' a)
    -> MixedVecs s (sh1 ++ sh2) (Mixed sh' a)
    -> ST s ()
  mvecsWritePartialLinear proxy idx (M_Nest _ arr) (MV_Nest _ vecs)
    | Refl <- lemAppAssoc (Proxy @sh1) (Proxy @sh2) (Proxy @sh')
    = mvecsWritePartialLinear proxy idx arr vecs

  mvecsFreeze sh (MV_Nest sh' vecs) = M_Nest sh <$> mvecsFreeze (shxAppend sh sh') vecs
  mvecsUnsafeFreeze sh (MV_Nest sh' vecs) = M_Nest sh <$> mvecsUnsafeFreeze (shxAppend sh sh') vecs

instance (KnownShX sh', KnownElt a) => KnownElt (Mixed sh' a) where
  memptyArrayUnsafe sh = M_Nest sh (memptyArrayUnsafe (shxAppend sh (shxCompleteZeros (knownShX @sh'))))

  mvecsUnsafeNew sh example
    | shxSize sh' == 0 = mvecsNewEmpty (Proxy @(Mixed sh' a))
    | otherwise = MV_Nest sh' <$> mvecsUnsafeNew (shxAppend sh sh') (mindex example (ixxZero (ssxFromShX sh')))
    where
      sh' = mshape example

  mvecsReplicate sh example = do
    vecs <- mvecsUnsafeNew sh example
    forM_ [0 .. shxSize sh - 1] $ \idx -> mvecsWriteLinear idx example vecs
      -- this is a slow case, but the alternative, mvecsUnsafeNew with manual
      -- writing in a loop, leads to every case being as slow
    return vecs

  mvecsNewEmpty _ = MV_Nest (shxCompleteZeros (knownShX @sh')) <$> mvecsNewEmpty (Proxy @a)


-- | Given the shape of this array, an index and a value, write the value at
-- that index in the vectors.
{-# INLINE mvecsWrite #-}
mvecsWrite :: Elt a => IShX sh -> IIxX sh -> a -> MixedVecs s sh a -> ST s ()
mvecsWrite sh idx val vecs = mvecsWriteLinear (ixxToLinear sh idx) val vecs

-- | Given the shape of this array, an index and a value, write the value at
-- that index in the vectors.
{-# INLINE mvecsWritePartial #-}
mvecsWritePartial :: forall sh sh' s a. Elt a => IShX sh -> IIxX sh -> Mixed sh' a -> MixedVecs s (sh ++ sh') a -> ST s ()
mvecsWritePartial sh idx val vecs = mvecsWritePartialLinear (Proxy @sh) (ixxToLinear sh idx) val vecs

-- TODO: should we provide a function that's just memptyArrayUnsafe but with a size==0 check? That may save someone a transpose somewhere
memptyArray :: forall sh a. KnownElt a => IShX sh -> Mixed (Just 0 : sh) a
memptyArray sh = memptyArrayUnsafe (SKnown SNat :$% sh)

mrank :: Elt a => Mixed sh a -> SNat (Rank sh)
mrank = shxRank . mshape

-- | The total number of elements in the array.
msize :: Elt a => Mixed sh a -> Int
msize = shxSize . mshape

-- | Create an array given a size and a function that computes the element at a
-- given index.
--
-- __WARNING__: It is required that every @a@ returned by the argument to
-- 'mgenerate' has the same shape. For example, the following will throw a
-- runtime error:
--
-- > foo :: Mixed [Nothing] (Mixed [Nothing] Double)
-- > foo = mgenerate (10 :.: ZIR) $ \(i :.: ZIR) ->
-- >         mgenerate (i :.: ZIR) $ \(j :.: ZIR) ->
-- >           ...
--
-- because the size of the inner 'mgenerate' is not always the same (it depends
-- on @i@). Nested arrays in @ox-arrays@ are always stored fully flattened, so
-- the entire hierarchy (after distributing out tuples) must be a rectangular
-- array. The type of 'mgenerate' allows this requirement to be broken very
-- easily, hence the runtime check.
--
-- If your element type @a@ is a scalar, use the faster 'mgeneratePrim'.
mgenerate :: forall sh a. KnownElt a => IShX sh -> (IIxX sh -> a) -> Mixed sh a
mgenerate sh f = case shxEnum sh of
  [] -> memptyArrayUnsafe sh
  firstidx : restidxs ->
    let firstelem = f (ixxZero' sh)
        shapetree = mshapeTree firstelem
    in if mshapeTreeIsEmpty (Proxy @a) shapetree
         then memptyArrayUnsafe sh
         else runST $ do
                vecs <- mvecsUnsafeNew sh firstelem
                mvecsWrite sh firstidx firstelem vecs
                forM_ restidxs $ \idx -> do
                  let val = f idx
                  when (not (mshapeTreeEq (Proxy @a) (mshapeTree val) shapetree)) $
                    error "Data.Array.Nested mgenerate: generated values do not have equal shapes"
                  mvecsWrite sh idx val vecs
                mvecsUnsafeFreeze sh vecs

-- | An optimized special case of 'mgenerate', where the function results
-- are of a primitive type and so there's not need to check that all shapes
-- are equal. This is also generalized to an arbitrary @Num@ index type
-- compared to @mgenerate@.
{-# INLINE mgeneratePrim #-}
mgeneratePrim :: forall sh a i. (PrimElt a, Num i)
              => IShX sh -> (IxX sh i -> a) -> Mixed sh a
mgeneratePrim sh f =
  let g i = f (ixxFromLinear sh i)
  in mfromVector sh $ VS.generate (shxSize sh) g

{-# INLINEABLE msumOuter1PrimP #-}
msumOuter1PrimP :: forall sh n a. (Storable a, NumElt a)
                => Mixed (n : sh) (Primitive a) -> Mixed sh (Primitive a)
msumOuter1PrimP (M_Primitive (n :$% sh) arr) =
  let nssh = fromSMayNat (\_ -> SUnknown ()) SKnown n :!% ZKX
  in M_Primitive sh (X.sumOuter nssh (ssxFromShX sh) arr)

{-# INLINEABLE msumOuter1Prim #-}
msumOuter1Prim :: forall sh n a. (NumElt a, PrimElt a)
               => Mixed (n : sh) a -> Mixed sh a
msumOuter1Prim = fromPrimitive . msumOuter1PrimP @sh @n @a . toPrimitive

{-# INLINEABLE msumAllPrimP #-}
msumAllPrimP :: (Storable a, NumElt a) => Mixed sh (Primitive a) -> a
msumAllPrimP (M_Primitive sh arr) = X.sumFull (ssxFromShX sh) arr

{-# INLINEABLE msumAllPrim #-}
msumAllPrim :: (PrimElt a, NumElt a) => Mixed sh a -> a
msumAllPrim arr = msumAllPrimP (toPrimitive arr)

mappend :: forall n m sh a. Elt a
        => Mixed (n : sh) a -> Mixed (m : sh) a -> Mixed (AddMaybe n m : sh) a
mappend arr1 arr2 = mlift2 (snm :!% ssh) f arr1 arr2
  where
    sn :$% sh = mshape arr1
    sm :$% _ = mshape arr2
    ssh = ssxFromShX sh
    snm :: SMayNat () (AddMaybe n m)
    snm = case (sn, sm) of
            (SUnknown{}, _) -> SUnknown ()
            (SKnown{}, SUnknown{}) -> SUnknown ()
            (SKnown n, SKnown m) -> SKnown (snatPlus n m)

    f :: forall sh' b. Storable b
      => StaticShX sh' -> XArray (n : sh ++ sh') b -> XArray (m : sh ++ sh') b -> XArray (AddMaybe n m : sh ++ sh') b
    f ssh' = X.append (ssxAppend ssh ssh')

{-# INLINEABLE mfromVectorP #-}
mfromVectorP :: forall sh a. Storable a => IShX sh -> VS.Vector a -> Mixed sh (Primitive a)
mfromVectorP sh v = M_Primitive sh (X.fromVector sh v)

{-# INLINEABLE mfromVector #-}
mfromVector :: forall sh a. PrimElt a => IShX sh -> VS.Vector a -> Mixed sh a
mfromVector sh v = fromPrimitive (mfromVectorP sh v)

{-# INLINEABLE mtoVectorP #-}
mtoVectorP :: Storable a => Mixed sh (Primitive a) -> VS.Vector a
mtoVectorP (M_Primitive _ v) = X.toVector v

{-# INLINEABLE mtoVector #-}
mtoVector :: PrimElt a => Mixed sh a -> VS.Vector a
mtoVector arr = mtoVectorP (toPrimitive arr)

-- | All arrays in the list, even subarrays inside @a@, must have the same
-- shape; if they do not, a runtime error will be thrown. See the
-- documentation of 'mgenerate' for more information about this restriction.
--
-- Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'mfromListOuterN' or 'mfromListOuterSN' to be able to
-- stream the list.
--
-- If your array is 1-dimensional and contains scalars, use 'mfromList1Prim'.
mfromListOuter :: Elt a => NonEmpty (Mixed sh a) -> Mixed (Nothing : sh) a
mfromListOuter l = mfromListOuterN (length l) l

-- | See 'mfromListOuter'. If the list does not have the given length, a
-- runtime error is thrown. 'mfromList1PrimN' is faster if applicable.
mfromListOuterN :: Elt a => Int -> NonEmpty (Mixed sh a) -> Mixed (Nothing : sh) a
mfromListOuterN n l =
  withSomeSNat (fromIntegral n) $ \case
    Just sn -> mcastPartial (SKnown sn :!% ZKX) (SUnknown () :!% ZKX) Proxy (mfromListOuterSN sn l)
    Nothing -> error $ "mfromListOuterN: length negative (" ++ show n ++ ")"

-- | Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'mfromList1N' or 'mfromList1SN' to be able to stream the
-- list.
--
-- If the elements are scalars, 'mfromList1Prim' is faster.
mfromList1 :: Elt a => NonEmpty a -> Mixed '[Nothing] a
mfromList1 = mfromListOuter . fmap mscalar

-- | If the elements are scalars, 'mfromList1PrimN' is faster. A runtime error
-- is thrown if the list length does not match the given length.
mfromList1N :: Elt a => Int -> NonEmpty a -> Mixed '[Nothing] a
mfromList1N n = mfromListOuterN n . fmap mscalar

-- | If the elements are scalars, 'mfromList1PrimSN' is faster. A runtime error
-- is thrown if the list length does not match the given length.
mfromList1SN :: Elt a => SNat n -> NonEmpty a -> Mixed '[Just n] a
mfromList1SN sn = mfromListOuterSN sn . fmap mscalar

-- This forall is there so that a simple type application can constrain the
-- shape, in case the user wants to use OverloadedLists for the shape.
-- | If the elements are scalars, 'mfromListPrimLinear' is faster.
mfromListLinear :: forall sh a. Elt a => IShX sh -> NonEmpty a -> Mixed sh a
mfromListLinear sh l = mreshape sh (mfromList1N (shxSize sh) l)

-- | Because the length of the list is unknown, its spine must be materialised
-- in memory in order to compute its length. If its length is already known,
-- use 'mfromList1PrimN' or 'mfromList1PrimSN' to be able to stream the list.
mfromList1Prim :: PrimElt a => [a] -> Mixed '[Nothing] a
mfromList1Prim l =
  let ssh = SUnknown () :!% ZKX
      xarr = X.fromList1 ssh l
  in fromPrimitive $ M_Primitive (X.shape ssh xarr) xarr

mfromList1PrimN :: PrimElt a => Int -> [a] -> Mixed '[Nothing] a
mfromList1PrimN n l =
  withSomeSNat (fromIntegral n) $ \case
    Just sn -> mcastPartial (SKnown sn :!% ZKX) (SUnknown () :!% ZKX) Proxy (mfromList1PrimSN sn l)
    Nothing -> error $ "mfromList1PrimN: length negative (" ++ show n ++ ")"

mfromList1PrimSN :: PrimElt a => SNat n -> [a] -> Mixed '[Just n] a
mfromList1PrimSN sn l =
  let ssh = SKnown sn :!% ZKX
      xarr = X.fromList1 ssh l
  in fromPrimitive $ M_Primitive (X.shape ssh xarr) xarr

mfromListPrimLinear :: forall sh a. PrimElt a => IShX sh -> [a] -> Mixed sh a
mfromListPrimLinear sh l =
  let M_Primitive _ xarr = toPrimitive (mfromList1PrimN (shxSize sh) l)
  in fromPrimitive $ M_Primitive sh (X.reshape (SUnknown () :!% ZKX) sh xarr)

mtoList :: Elt a => Mixed '[n] a -> [a]
mtoList = map munScalar . mtoListOuter

mtoListLinear :: Elt a => Mixed sh a -> [a]
mtoListLinear arr = map (mindex arr) (shxEnum (mshape arr))  -- TODO: optimise

munScalar :: Elt a => Mixed '[] a -> a
munScalar arr = mindex arr ZIX

mnest :: forall sh sh' a. Elt a => StaticShX sh -> Mixed (sh ++ sh') a -> Mixed sh (Mixed sh' a)
mnest ssh arr = M_Nest (shxTakeSSX (Proxy @sh') ssh (mshape arr)) arr

munNest :: Mixed sh (Mixed sh' a) -> Mixed (sh ++ sh') a
munNest (M_Nest _ arr) = arr

-- | The arguments must have equal shapes. If they do not, an error is raised.
mzip :: (Elt a, Elt b) => Mixed sh a -> Mixed sh b -> Mixed sh (a, b)
mzip a b
  | Just Refl <- shxEqual (mshape a) (mshape b) = M_Tup2 a b
  | otherwise = error "mzip: unequal shapes"

munzip :: Mixed sh (a, b) -> (Mixed sh a, Mixed sh b)
munzip (M_Tup2 a b) = (a, b)

mrerankPrimP :: forall sh1 sh2 sh a b. (Storable a, Storable b)
             => IShX sh2
             -> (Mixed sh1 (Primitive a) -> Mixed sh2 (Primitive b))
             -> Mixed sh (Mixed sh1 (Primitive a)) -> Mixed sh (Mixed sh2 (Primitive b))
mrerankPrimP sh2 f (M_Nest sh (M_Primitive shsh1 arr)) =
  let sh1 = shxDropSh sh shsh1
  in M_Nest sh $
       M_Primitive (shxAppend sh sh2)
                   (X.rerank (ssxFromShX sh) (ssxFromShX sh1) (ssxFromShX sh2)
                             (\a -> let M_Primitive _ r = f (M_Primitive sh1 a) in r)
                             arr)

-- | If the shape of the outer array (@sh@) is empty (i.e. contains a zero),
-- then there is no way to deduce the full shape of the output array (more
-- precisely, the @sh2@ part): that could only come from calling @f@, and there
-- are no subarrays to call @f@ on. @orthotope@ errors out in this case; we
-- choose to fill the shape with zeros wherever we cannot deduce what it should
-- be.
--
-- For example, if:
--
-- @
-- -- arr has shape [3, 0, 4] and the inner arrays have shape [2, 21]
-- arr :: Mixed '[Just 3, Just 0, Just 4] (Mixed '[Just 2, Nothing] Int)
-- f :: Mixed '[Just 2, Nothing] Int -> Mixed '[Just 5, Nothing, Just 17] Float
-- @
--
-- then:
--
-- @
-- mrerankPrim _ f arr :: Mixed '[Just 3, Just 0, Just 4] (Mixed '[Just 5, Nothing, Just 17] Float)
-- @
--
-- and the inner arrays of the result will have shape @[5, 0, 17]@. Note the
-- @0@ in this shape: we don't know if @f@ intended to return an array with
-- shape 0 here (it probably didn't), but there is no better number to put here
-- absent a subarray of the input to pass to @f@.
--
-- In this particular case the fact that @sh@ is empty was evident from the
-- type-level information, but the same situation occurs when @sh@ consists of
-- @Nothing@s, and some of those happen to be zero at runtime.
mrerankPrim :: forall sh1 sh2 sh a b. (PrimElt a, PrimElt b)
            => IShX sh2
            -> (Mixed sh1 a -> Mixed sh2 b)
            -> Mixed sh (Mixed sh1 a) -> Mixed sh (Mixed sh2 b)
mrerankPrim sh2 f (M_Nest sh arr) =
  let M_Nest sh' arr' = mrerankPrimP sh2 (toPrimitive . f . fromPrimitive) (M_Nest sh (toPrimitive arr))
  in M_Nest sh' (fromPrimitive arr')

mreplicate :: forall sh sh' a. Elt a
           => IShX sh -> Mixed sh' a -> Mixed (sh ++ sh') a
mreplicate sh arr =
  let ssh' = ssxFromShX (mshape arr)
  in mlift (ssxAppend (ssxFromShX sh) ssh')
           (\(sshT :: StaticShX shT) ->
              case lemAppAssoc (Proxy @sh) (Proxy @sh') (Proxy @shT) of
                Refl -> X.replicate sh (ssxAppend ssh' sshT))
           arr

mreplicatePrimP :: forall sh a. Storable a => IShX sh -> a -> Mixed sh (Primitive a)
mreplicatePrimP sh x = M_Primitive sh (X.replicateScal sh x)

mreplicatePrim :: forall sh a. PrimElt a
               => IShX sh -> a -> Mixed sh a
mreplicatePrim sh x = fromPrimitive (mreplicatePrimP sh x)

msliceN :: Elt a => Int -> Int -> Mixed (Nothing : sh) a -> Mixed (Nothing : sh) a
msliceN i n arr = mlift (ssxFromShX (mshape arr)) (\_ -> X.sliceU i n) arr

msliceSN :: Elt a => SNat i -> SNat n -> Mixed (Just (i + n + k) : sh) a -> Mixed (Just n : sh) a
msliceSN i n arr =
  let _ :$% sh = mshape arr
  in mlift (SKnown n :!% ssxFromShX sh) (\_ -> X.slice i n) arr

mrev1 :: Elt a => Mixed (n : sh) a -> Mixed (n : sh) a
mrev1 arr = mlift (ssxFromShX (mshape arr)) (\_ -> X.rev1) arr

mreshape :: forall sh sh' a. Elt a => IShX sh' -> Mixed sh a -> Mixed sh' a
mreshape sh' arr =
  mlift (ssxFromShX sh')
        (\sshIn -> X.reshapePartial (ssxFromShX (mshape arr)) sshIn sh')
        arr

mflatten :: Elt a => Mixed sh a -> Mixed '[Flatten sh] a
mflatten arr = mreshape (shxFlatten (mshape arr) :$% ZSX) arr

miota :: (Enum a, PrimElt a) => SNat n -> Mixed '[Just n] a
miota sn = fromPrimitive $ M_Primitive (SKnown sn :$% ZSX) (X.iota sn)

-- | Throws if the array is empty.
mminIndexPrim :: (PrimElt a, NumElt a) => Mixed sh a -> IIxX sh
mminIndexPrim (toPrimitive -> M_Primitive sh (XArray arr)) =
  ixxFromList (ssxFromShX sh) (numEltMinIndex (shxRank sh) (fromO arr))

-- | Throws if the array is empty.
mmaxIndexPrim :: (PrimElt a, NumElt a) => Mixed sh a -> IIxX sh
mmaxIndexPrim (toPrimitive -> M_Primitive sh (XArray arr)) =
  ixxFromList (ssxFromShX sh) (numEltMaxIndex (shxRank sh) (fromO arr))

{-# INLINEABLE mdot1Inner #-}
mdot1Inner :: forall sh n a. (PrimElt a, NumElt a)
           => Proxy n -> Mixed (sh ++ '[n]) a -> Mixed (sh ++ '[n]) a -> Mixed sh a
mdot1Inner _ (toPrimitive -> M_Primitive sh1 (XArray a)) (toPrimitive -> M_Primitive sh2 (XArray b))
  | Refl <- lemInitApp (Proxy @sh) (Proxy @n)
  , Refl <- lemLastApp (Proxy @sh) (Proxy @n)
  = case sh1 of
      _ :$% _
        | sh1 == sh2
        , Refl <- lemRankApp (ssxInit (ssxFromShX sh1)) (ssxLast (ssxFromShX sh1) :!% ZKX) ->
            fromPrimitive $ M_Primitive (shxInit sh1) (XArray (liftO2 (numEltDotprodInner (shxRank (shxInit sh1))) a b))
        | otherwise -> error $ "mdot1Inner: Unequal shapes (" ++ show sh1 ++ " and " ++ show sh2 ++ ")"
      ZSX -> error "unreachable"

-- | This has a temporary, suboptimal implementation in terms of 'mflatten'.
-- Prefer 'mdot1Inner' if applicable.
{-# INLINEABLE mdot #-}
mdot :: (PrimElt a, NumElt a) => Mixed sh a -> Mixed sh a -> a
mdot a b =
  munScalar $
    mdot1Inner Proxy (fromPrimitive (mflatten (toPrimitive a)))
                     (fromPrimitive (mflatten (toPrimitive b)))

mtoXArrayPrimP :: Mixed sh (Primitive a) -> (IShX sh, XArray sh a)
mtoXArrayPrimP (M_Primitive sh arr) = (sh, arr)

mtoXArrayPrim :: PrimElt a => Mixed sh a -> (IShX sh, XArray sh a)
mtoXArrayPrim = mtoXArrayPrimP . toPrimitive

mfromXArrayPrimP :: StaticShX sh -> XArray sh a -> Mixed sh (Primitive a)
mfromXArrayPrimP ssh arr = M_Primitive (X.shape ssh arr) arr

mfromXArrayPrim :: PrimElt a => StaticShX sh -> XArray sh a -> Mixed sh a
mfromXArrayPrim = (fromPrimitive .) . mfromXArrayPrimP

{-# INLINE mliftPrim #-}
mliftPrim :: (PrimElt a, PrimElt b)
          => (a -> b)
          -> Mixed sh a -> Mixed sh b
mliftPrim f (toPrimitive -> M_Primitive sh (X.XArray arr)) = fromPrimitive $ M_Primitive sh (X.XArray (S.mapA f arr))

{-# INLINE mliftPrim2 #-}
mliftPrim2 :: (PrimElt a, PrimElt b, PrimElt c)
           => (a -> b -> c)
           -> Mixed sh a -> Mixed sh b -> Mixed sh c
mliftPrim2 f (toPrimitive -> M_Primitive sh (X.XArray arr1)) (toPrimitive -> M_Primitive _ (X.XArray arr2)) =
  fromPrimitive $ M_Primitive sh (X.XArray (S.zipWithA f arr1 arr2))
