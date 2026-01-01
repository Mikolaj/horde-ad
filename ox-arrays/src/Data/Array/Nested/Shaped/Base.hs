{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK not-home #-}
module Data.Array.Nested.Shaped.Base where

import Prelude hiding (mappend, mconcat)

import Control.DeepSeq (NFData(..))
import Control.Monad.ST
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy
import Foreign.Storable (Storable)
import GHC.Float qualified (expm1, log1mexp, log1p, log1pexp)
import GHC.Generics (Generic)
import GHC.TypeLits

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types
import Data.Array.Strided.Arith
import Data.Array.XArray (XArray)


-- | A shape-typed array: the full shape of the array (the sizes of its
-- dimensions) is represented on the type level as a list of 'Nat's. Note that
-- these are "GHC.TypeLits" naturals, because we do not need induction over
-- them and we want very large arrays to be possible.
--
-- Like for 'Ranked', the valid elements are described by the 'Elt' type class,
-- and 'Shaped' itself is again an instance of 'Elt' as well.
--
-- 'Shaped' is a newtype around a 'Mixed' of 'Just's.
type Shaped :: [Nat] -> Type -> Type
newtype Shaped sh a = Shaped (Mixed (MapJust sh) a)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (Mixed (MapJust sh) a) => Show (Shaped sh a)
#endif
deriving instance Eq (Mixed (MapJust sh) a) => Eq (Shaped sh a)
deriving instance Ord (Mixed (MapJust sh) a) => Ord (Shaped sh a)

#ifndef OXAR_DEFAULT_SHOW_INSTANCES
instance (Show a, Elt a) => Show (Shaped n a) where
  showsPrec d arr@(Shaped marr) =
    let sh = show (shsToList (sshape arr))
    in showsMixedArray ("sfromListLinear " ++ sh) ("sreplicate " ++ sh) d marr
#endif

instance Elt a => NFData (Shaped sh a) where
  rnf (Shaped arr) = rnf arr

-- just unwrap the newtype and defer to the general instance for nested arrays
newtype instance Mixed sh (Shaped sh' a) = M_Shaped (Mixed sh (Mixed (MapJust sh') a))
  deriving (Generic)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (Mixed sh (Mixed (MapJust sh') a)) => Show (Mixed sh (Shaped sh' a))
#endif

deriving instance Eq (Mixed sh (Mixed (MapJust sh') a)) => Eq (Mixed sh (Shaped sh' a))

newtype instance MixedVecs s sh (Shaped sh' a) = MV_Shaped (MixedVecs s sh (Mixed (MapJust sh') a))

instance Elt a => Elt (Shaped sh a) where
  {-# INLINE mshape #-}
  mshape (M_Shaped arr) = mshape arr
  {-# INLINE mindex #-}
  mindex (M_Shaped arr) i = Shaped (mindex arr i)

  {-# INLINE mindexPartial #-}
  mindexPartial :: forall sh1 sh2. Mixed (sh1 ++ sh2) (Shaped sh a) -> IIxX sh1 -> Mixed sh2 (Shaped sh a)
  mindexPartial (M_Shaped arr) i =
    coerce @(Mixed sh2 (Mixed (MapJust sh) a)) @(Mixed sh2 (Shaped sh a)) $
      mindexPartial arr i

  mscalar (Shaped x) = M_Shaped (M_Nest ZSX x)

  mfromListOuterSN :: SNat n -> NonEmpty (Mixed sh' (Shaped sh a)) -> Mixed (Just n : sh') (Shaped sh a)
  mfromListOuterSN sn l = M_Shaped (mfromListOuterSN sn (coerce l))

  mtoListOuter :: forall n sh'. Mixed (n : sh') (Shaped sh a) -> [Mixed sh' (Shaped sh a)]
  mtoListOuter (M_Shaped arr)
    = coerce @[Mixed sh' (Mixed (MapJust sh) a)] @[Mixed sh' (Shaped sh a)] (mtoListOuter arr)

  {-# INLINE mlift #-}
  mlift :: forall sh1 sh2.
           StaticShX sh2
        -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b)
        -> Mixed sh1 (Shaped sh a) -> Mixed sh2 (Shaped sh a)
  mlift ssh2 f (M_Shaped arr) =
    coerce @(Mixed sh2 (Mixed (MapJust sh) a)) @(Mixed sh2 (Shaped sh a)) $
      mlift ssh2 f arr

  {-# INLINE mlift2 #-}
  mlift2 :: forall sh1 sh2 sh3.
            StaticShX sh3
         -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b -> XArray (sh3 ++ sh') b)
         -> Mixed sh1 (Shaped sh a) -> Mixed sh2 (Shaped sh a) -> Mixed sh3 (Shaped sh a)
  mlift2 ssh3 f (M_Shaped arr1) (M_Shaped arr2) =
    coerce @(Mixed sh3 (Mixed (MapJust sh) a)) @(Mixed sh3 (Shaped sh a)) $
      mlift2 ssh3 f arr1 arr2

  {-# INLINE mliftL #-}
  mliftL :: forall sh1 sh2.
            StaticShX sh2
         -> (forall sh' b. Storable b => StaticShX sh' -> NonEmpty (XArray (sh1 ++ sh') b) -> NonEmpty (XArray (sh2 ++ sh') b))
         -> NonEmpty (Mixed sh1 (Shaped sh a)) -> NonEmpty (Mixed sh2 (Shaped sh a))
  mliftL ssh2 f l =
    coerce @(NonEmpty (Mixed sh2 (Mixed (MapJust sh) a)))
           @(NonEmpty (Mixed sh2 (Shaped sh a))) $
      mliftL ssh2 f (coerce l)

  mcastPartial ssh1 ssh2 psh' (M_Shaped arr) = M_Shaped (mcastPartial ssh1 ssh2 psh' arr)

  mtranspose perm (M_Shaped arr) = M_Shaped (mtranspose perm arr)

  mconcat l = M_Shaped (mconcat (coerce l))

  mrnf (M_Shaped arr) = mrnf arr

  type ShapeTree (Shaped sh a) = (ShS sh, ShapeTree a)

  mshapeTree (Shaped arr) = first coerce (mshapeTree arr)

  mshapeTreeEq _ (sh1, t1) (sh2, t2) = sh1 == sh2 && mshapeTreeEq (Proxy @a) t1 t2

  mshapeTreeIsEmpty _ (sh, t) = shsSize sh == 0 || mshapeTreeIsEmpty (Proxy @a) t

  mshowShapeTree _ (sh, t) = "(" ++ show sh ++ ", " ++ mshowShapeTree (Proxy @a) t ++ ")"

  marrayStrides (M_Shaped arr) = marrayStrides arr

  mvecsWriteLinear :: forall sh' s. Int -> Shaped sh a -> MixedVecs s sh' (Shaped sh a) -> ST s ()
  mvecsWriteLinear idx (Shaped arr) vecs =
    mvecsWriteLinear idx arr
      (coerce @(MixedVecs s sh' (Shaped sh a)) @(MixedVecs s sh' (Mixed (MapJust sh) a))
         vecs)

  mvecsWritePartialLinear
    :: forall sh1 sh2 s.
       Proxy sh1 -> Int -> Mixed sh2 (Shaped sh a)
    -> MixedVecs s (sh1 ++ sh2) (Shaped sh a)
    -> ST s ()
  mvecsWritePartialLinear proxy idx arr vecs =
    mvecsWritePartialLinear proxy idx
      (coerce @(Mixed sh2 (Shaped sh a))
              @(Mixed sh2 (Mixed (MapJust sh) a))
         arr)
      (coerce @(MixedVecs s (sh1 ++ sh2) (Shaped sh a))
              @(MixedVecs s (sh1 ++ sh2) (Mixed (MapJust sh) a))
         vecs)

  mvecsFreeze :: forall sh' s. IShX sh' -> MixedVecs s sh' (Shaped sh a) -> ST s (Mixed sh' (Shaped sh a))
  mvecsFreeze sh vecs =
    coerce @(Mixed sh' (Mixed (MapJust sh) a))
           @(Mixed sh' (Shaped sh a))
      <$> mvecsFreeze sh
            (coerce @(MixedVecs s sh' (Shaped sh a))
                    @(MixedVecs s sh' (Mixed (MapJust sh) a))
                    vecs)
  mvecsUnsafeFreeze :: forall sh' s. IShX sh' -> MixedVecs s sh' (Shaped sh a) -> ST s (Mixed sh' (Shaped sh a))
  mvecsUnsafeFreeze sh vecs =
    coerce @(Mixed sh' (Mixed (MapJust sh) a))
           @(Mixed sh' (Shaped sh a))
      <$> mvecsUnsafeFreeze sh
            (coerce @(MixedVecs s sh' (Shaped sh a))
                    @(MixedVecs s sh' (Mixed (MapJust sh) a))
                    vecs)

instance (KnownShS sh, KnownElt a) => KnownElt (Shaped sh a) where
  memptyArrayUnsafe :: forall sh'. IShX sh' -> Mixed sh' (Shaped sh a)
  memptyArrayUnsafe sh
    | Dict <- lemKnownMapJust (Proxy @sh)
    = coerce @(Mixed sh' (Mixed (MapJust sh) a)) @(Mixed sh' (Shaped sh a)) $
        memptyArrayUnsafe sh

  mvecsUnsafeNew idx (Shaped arr)
    | Dict <- lemKnownMapJust (Proxy @sh)
    = MV_Shaped <$> mvecsUnsafeNew idx arr

  mvecsReplicate idx (Shaped arr)
    | Dict <- lemKnownMapJust (Proxy @sh)
    = MV_Shaped <$> mvecsReplicate idx arr

  mvecsNewEmpty _
    | Dict <- lemKnownMapJust (Proxy @sh)
    = MV_Shaped <$> mvecsNewEmpty (Proxy @(Mixed (MapJust sh) a))


liftShaped1 :: forall sh a b.
               (Mixed (MapJust sh) a -> Mixed (MapJust sh) b)
            -> Shaped sh a -> Shaped sh b
liftShaped1 = coerce

liftShaped2 :: forall sh a b c.
               (Mixed (MapJust sh) a -> Mixed (MapJust sh) b -> Mixed (MapJust sh) c)
            -> Shaped sh a -> Shaped sh b -> Shaped sh c
liftShaped2 = coerce

instance (NumElt a, PrimElt a) => Num (Shaped sh a) where
  (+) = liftShaped2 (+)
  (-) = liftShaped2 (-)
  (*) = liftShaped2 (*)
  negate = liftShaped1 negate
  abs = liftShaped1 abs
  signum = liftShaped1 signum
  fromInteger = error "Data.Array.Nested.fromInteger: No singletons available, use explicit sreplicatePrim"

instance (FloatElt a, PrimElt a) => Fractional (Shaped sh a) where
  fromRational = error "Data.Array.Nested.fromRational: No singletons available, use explicit sreplicatePrim"
  recip = liftShaped1 recip
  (/) = liftShaped2 (/)

instance (FloatElt a, PrimElt a) => Floating (Shaped sh a) where
  pi = error "Data.Array.Nested.pi: No singletons available, use explicit sreplicatePrim"
  exp = liftShaped1 exp
  log = liftShaped1 log
  sqrt = liftShaped1 sqrt
  (**) = liftShaped2 (**)
  logBase = liftShaped2 logBase
  sin = liftShaped1 sin
  cos = liftShaped1 cos
  tan = liftShaped1 tan
  asin = liftShaped1 asin
  acos = liftShaped1 acos
  atan = liftShaped1 atan
  sinh = liftShaped1 sinh
  cosh = liftShaped1 cosh
  tanh = liftShaped1 tanh
  asinh = liftShaped1 asinh
  acosh = liftShaped1 acosh
  atanh = liftShaped1 atanh
  log1p = liftShaped1 GHC.Float.log1p
  expm1 = liftShaped1 GHC.Float.expm1
  log1pexp = liftShaped1 GHC.Float.log1pexp
  log1mexp = liftShaped1 GHC.Float.log1mexp

squotArray, sremArray :: (IntElt a, PrimElt a) => Shaped sh a -> Shaped sh a -> Shaped sh a
squotArray = liftShaped2 mquotArray
sremArray = liftShaped2 mremArray

satan2Array :: (FloatElt a, PrimElt a) => Shaped sh a -> Shaped sh a -> Shaped sh a
satan2Array = liftShaped2 matan2Array


{-# INLINE sshape #-}
sshape :: forall sh a. Elt a => Shaped sh a -> ShS sh
sshape (Shaped arr) = coerce (mshape arr)
