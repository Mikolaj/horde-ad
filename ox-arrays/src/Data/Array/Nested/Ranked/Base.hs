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
module Data.Array.Nested.Ranked.Base where

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
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Types
import Data.Array.Strided.Arith
import Data.Array.XArray (XArray(..))


-- | A rank-typed array: the number of dimensions of the array (its /rank/) is
-- represented on the type level as a 'Nat'.
--
-- Valid elements of a ranked arrays are described by the 'Elt' type class.
-- Because 'Ranked' itself is also an instance of 'Elt', nested arrays are
-- supported (and are represented as a single, flattened, struct-of-arrays
-- array internally).
--
-- 'Ranked' is a newtype around a 'Mixed' of 'Nothing's.
type Ranked :: Nat -> Type -> Type
newtype Ranked n a = Ranked (Mixed (Replicate n Nothing) a)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (Mixed (Replicate n Nothing) a) => Show (Ranked n a)
#endif
deriving instance Eq (Mixed (Replicate n Nothing) a) => Eq (Ranked n a)
deriving instance Ord (Mixed (Replicate n Nothing) a) => Ord (Ranked n a)

#ifndef OXAR_DEFAULT_SHOW_INSTANCES
instance (Show a, Elt a) => Show (Ranked n a) where
  showsPrec d arr@(Ranked marr) =
    let sh = show (shrToList (rshape arr))
    in showsMixedArray ("rfromListLinear " ++ sh) ("rreplicate " ++ sh) d marr
#endif

instance Elt a => NFData (Ranked n a) where
  rnf (Ranked arr) = rnf arr

-- just unwrap the newtype and defer to the general instance for nested arrays
newtype instance Mixed sh (Ranked n a) = M_Ranked (Mixed sh (Mixed (Replicate n Nothing) a))
  deriving (Generic)
#ifdef OXAR_DEFAULT_SHOW_INSTANCES
deriving instance Show (Mixed sh (Mixed (Replicate n Nothing) a)) => Show (Mixed sh (Ranked n a))
#endif

deriving instance Eq (Mixed sh (Mixed (Replicate n Nothing) a)) => Eq (Mixed sh (Ranked n a))

newtype instance MixedVecs s sh (Ranked n a) = MV_Ranked (MixedVecs s sh (Mixed (Replicate n Nothing) a))

-- 'Ranked' and 'Shaped' can already be used at the top level of an array nest;
-- these instances allow them to also be used as elements of arrays, thus
-- making them first-class in the API.
instance Elt a => Elt (Ranked n a) where
  {-# INLINE mshape #-}
  mshape (M_Ranked arr) = mshape arr
  {-# INLINE mindex #-}
  mindex (M_Ranked arr) i = Ranked (mindex arr i)

  {-# INLINE mindexPartial #-}
  mindexPartial :: forall sh sh'. Mixed (sh ++ sh') (Ranked n a) -> IIxX sh -> Mixed sh' (Ranked n a)
  mindexPartial (M_Ranked arr) i =
    coerce @(Mixed sh' (Mixed (Replicate n Nothing) a)) @(Mixed sh' (Ranked n a)) $
        mindexPartial arr i

  mscalar (Ranked x) = M_Ranked (M_Nest ZSX x)

  mfromListOuterSN :: SNat m -> NonEmpty (Mixed sh (Ranked n a)) -> Mixed (Just m : sh) (Ranked n a)
  mfromListOuterSN sn l = M_Ranked (mfromListOuterSN sn (coerce l))

  mtoListOuter :: forall m sh. Mixed (m : sh) (Ranked n a) -> [Mixed sh (Ranked n a)]
  mtoListOuter (M_Ranked arr) =
    coerce @[Mixed sh (Mixed (Replicate n 'Nothing) a)] @[Mixed sh (Ranked n a)] (mtoListOuter arr)

  {-# INLINE mlift #-}
  mlift :: forall sh1 sh2.
           StaticShX sh2
        -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b)
        -> Mixed sh1 (Ranked n a) -> Mixed sh2 (Ranked n a)
  mlift ssh2 f (M_Ranked arr) =
    coerce @(Mixed sh2 (Mixed (Replicate n Nothing) a)) @(Mixed sh2 (Ranked n a)) $
      mlift ssh2 f arr

  {-# INLINE mlift2 #-}
  mlift2 :: forall sh1 sh2 sh3.
            StaticShX sh3
         -> (forall sh' b. Storable b => StaticShX sh' -> XArray (sh1 ++ sh') b -> XArray (sh2 ++ sh') b -> XArray (sh3 ++ sh') b)
         -> Mixed sh1 (Ranked n a) -> Mixed sh2 (Ranked n a) -> Mixed sh3 (Ranked n a)
  mlift2 ssh3 f (M_Ranked arr1) (M_Ranked arr2) =
    coerce @(Mixed sh3 (Mixed (Replicate n Nothing) a)) @(Mixed sh3 (Ranked n a)) $
      mlift2 ssh3 f arr1 arr2

  {-# INLINE mliftL #-}
  mliftL :: forall sh1 sh2.
            StaticShX sh2
         -> (forall sh' b. Storable b => StaticShX sh' -> NonEmpty (XArray (sh1 ++ sh') b) -> NonEmpty (XArray (sh2 ++ sh') b))
         -> NonEmpty (Mixed sh1 (Ranked n a)) -> NonEmpty (Mixed sh2 (Ranked n a))
  mliftL ssh2 f l =
    coerce @(NonEmpty (Mixed sh2 (Mixed (Replicate n Nothing) a)))
           @(NonEmpty (Mixed sh2 (Ranked n a))) $
      mliftL ssh2 f (coerce l)

  mcastPartial ssh1 ssh2 psh' (M_Ranked arr) = M_Ranked (mcastPartial ssh1 ssh2 psh' arr)

  mtranspose perm (M_Ranked arr) = M_Ranked (mtranspose perm arr)

  mconcat l = M_Ranked (mconcat (coerce l))

  mrnf (M_Ranked arr) = mrnf arr

  type ShapeTree (Ranked n a) = (IShR n, ShapeTree a)

  mshapeTree (Ranked arr) = first coerce (mshapeTree arr)

  mshapeTreeEq _ (sh1, t1) (sh2, t2) = sh1 == sh2 && mshapeTreeEq (Proxy @a) t1 t2

  mshapeTreeIsEmpty _ (sh, t) = shrSize sh == 0 || mshapeTreeIsEmpty (Proxy @a) t

  mshowShapeTree _ (sh, t) = "(" ++ show sh ++ ", " ++ mshowShapeTree (Proxy @a) t ++ ")"

  marrayStrides (M_Ranked arr) = marrayStrides arr

  mvecsWriteLinear :: forall sh s. Int -> Ranked n a -> MixedVecs s sh (Ranked n a) -> ST s ()
  mvecsWriteLinear idx (Ranked arr) vecs =
    mvecsWriteLinear idx arr
      (coerce @(MixedVecs s sh (Ranked n a)) @(MixedVecs s sh (Mixed (Replicate n Nothing) a))
         vecs)

  mvecsWritePartialLinear
    :: forall sh sh' s.
       Proxy sh -> Int -> Mixed sh' (Ranked n a)
    -> MixedVecs s (sh ++ sh') (Ranked n a)
    -> ST s ()
  mvecsWritePartialLinear proxy idx arr vecs =
    mvecsWritePartialLinear proxy idx
      (coerce @(Mixed sh' (Ranked n a))
              @(Mixed sh' (Mixed (Replicate n Nothing) a))
         arr)
      (coerce @(MixedVecs s (sh ++ sh') (Ranked n a))
              @(MixedVecs s (sh ++ sh') (Mixed (Replicate n Nothing) a))
         vecs)

  mvecsFreeze :: forall sh s. IShX sh -> MixedVecs s sh (Ranked n a) -> ST s (Mixed sh (Ranked n a))
  mvecsFreeze sh vecs =
    coerce @(Mixed sh (Mixed (Replicate n Nothing) a))
           @(Mixed sh (Ranked n a))
      <$> mvecsFreeze sh
            (coerce @(MixedVecs s sh (Ranked n a))
                    @(MixedVecs s sh (Mixed (Replicate n Nothing) a))
                    vecs)
  mvecsUnsafeFreeze :: forall sh s. IShX sh -> MixedVecs s sh (Ranked n a) -> ST s (Mixed sh (Ranked n a))
  mvecsUnsafeFreeze sh vecs =
    coerce @(Mixed sh (Mixed (Replicate n Nothing) a))
           @(Mixed sh (Ranked n a))
      <$> mvecsUnsafeFreeze sh
            (coerce @(MixedVecs s sh (Ranked n a))
                    @(MixedVecs s sh (Mixed (Replicate n Nothing) a))
                    vecs)

instance (KnownNat n, KnownElt a) => KnownElt (Ranked n a) where
  memptyArrayUnsafe :: forall sh. IShX sh -> Mixed sh (Ranked n a)
  memptyArrayUnsafe sh
    | Dict <- lemKnownReplicate (SNat @n)
    = coerce @(Mixed sh (Mixed (Replicate n Nothing) a)) @(Mixed sh (Ranked n a)) $
        memptyArrayUnsafe sh

  mvecsUnsafeNew idx (Ranked arr)
    | Dict <- lemKnownReplicate (SNat @n)
    = MV_Ranked <$> mvecsUnsafeNew idx arr

  mvecsReplicate idx (Ranked arr)
    | Dict <- lemKnownReplicate (SNat @n)
    = MV_Ranked <$> mvecsReplicate idx arr

  mvecsNewEmpty _
    | Dict <- lemKnownReplicate (SNat @n)
    = MV_Ranked <$> mvecsNewEmpty (Proxy @(Mixed (Replicate n Nothing) a))


liftRanked1 :: forall n a b.
               (Mixed (Replicate n Nothing) a -> Mixed (Replicate n Nothing) b)
            -> Ranked n a -> Ranked n b
liftRanked1 = coerce

liftRanked2 :: forall n a b c.
               (Mixed (Replicate n Nothing) a -> Mixed (Replicate n Nothing) b -> Mixed (Replicate n Nothing) c)
            -> Ranked n a -> Ranked n b -> Ranked n c
liftRanked2 = coerce

instance (NumElt a, PrimElt a) => Num (Ranked n a) where
  (+) = liftRanked2 (+)
  (-) = liftRanked2 (-)
  (*) = liftRanked2 (*)
  negate = liftRanked1 negate
  abs = liftRanked1 abs
  signum = liftRanked1 signum
  fromInteger = error "Data.Array.Nested(Ranked).fromInteger: No singletons available, use explicit rreplicatePrim"

instance (FloatElt a, PrimElt a) => Fractional (Ranked n a) where
  fromRational _ = error "Data.Array.Nested(Ranked).fromRational: No singletons available, use explicit rreplicatePrim"
  recip = liftRanked1 recip
  (/) = liftRanked2 (/)

instance (FloatElt a, PrimElt a) => Floating (Ranked n a) where
  pi = error "Data.Array.Nested(Ranked).pi: No singletons available, use explicit rreplicatePrim"
  exp = liftRanked1 exp
  log = liftRanked1 log
  sqrt = liftRanked1 sqrt
  (**) = liftRanked2 (**)
  logBase = liftRanked2 logBase
  sin = liftRanked1 sin
  cos = liftRanked1 cos
  tan = liftRanked1 tan
  asin = liftRanked1 asin
  acos = liftRanked1 acos
  atan = liftRanked1 atan
  sinh = liftRanked1 sinh
  cosh = liftRanked1 cosh
  tanh = liftRanked1 tanh
  asinh = liftRanked1 asinh
  acosh = liftRanked1 acosh
  atanh = liftRanked1 atanh
  log1p = liftRanked1 GHC.Float.log1p
  expm1 = liftRanked1 GHC.Float.expm1
  log1pexp = liftRanked1 GHC.Float.log1pexp
  log1mexp = liftRanked1 GHC.Float.log1mexp

rquotArray, rremArray :: (IntElt a, PrimElt a) => Ranked n a -> Ranked n a -> Ranked n a
rquotArray = liftRanked2 mquotArray
rremArray = liftRanked2 mremArray

ratan2Array :: (FloatElt a, PrimElt a) => Ranked n a -> Ranked n a -> Ranked n a
ratan2Array = liftRanked2 matan2Array


{-# INLINE rshape #-}
rshape :: Elt a => Ranked n a -> IShR n
rshape (Ranked arr) = coerce (mshape arr)

rrank :: Elt a => Ranked n a -> SNat n
rrank = shrRank . rshape
