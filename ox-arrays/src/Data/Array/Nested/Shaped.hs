{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Nested.Shaped (
  Shaped(Shaped),
  squotArray, sremArray, satan2Array,
  sshape,
  module Data.Array.Nested.Shaped,
  liftShaped1, liftShaped2,
) where

import Prelude hiding (mappend, mconcat)

import Data.Array.Internal.RankedG qualified as RG
import Data.Array.Internal.RankedS qualified as RS
import Data.Array.Internal.ShapedG qualified as SG
import Data.Array.Internal.ShapedS qualified as SS
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy
import Data.Type.Equality
import Data.Vector.Storable qualified as VS
import Foreign.Storable (Storable)
import GHC.TypeLits

import Data.Array.Nested.Convert
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Shaped.Base
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types
import Data.Array.Strided.Arith
import Data.Array.XArray (XArray)
import Data.Array.XArray qualified as X


semptyArray :: forall sh a. KnownElt a => ShS sh -> Shaped (0 : sh) a
semptyArray sh = Shaped (memptyArray (shxFromShS sh))

srank :: Elt a => Shaped sh a -> SNat (Rank sh)
srank = shsRank . sshape

-- | The total number of elements in the array.
ssize :: Elt a => Shaped sh a -> Int
ssize = shsSize . sshape

{-# INLINEABLE sindex #-}
sindex :: Elt a => Shaped sh a -> IIxS sh -> a
sindex (Shaped arr) idx = mindex arr (ixxFromIxS idx)

shsTakeIx :: Proxy sh' -> ShS (sh ++ sh') -> IxS sh i -> ShS sh
shsTakeIx _ _ ZIS = ZSS
shsTakeIx p sh (_ :.$ idx) = case sh of n :$$ sh' -> n :$$ shsTakeIx p sh' idx

{-# INLINEABLE sindexPartial #-}
sindexPartial :: forall sh1 sh2 a. Elt a => Shaped (sh1 ++ sh2) a -> IIxS sh1 -> Shaped sh2 a
sindexPartial sarr@(Shaped arr) idx =
  Shaped (mindexPartial @a @(MapJust sh1) @(MapJust sh2)
            (castWith (subst2 (lemMapJustApp (shsTakeIx (Proxy @sh2) (sshape sarr) idx) (Proxy @sh2))) arr)
            (ixxFromIxS idx))

-- | __WARNING__: All values returned from the function must have equal shape.
-- See the documentation of 'mgenerate' for more details.
sgenerate :: forall sh a. KnownElt a => ShS sh -> (IIxS sh -> a) -> Shaped sh a
sgenerate sh f = Shaped (mgenerate (shxFromShS sh) (f . ixsFromIxX))

-- | See 'mgeneratePrim'.
{-# INLINE sgeneratePrim #-}
sgeneratePrim :: forall sh a i. (PrimElt a, Num i)
              => ShS sh -> (IxS sh i -> a) -> Shaped sh a
sgeneratePrim sh f =
  let g i = f (ixsFromLinear sh i)
  in sfromVector sh $ VS.generate (shsSize sh) g

-- | See the documentation of 'mlift'.
{-# INLINE slift #-}
slift :: forall sh1 sh2 a. Elt a
      => ShS sh2
      -> (forall sh' b. Storable b => StaticShX sh' -> XArray (MapJust sh1 ++ sh') b -> XArray (MapJust sh2 ++ sh') b)
      -> Shaped sh1 a -> Shaped sh2 a
slift sh2 f (Shaped arr) = Shaped (mlift (ssxFromShX (shxFromShS sh2)) f arr)

-- | See the documentation of 'mlift'.
{-# INLINE slift2 #-}
slift2 :: forall sh1 sh2 sh3 a. Elt a
       => ShS sh3
       -> (forall sh' b. Storable b => StaticShX sh' -> XArray (MapJust sh1 ++ sh') b -> XArray (MapJust sh2 ++ sh') b -> XArray (MapJust sh3 ++ sh') b)
       -> Shaped sh1 a -> Shaped sh2 a -> Shaped sh3 a
slift2 sh3 f (Shaped arr1) (Shaped arr2) = Shaped (mlift2 (ssxFromShX (shxFromShS sh3)) f arr1 arr2)

{-# INLINE ssumOuter1PrimP #-}
ssumOuter1PrimP :: forall sh n a. (Storable a, NumElt a)
                => Shaped (n : sh) (Primitive a) -> Shaped sh (Primitive a)
ssumOuter1PrimP (Shaped arr) = Shaped (msumOuter1PrimP arr)

{-# INLINEABLE ssumOuter1Prim #-}
ssumOuter1Prim :: forall sh n a. (NumElt a, PrimElt a)
               => Shaped (n : sh) a -> Shaped sh a
ssumOuter1Prim = sfromPrimitive . ssumOuter1PrimP . stoPrimitive

{-# INLINE ssumAllPrimP #-}
ssumAllPrimP :: (PrimElt a, NumElt a) => Shaped n (Primitive a) -> a
ssumAllPrimP (Shaped arr) = msumAllPrimP arr

{-# INLINE ssumAllPrim #-}
ssumAllPrim :: (PrimElt a, NumElt a) => Shaped n a -> a
ssumAllPrim (Shaped arr) = msumAllPrim arr

stranspose :: forall is sh a. (IsPermutation is, Rank is <= Rank sh, Elt a)
           => Perm is -> Shaped sh a -> Shaped (PermutePrefix is sh) a
stranspose perm sarr@(Shaped arr)
  | Refl <- lemRankMapJust (sshape sarr)
  , Refl <- lemTakeLenMapJust perm (sshape sarr)
  , Refl <- lemDropLenMapJust perm (sshape sarr)
  , Refl <- lemPermuteMapJust perm (shsTakeLen perm (sshape sarr))
  , Refl <- lemMapJustApp (shsPermute perm (shsTakeLen perm (sshape sarr))) (Proxy @(DropLen is sh))
  = Shaped (mtranspose perm arr)

sappend :: Elt a => Shaped (n : sh) a -> Shaped (m : sh) a -> Shaped (n + m : sh) a
sappend = coerce mappend

sscalar :: Elt a => a -> Shaped '[] a
sscalar x = Shaped (mscalar x)

{-# INLINEABLE sfromVectorP #-}
sfromVectorP :: Storable a => ShS sh -> VS.Vector a -> Shaped sh (Primitive a)
sfromVectorP sh v = Shaped (mfromVectorP (shxFromShS sh) v)

{-# INLINEABLE sfromVector #-}
sfromVector :: PrimElt a => ShS sh -> VS.Vector a -> Shaped sh a
sfromVector sh v = sfromPrimitive (sfromVectorP sh v)

{-# INLINEABLE stoVectorP #-}
stoVectorP :: Storable a => Shaped sh (Primitive a) -> VS.Vector a
stoVectorP = coerce mtoVectorP

{-# INLINEABLE stoVector #-}
stoVector :: PrimElt a => Shaped sh a -> VS.Vector a
stoVector = coerce mtoVector

-- | All arrays in the list, even subarrays inside @a@, must have the same
-- shape; if they do not, a runtime error will be thrown. See the
-- documentation of 'mgenerate' for more information about this restriction.
--
-- Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'sfromListOuterSN' to be able to stream the list.
--
-- If your array is 1-dimensional and contains scalars, use 'sfromList1Prim'.
sfromListOuter :: Elt a => SNat n -> NonEmpty (Shaped sh a) -> Shaped (n : sh) a
sfromListOuter = coerce mfromListOuterSN

-- | Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'sfromList1SN' to be able to stream the list.
--
-- If the elements are scalars, 'sfromList1Prim' is faster.
sfromList1 :: Elt a => SNat n -> NonEmpty a -> Shaped '[n] a
sfromList1 = coerce mfromList1SN

-- | If the elements are scalars, 'sfromListPrimLinear' is faster.
sfromListLinear :: forall sh a. Elt a => ShS sh -> NonEmpty a -> Shaped sh a
sfromListLinear sh l = Shaped (mfromListLinear (shxFromShS sh) l)

-- | Because the length of the list is unknown, its spine must be materialised
-- in memory in order to compute its length. If its length is already known,
-- use 'sfromList1PrimN' to be able to stream the list.
sfromList1Prim :: forall n a. PrimElt a => SNat n -> [a] -> Shaped '[n] a
sfromList1Prim = coerce mfromList1PrimSN

sfromListPrimLinear :: forall sh a. PrimElt a => ShS sh -> [a] -> Shaped sh a
sfromListPrimLinear sh l = Shaped (mfromListPrimLinear (shxFromShS sh) l)

stoList :: Elt a => Shaped '[n] a -> [a]
stoList = map sunScalar . stoListOuter

stoListOuter :: Elt a => Shaped (n : sh) a -> [Shaped sh a]
stoListOuter (Shaped arr) = coerce (mtoListOuter arr)

stoListLinear :: Elt a => Shaped sh a -> [a]
stoListLinear (Shaped arr) = mtoListLinear arr

sfromOrthotope :: PrimElt a => ShS sh -> SS.Array sh a -> Shaped sh a
sfromOrthotope sh (SS.A (SG.A arr)) =
  Shaped (fromPrimitive (M_Primitive (shxFromShS sh) (X.XArray (RS.A (RG.A (shsToList sh) arr)))))

stoOrthotope :: PrimElt a => Shaped sh a -> SS.Array sh a
stoOrthotope (stoPrimitive -> Shaped (M_Primitive _ (X.XArray (RS.A (RG.A _ arr))))) = SS.A (SG.A arr)

sunScalar :: Elt a => Shaped '[] a -> a
sunScalar arr = sindex arr ZIS

snest :: forall sh sh' a. Elt a => ShS sh -> Shaped (sh ++ sh') a -> Shaped sh (Shaped sh' a)
snest sh arr
  | Refl <- lemMapJustApp sh (Proxy @sh')
  = coerce (mnest (ssxFromShX (shxFromShS sh)) (coerce arr))

sunNest :: forall sh sh' a. Elt a => Shaped sh (Shaped sh' a) -> Shaped (sh ++ sh') a
sunNest sarr@(Shaped (M_Shaped (M_Nest _ arr)))
  | Refl <- lemMapJustApp (sshape sarr) (Proxy @sh')
  = Shaped arr

szip :: (Elt a, Elt b) => Shaped sh a -> Shaped sh b -> Shaped sh (a, b)
szip = coerce mzip

sunzip :: Shaped sh (a, b) -> (Shaped sh a, Shaped sh b)
sunzip = coerce munzip

srerankPrimP :: forall sh1 sh2 sh a b. (Storable a, Storable b)
             => ShS sh2
             -> (Shaped sh1 (Primitive a) -> Shaped sh2 (Primitive b))
             -> Shaped sh (Shaped sh1 (Primitive a)) -> Shaped sh (Shaped sh2 (Primitive b))
srerankPrimP sh2 f (Shaped (M_Shaped arr))
  = Shaped (M_Shaped (mrerankPrimP (shxFromShS sh2)
                                   (\a -> let Shaped r = f (Shaped a) in r)
                                   arr))

-- | See the caveats at 'mrerankPrim'.
srerankPrim :: forall sh1 sh2 sh a b. (PrimElt a, PrimElt b)
            => ShS sh2
            -> (Shaped sh1 a -> Shaped sh2 b)
            -> Shaped sh (Shaped sh1 a) -> Shaped sh (Shaped sh2 b)
srerankPrim sh2 f (Shaped (M_Shaped arr)) =
  Shaped (M_Shaped (mrerankPrim (shxFromShS sh2)
                                (\a -> let Shaped r = f (Shaped a) in r)
                                arr))

sreplicate :: forall sh sh' a. Elt a => ShS sh -> Shaped sh' a -> Shaped (sh ++ sh') a
sreplicate sh (Shaped arr)
  | Refl <- lemMapJustApp sh (Proxy @sh')
  = Shaped (mreplicate (shxFromShS sh) arr)

sreplicatePrimP :: forall sh a. Storable a => ShS sh -> a -> Shaped sh (Primitive a)
sreplicatePrimP sh x = Shaped (mreplicatePrimP (shxFromShS sh) x)

sreplicatePrim :: forall sh a. PrimElt a => ShS sh -> a -> Shaped sh a
sreplicatePrim sh x = sfromPrimitive (sreplicatePrimP sh x)

sslice :: Elt a => SNat i -> SNat n -> Shaped (i + n + k : sh) a -> Shaped (n : sh) a
sslice i n@SNat arr =
  let _ :$$ sh = sshape arr
  in slift (n :$$ sh) (\_ -> X.slice i n) arr

srev1 :: Elt a => Shaped (n : sh) a -> Shaped (n : sh) a
srev1 arr = slift (sshape arr) (\_ -> X.rev1) arr

sreshape :: (Elt a, Product sh ~ Product sh') => ShS sh' -> Shaped sh a -> Shaped sh' a
sreshape sh' (Shaped arr) = Shaped (mreshape (shxFromShS sh') arr)

sflatten :: Elt a => Shaped sh a -> Shaped '[Product sh] a
sflatten arr = sreshape (shsProduct (sshape arr) :$$ ZSS) arr

siota :: (Enum a, PrimElt a) => SNat n -> Shaped '[n] a
siota sn = Shaped (miota sn)

-- | Throws if the array is empty.
sminIndexPrim :: (PrimElt a, NumElt a) => Shaped sh a -> IIxS sh
sminIndexPrim (Shaped arr) = ixsFromIxX (mminIndexPrim arr)

-- | Throws if the array is empty.
smaxIndexPrim :: (PrimElt a, NumElt a) => Shaped sh a -> IIxS sh
smaxIndexPrim (Shaped arr) = ixsFromIxX (mmaxIndexPrim arr)

{-# INLINEABLE sdot1Inner #-}
sdot1Inner :: forall sh n a. (PrimElt a, NumElt a)
           => Proxy n -> Shaped (sh ++ '[n]) a -> Shaped (sh ++ '[n]) a -> Shaped sh a
sdot1Inner Proxy sarr1@(Shaped arr1) (Shaped arr2)
  | Refl <- lemInitApp (Proxy @sh) (Proxy @n)
  , Refl <- lemLastApp (Proxy @sh) (Proxy @n)
  = case sshape sarr1 of
      _ :$$ _
        | Refl <- lemMapJustApp (shsInit (sshape sarr1)) (Proxy @'[n])
        -> Shaped (mdot1Inner (Proxy @(Just n)) arr1 arr2)
      _ -> error "unreachable"

{-# INLINE sdot #-}
-- | This has a temporary, suboptimal implementation in terms of 'mflatten'.
-- Prefer 'sdot1Inner' if applicable.
sdot :: (PrimElt a, NumElt a) => Shaped sh a -> Shaped sh a -> a
sdot = coerce mdot

stoXArrayPrimP :: Shaped sh (Primitive a) -> (ShS sh, XArray (MapJust sh) a)
stoXArrayPrimP (Shaped arr) = first shsFromShX (mtoXArrayPrimP arr)

stoXArrayPrim :: PrimElt a => Shaped sh a -> (ShS sh, XArray (MapJust sh) a)
stoXArrayPrim (Shaped arr) = first shsFromShX (mtoXArrayPrim arr)

sfromXArrayPrimP :: ShS sh -> XArray (MapJust sh) a -> Shaped sh (Primitive a)
sfromXArrayPrimP sh arr = Shaped (mfromXArrayPrimP (ssxFromShX (shxFromShS sh)) arr)

sfromXArrayPrim :: PrimElt a => ShS sh -> XArray (MapJust sh) a -> Shaped sh a
sfromXArrayPrim sh arr = Shaped (mfromXArrayPrim (ssxFromShX (shxFromShS sh)) arr)

sfromPrimitive :: PrimElt a => Shaped sh (Primitive a) -> Shaped sh a
sfromPrimitive (Shaped arr) = Shaped (fromPrimitive arr)

stoPrimitive :: PrimElt a => Shaped sh a -> Shaped sh (Primitive a)
stoPrimitive (Shaped arr) = Shaped (toPrimitive arr)
