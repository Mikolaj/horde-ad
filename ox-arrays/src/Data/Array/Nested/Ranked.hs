{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Nested.Ranked (
  Ranked(Ranked),
  rquotArray, rremArray, ratan2Array,
  rshape, rrank,
  module Data.Array.Nested.Ranked,
  liftRanked1, liftRanked2,
) where

import Prelude hiding (mappend, mconcat)

import Data.Array.RankedS qualified as S
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy
import Data.Type.Equality
import Data.Vector.Storable qualified as VS
import Foreign.Storable (Storable)
import GHC.TypeLits
import GHC.TypeNats qualified as TN

import Data.Array.Nested.Convert
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Ranked.Base
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Types
import Data.Array.Strided.Arith
import Data.Array.XArray (XArray(..))
import Data.Array.XArray qualified as X


remptyArray :: KnownElt a => Ranked 1 a
remptyArray = mtoRanked (memptyArray ZSX)

-- | The total number of elements in the array.
rsize :: Elt a => Ranked n a -> Int
rsize = shrSize . rshape

{-# INLINEABLE rindex #-}
rindex :: Elt a => Ranked n a -> IIxR n -> a
rindex (Ranked arr) idx = mindex arr (ixxFromIxR idx)

{-# INLINEABLE rindexPartial #-}
rindexPartial :: forall n m a. Elt a => Ranked (n + m) a -> IIxR n -> Ranked m a
rindexPartial (Ranked arr) idx =
  Ranked (mindexPartial @a @(Replicate n Nothing) @(Replicate m Nothing)
            (castWith (subst2 (lemReplicatePlusApp (ixrRank idx) (Proxy @m) (Proxy @Nothing))) arr)
            (ixxFromIxR idx))

-- | __WARNING__: All values returned from the function must have equal shape.
-- See the documentation of 'mgenerate' for more details; see also
-- 'rgeneratePrim'.
rgenerate :: forall n a. KnownElt a => IShR n -> (IIxR n -> a) -> Ranked n a
rgenerate sh f
  | sn@SNat <- shrRank sh
  , Dict <- lemKnownReplicate sn
  , Refl <- lemRankReplicate sn
  = Ranked (mgenerate (shxFromShR sh) (f . ixrFromIxX))

-- | See 'mgeneratePrim'.
{-# INLINE rgeneratePrim #-}
rgeneratePrim :: forall n a i. (PrimElt a, Num i)
              => IShR n -> (IxR n i -> a) -> Ranked n a
rgeneratePrim sh f =
  let g i = f (ixrFromLinear sh i)
  in rfromVector sh $ VS.generate (shrSize sh) g

-- | See the documentation of 'mlift'.
{-# INLINE rlift #-}
rlift :: forall n1 n2 a. Elt a
      => SNat n2
      -> (forall sh' b. Storable b => StaticShX sh' -> XArray (Replicate n1 Nothing ++ sh') b -> XArray (Replicate n2 Nothing ++ sh') b)
      -> Ranked n1 a -> Ranked n2 a
rlift sn2 f (Ranked arr) = Ranked (mlift (ssxFromSNat sn2) f arr)

-- | See the documentation of 'mlift2'.
{-# INLINE rlift2 #-}
rlift2 :: forall n1 n2 n3 a. Elt a
       => SNat n3
       -> (forall sh' b. Storable b => StaticShX sh' -> XArray (Replicate n1 Nothing ++ sh') b -> XArray (Replicate n2 Nothing ++ sh') b -> XArray (Replicate n3 Nothing ++ sh') b)
       -> Ranked n1 a -> Ranked n2 a -> Ranked n3 a
rlift2 sn3 f (Ranked arr1) (Ranked arr2) = Ranked (mlift2 (ssxFromSNat sn3) f arr1 arr2)

{-# INLINE rsumOuter1PrimP #-}
rsumOuter1PrimP :: forall n a.
                   (Storable a, NumElt a)
                => Ranked (n + 1) (Primitive a) -> Ranked n (Primitive a)
rsumOuter1PrimP (Ranked arr)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = Ranked (msumOuter1PrimP arr)

{-# INLINEABLE rsumOuter1Prim #-}
rsumOuter1Prim :: forall n a. (NumElt a, PrimElt a)
               => Ranked (n + 1) a -> Ranked n a
rsumOuter1Prim = rfromPrimitive . rsumOuter1PrimP . rtoPrimitive

{-# INLINE rsumAllPrimP #-}
rsumAllPrimP :: (Storable a, NumElt a) => Ranked n (Primitive a) -> a
rsumAllPrimP (Ranked arr) = msumAllPrimP arr

{-# INLINE rsumAllPrim #-}
rsumAllPrim :: (PrimElt a, NumElt a) => Ranked n a -> a
rsumAllPrim (Ranked arr) = msumAllPrim arr

rtranspose :: forall n a. Elt a => PermR -> Ranked n a -> Ranked n a
rtranspose perm arr
  | sn@SNat <- rrank arr
  , Dict <- lemKnownReplicate sn
  , length perm <= fromIntegral (natVal (Proxy @n))
  = rlift sn
          (\ssh' -> X.transposeUntyped (natSing @n) ssh' perm)
          arr
  | otherwise
  = error "Data.Array.Nested.rtranspose: Permutation longer than rank of array"

rconcat :: forall n a. Elt a => NonEmpty (Ranked (n + 1) a) -> Ranked (n + 1) a
rconcat
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = coerce mconcat

rappend :: forall n a. Elt a
        => Ranked (n + 1) a -> Ranked (n + 1) a -> Ranked (n + 1) a
rappend arr1 arr2
  | sn@SNat <- rrank arr1
  , Dict <- lemKnownReplicate sn
  , Refl <- lemReplicateSucc @(Nothing @Nat) (SNat @n)
  = coerce (mappend @Nothing @Nothing @(Replicate n Nothing))
      arr1 arr2

rscalar :: Elt a => a -> Ranked 0 a
rscalar x = Ranked (mscalar x)

{-# INLINEABLE rfromVectorP #-}
rfromVectorP :: forall n a. Storable a => IShR n -> VS.Vector a -> Ranked n (Primitive a)
rfromVectorP sh v
  | Dict <- lemKnownReplicate (shrRank sh)
  = Ranked (mfromVectorP (shxFromShR sh) v)

{-# INLINEABLE rfromVector #-}
rfromVector :: forall n a. PrimElt a => IShR n -> VS.Vector a -> Ranked n a
rfromVector sh v = rfromPrimitive (rfromVectorP sh v)

{-# INLINEABLE rtoVectorP #-}
rtoVectorP :: Storable a => Ranked n (Primitive a) -> VS.Vector a
rtoVectorP = coerce mtoVectorP

{-# INLINEABLE rtoVector #-}
rtoVector :: PrimElt a => Ranked n a -> VS.Vector a
rtoVector = coerce mtoVector

-- | All arrays in the list, even subarrays inside @a@, must have the same
-- shape; if they do not, a runtime error will be thrown. See the
-- documentation of 'mgenerate' for more information about this restriction.
--
-- Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'rfromListOuterN' to be able to stream the list.
--
-- If your array is 1-dimensional and contains scalars, use 'rfromList1Prim'.
rfromListOuter :: forall n a. Elt a => NonEmpty (Ranked n a) -> Ranked (n + 1) a
rfromListOuter l
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = Ranked (mfromListOuter (coerce l :: NonEmpty (Mixed (Replicate n Nothing) a)))

-- | See 'rfromListOuter'. If the list does not have the given length, a
-- runtime error is thrown. 'rfromList1PrimN' is faster if applicable.
rfromListOuterN :: forall n a. Elt a => Int -> NonEmpty (Ranked n a) -> Ranked (n + 1) a
rfromListOuterN n l
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = Ranked (mfromListOuterN n (coerce l :: NonEmpty (Mixed (Replicate n Nothing) a)))

-- | Because the length of the 'NonEmpty' list is unknown, its spine must be
-- materialised in memory in order to compute its length. If its length is
-- already known, use 'rfromList1N' to be able to stream the list.
--
-- If the elements are scalars, 'rfromList1Prim' is faster.
rfromList1 :: Elt a => NonEmpty a -> Ranked 1 a
rfromList1 = coerce mfromList1

-- | If the elements are scalars, 'rfromList1PrimN' is faster. A runtime error
-- is thrown if the list length does not match the given length.
rfromList1N :: Elt a => Int -> NonEmpty a -> Ranked 1 a
rfromList1N = coerce mfromList1N

-- | If the elements are scalars, 'rfromListPrimLinear' is faster.
rfromListLinear :: forall n a. Elt a => IShR n -> NonEmpty a -> Ranked n a
rfromListLinear sh l = Ranked (mfromListLinear (shxFromShR sh) l)

-- | Because the length of the list is unknown, its spine must be materialised
-- in memory in order to compute its length. If its length is already known,
-- use 'rfromList1PrimN' to be able to stream the list.
rfromList1Prim :: PrimElt a => [a] -> Ranked 1 a
rfromList1Prim = coerce mfromList1Prim

rfromList1PrimN :: PrimElt a => Int -> [a] -> Ranked 1 a
rfromList1PrimN = coerce mfromList1PrimN

rfromListPrimLinear :: forall n a. PrimElt a => IShR n -> [a] -> Ranked n a
rfromListPrimLinear sh l = Ranked (mfromListPrimLinear (shxFromShR sh) l)

rtoList :: Elt a => Ranked 1 a -> [a]
rtoList = map runScalar . rtoListOuter

rtoListOuter :: forall n a. Elt a => Ranked (n + 1) a -> [Ranked n a]
rtoListOuter (Ranked arr)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = coerce (mtoListOuter @a @Nothing @(Replicate n Nothing) arr)

rtoListLinear :: Elt a => Ranked n a -> [a]
rtoListLinear (Ranked arr) = mtoListLinear arr

rfromOrthotope :: PrimElt a => SNat n -> S.Array n a -> Ranked n a
rfromOrthotope sn arr
  | Refl <- lemRankReplicate sn
  = let xarr = XArray arr
    in Ranked (fromPrimitive (M_Primitive (X.shape (ssxFromSNat sn) xarr) xarr))

rtoOrthotope :: forall a n. PrimElt a => Ranked n a -> S.Array n a
rtoOrthotope (rtoPrimitive -> Ranked (M_Primitive sh (XArray arr)))
  | Refl <- lemRankReplicate (shrRank $ shrFromShX @n sh)
  = arr

runScalar :: Elt a => Ranked 0 a -> a
runScalar arr = rindex arr ZIR

rnest :: forall n m a. Elt a => SNat n -> Ranked (n + m) a -> Ranked n (Ranked m a)
rnest n arr
  | Refl <- lemReplicatePlusApp n (Proxy @m) (Proxy @(Nothing @Nat))
  = coerce (mnest (ssxFromSNat n) (coerce arr))

runNest :: forall n m a. Elt a => Ranked n (Ranked m a) -> Ranked (n + m) a
runNest rarr@(Ranked (M_Ranked (M_Nest _ arr)))
  | Refl <- lemReplicatePlusApp (rrank rarr) (Proxy @m) (Proxy @(Nothing @Nat))
  = Ranked arr

rzip :: (Elt a, Elt b) => Ranked n a -> Ranked n b -> Ranked n (a, b)
rzip = coerce mzip

runzip :: Ranked n (a, b) -> (Ranked n a, Ranked n b)
runzip = coerce munzip

rrerankPrimP :: forall n1 n2 n a b. (Storable a, Storable b)
             => IShR n2
             -> (Ranked n1 (Primitive a) -> Ranked n2 (Primitive b))
             -> Ranked n (Ranked n1 (Primitive a)) -> Ranked n (Ranked n2 (Primitive b))
rrerankPrimP sh2 f (Ranked (M_Ranked arr))
  = Ranked (M_Ranked (mrerankPrimP (shxFromShR sh2)
                                   (\a -> let Ranked r = f (Ranked a) in r)
                                   arr))

-- | If there is a zero-sized dimension in the @n@-prefix of the shape of the
-- input array, then there is no way to deduce the full shape of the output
-- array (more precisely, the @n2@ part): that could only come from calling
-- @f@, and there are no subarrays to call @f@ on. @orthotope@ errors out in
-- this case; we choose to fill the @n2@ part of the output shape with zeros.
--
-- For example, if:
--
-- @
-- arr :: Ranked 3 (Ranked 2 Int)   -- outer array shape [3, 0, 4]; inner shape [2, 21]
-- f :: Ranked 2 Int -> Ranked 3 Float
-- @
--
-- then:
--
-- @
-- rrerank _ f arr :: Ranked 3 (Ranked 3 Float)
-- @
--
-- and the inner arrays of the result will have shape @[0, 0, 0]@. We don't
-- know if @f@ intended to return an array with all-zero shape here (it
-- probably didn't), but there is no better number to put here absent a
-- subarray of the input to pass to @f@.
rrerankPrim :: forall n1 n2 n a b. (PrimElt a, PrimElt b)
            => IShR n2
            -> (Ranked n1 a -> Ranked n2 b)
            -> Ranked n (Ranked n1 a) -> Ranked n (Ranked n2 b)
rrerankPrim sh2 f (Ranked (M_Ranked arr)) =
  Ranked (M_Ranked (mrerankPrim (shxFromShR sh2)
                                (\a -> let Ranked r = f (Ranked a) in r)
                                arr))

rreplicate :: forall n m a. Elt a
           => IShR n -> Ranked m a -> Ranked (n + m) a
rreplicate sh (Ranked arr)
  | Refl <- lemReplicatePlusApp (shrRank sh) (Proxy @m) (Proxy @(Nothing @Nat))
  = Ranked (mreplicate (shxFromShR sh) arr)

rreplicatePrimP :: forall n a. Storable a => IShR n -> a -> Ranked n (Primitive a)
rreplicatePrimP sh x
  | Dict <- lemKnownReplicate (shrRank sh)
  = Ranked (mreplicatePrimP (shxFromShR sh) x)

rreplicatePrim :: forall n a. PrimElt a
               => IShR n -> a -> Ranked n a
rreplicatePrim sh x = rfromPrimitive (rreplicatePrimP sh x)

rslice :: forall n a. Elt a => Int -> Int -> Ranked (n + 1) a -> Ranked (n + 1) a
rslice i n (Ranked arr)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = Ranked (msliceN i n arr)

rrev1 :: forall n a. Elt a => Ranked (n + 1) a -> Ranked (n + 1) a
rrev1 (Ranked arr)
  | Refl <- lemReplicateSucc @(Nothing @Nat) (Proxy @n)
  = Ranked (mrev1 arr)

rreshape :: forall n n' a. Elt a
         => IShR n' -> Ranked n a -> Ranked n' a
rreshape sh' rarr@(Ranked arr)
  | Dict <- lemKnownReplicate (rrank rarr)
  , Dict <- lemKnownReplicate (shrRank sh')
  = Ranked (mreshape (shxFromShR sh') arr)

rflatten :: Elt a => Ranked n a -> Ranked 1 a
rflatten (Ranked arr) = mtoRanked (mflatten arr)

riota :: (Enum a, PrimElt a) => Int -> Ranked 1 a
riota n = TN.withSomeSNat (fromIntegral n) $ mtoRanked . miota

-- | Throws if the array is empty.
rminIndexPrim :: (PrimElt a, NumElt a) => Ranked n a -> IIxR n
rminIndexPrim rarr@(Ranked arr)
  | Refl <- lemRankReplicate (rrank (rtoPrimitive rarr))
  = ixrFromIxX (mminIndexPrim arr)

-- | Throws if the array is empty.
rmaxIndexPrim :: (PrimElt a, NumElt a) => Ranked n a -> IIxR n
rmaxIndexPrim rarr@(Ranked arr)
  | Refl <- lemRankReplicate (rrank (rtoPrimitive rarr))
  = ixrFromIxX (mmaxIndexPrim arr)

{-# INLINEABLE rdot1Inner #-}
rdot1Inner :: forall n a. (PrimElt a, NumElt a) => Ranked (n + 1) a -> Ranked (n + 1) a -> Ranked n a
rdot1Inner arr1 arr2
  | SNat <- rrank arr1
  , Refl <- lemReplicatePlusApp (SNat @n) (Proxy @1) (Proxy @(Nothing @Nat))
  = coerce (mdot1Inner (Proxy @(Nothing @Nat))) arr1 arr2

-- | This has a temporary, suboptimal implementation in terms of 'mflatten'.
-- Prefer 'rdot1Inner' if applicable.
{-# INLINE rdot #-}
rdot :: (PrimElt a, NumElt a) => Ranked n a -> Ranked n a -> a
rdot = coerce mdot

rtoXArrayPrimP :: Ranked n (Primitive a) -> (IShR n, XArray (Replicate n Nothing) a)
rtoXArrayPrimP (Ranked arr) = first shrFromShX (mtoXArrayPrimP arr)

rtoXArrayPrim :: PrimElt a => Ranked n a -> (IShR n, XArray (Replicate n Nothing) a)
rtoXArrayPrim (Ranked arr) = first shrFromShX (mtoXArrayPrim arr)

rfromXArrayPrimP :: SNat n -> XArray (Replicate n Nothing) a -> Ranked n (Primitive a)
rfromXArrayPrimP sn arr = Ranked (mfromXArrayPrimP (ssxFromShX (X.shape (ssxFromSNat sn) arr)) arr)

rfromXArrayPrim :: PrimElt a => SNat n -> XArray (Replicate n Nothing) a -> Ranked n a
rfromXArrayPrim sn arr = Ranked (mfromXArrayPrim (ssxFromShX (X.shape (ssxFromSNat sn) arr)) arr)

rfromPrimitive :: PrimElt a => Ranked n (Primitive a) -> Ranked n a
rfromPrimitive (Ranked arr) = Ranked (fromPrimitive arr)

rtoPrimitive :: PrimElt a => Ranked n a -> Ranked n (Primitive a)
rtoPrimitive (Ranked arr) = Ranked (toPrimitive arr)
