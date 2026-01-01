{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.XArray where

import Control.DeepSeq (NFData)
import Control.Monad (foldM)
import Control.Monad.ST
import Data.Array.Internal qualified as OI
import Data.Array.Internal.RankedG qualified as ORG
import Data.Array.Internal.RankedS qualified as ORS
import Data.Array.RankedS qualified as S
import Data.Coerce
import Data.Foldable (toList)
import Data.Kind
import Data.List.NonEmpty (NonEmpty)
import Data.Proxy
import Data.Type.Equality
import Data.Type.Ord
import Data.Vector.Generic.Checked qualified as VGC
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Foreign.Storable (Storable)
import GHC.Generics (Generic)
import GHC.TypeLits
#if !MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
import Unsafe.Coerce (unsafeCoerce)
#endif

import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Types
import Data.Array.Strided.Orthotope


type XArray :: [Maybe Nat] -> Type -> Type
newtype XArray sh a = XArray (S.Array (Rank sh) a)
  deriving (Show, Eq, Ord, Generic)

instance NFData (XArray sh a)


shape :: forall sh a. StaticShX sh -> XArray sh a -> IShX sh
shape = \ssh (XArray arr) -> go ssh (S.shapeL arr)
  where
    go :: StaticShX sh' -> [Int] -> IShX sh'
    go ZKX [] = ZSX
    go (n :!% ssh) (i : l) = fromSMayNat (\_ -> SUnknown i) SKnown n :$% go ssh l
    go _ _ = error "Invalid shapeL"

{-# INLINEABLE fromVector #-}
fromVector :: forall sh a. Storable a => IShX sh -> VS.Vector a -> XArray sh a
fromVector sh v
  | Dict <- lemKnownNatRank sh
  = XArray (S.fromVector (shxToList sh) v)

toVector :: Storable a => XArray sh a -> VS.Vector a
toVector (XArray arr) = S.toVector arr

-- | This allows observing the strides in the underlying orthotope array. This
-- can be useful for optimisation, but should be considered an implementation
-- detail: strides may change in new versions of this library without notice.
arrayStrides :: XArray sh a -> [Int]
arrayStrides (XArray (ORS.A (ORG.A _ (OI.T strides _ _)))) = strides

scalar :: Storable a => a -> XArray '[] a
scalar = XArray . S.scalar

-- | Will throw if the array does not have the casted-to shape.
cast :: forall sh1 sh2 sh' a. Rank sh1 ~ Rank sh2
     => StaticShX sh1 -> IShX sh2 -> StaticShX sh'
     -> XArray (sh1 ++ sh') a -> XArray (sh2 ++ sh') a
cast ssh1 sh2 ssh' (XArray arr)
  | Refl <- lemRankApp ssh1 ssh'
  , Refl <- lemRankApp (ssxFromShX sh2) ssh'
  = let arrsh :: IShX sh1
        arrsh = shxTakeSSX (Proxy @sh') ssh1 (shape (ssxAppend ssh1 ssh') (XArray arr))
    in if shxToList arrsh == shxToList sh2
         then XArray arr
         else error $ "Data.Array.Mixed.cast: Cannot cast (" ++ show arrsh ++ ") to (" ++ show sh2 ++ ")"

unScalar :: Storable a => XArray '[] a -> a
unScalar (XArray a) = S.unScalar a

replicate :: forall sh sh' a. Storable a => IShX sh -> StaticShX sh' -> XArray sh' a -> XArray (sh ++ sh') a
replicate sh ssh' (XArray arr)
  | Dict <- lemKnownNatRankSSX ssh'
  , Dict <- lemKnownNatRankSSX (ssxAppend (ssxFromShX sh) ssh')
  , Refl <- lemRankApp (ssxFromShX sh) ssh'
  = XArray (S.stretch (shxToList sh ++ S.shapeL arr) $
            S.reshape (map (const 1) (shxToList sh) ++ S.shapeL arr)
              arr)

replicateScal :: forall sh a. Storable a => IShX sh -> a -> XArray sh a
replicateScal sh x
  | Dict <- lemKnownNatRank sh
  = XArray (S.constant (shxToList sh) x)

generate :: Storable a => IShX sh -> (IIxX sh -> a) -> XArray sh a
generate sh f = fromVector sh $ VS.generate (shxSize sh) (f . ixxFromLinear sh)

-- generateM :: (Monad m, Storable a) => IShX sh -> (IIxX sh -> m a) -> m (XArray sh a)
-- generateM sh f | Dict <- lemKnownNatRank sh =
--   XArray . S.fromVector (shxShapeL sh)
--     <$> VS.generateM (shxSize sh) (f . ixxFromLinear sh)

-- This manually inlines S.index to make GHC simplification less fragile.
{-# INLINEABLE indexPartial #-}
indexPartial :: Storable a => XArray (sh ++ sh') a -> IIxX sh -> XArray sh' a
indexPartial (XArray (ORS.A (ORG.A (dim : sh) t@(OI.T {OI.strides = s : ss})))) (i :.% ix) =
  if i < 0 || i >= dim
  then error $ "indexPartial: out of bounds " ++ show (i, dim)
  else indexPartial (XArray (ORS.A (ORG.A sh (OI.T { OI.strides = ss
                                                   , OI.offset = OI.offset t + i * s
                                                   , OI.values = OI.values t })))) ix
indexPartial arr ZIX = arr
indexPartial _ _ = error "indexPartial: corrupted array"

{-# INLINEABLE index #-}
index :: forall sh a. Storable a => XArray sh a -> IIxX sh -> a
index (XArray (ORS.A (ORG.A _ t))) ix =
  OI.values t VS.! (OI.offset t + sum (zipWith (*) (toList ix) (OI.strides t)))

append :: forall n m sh a. Storable a
       => StaticShX sh -> XArray (n : sh) a -> XArray (m : sh) a -> XArray (AddMaybe n m : sh) a
append ssh (XArray a) (XArray b)
  | Dict <- lemKnownNatRankSSX ssh
  = XArray (S.append a b)

-- | All arrays must have the same shape, except possibly for the outermost
-- dimension.
concat :: Storable a
       => StaticShX sh -> NonEmpty (XArray (Nothing : sh) a) -> XArray (Nothing : sh) a
concat ssh l
  | Dict <- lemKnownNatRankSSX ssh
  = XArray (S.concatOuter (coerce (toList l)))

-- | If the prefix of the shape of the input array (@sh@) is empty (i.e.
-- contains a zero), then there is no way to deduce the full shape of the output
-- array (more precisely, the @sh2@ part): that could only come from calling
-- @f@, and there are no subarrays to call @f@ on. @orthotope@ errors out in
-- this case; we choose to fill the shape with zeros wherever we cannot deduce
-- what it should be.
--
-- For example, if:
--
-- @
-- arr :: XArray '[Just 3, Just 0, Just 4, Just 2, Nothing] Int   -- of shape [3, 0, 4, 2, 21]
-- f :: XArray '[Just 2, Nothing] Int -> XArray '[Just 5, Nothing, Just 17] Float
-- @
--
-- then:
--
-- @
-- rerank _ _ _ f arr :: XArray '[Just 3, Just 0, Just 4, Just 5, Nothing, Just 17] Float
-- @
--
-- and this result will have shape @[3, 0, 4, 5, 0, 17]@. Note the second @0@
-- in this shape: we don't know if @f@ intended to return an array with shape 0
-- here (it probably didn't), but there is no better number to put here absent
-- a subarray of the input to pass to @f@.
--
-- In this particular case the fact that @sh@ is empty was evident from the
-- type-level information, but the same situation occurs when @sh@ consists of
-- @Nothing@s, and some of those happen to be zero at runtime.
rerank :: forall sh sh1 sh2 a b.
          (Storable a, Storable b)
       => StaticShX sh -> StaticShX sh1 -> StaticShX sh2
       -> (XArray sh1 a -> XArray sh2 b)
       -> XArray (sh ++ sh1) a -> XArray (sh ++ sh2) b
rerank ssh ssh1 ssh2 f xarr@(XArray arr)
  | Dict <- lemKnownNatRankSSX (ssxAppend ssh ssh2)
  = let sh = shxTakeSSX (Proxy @sh1) ssh (shape (ssxAppend ssh ssh1) xarr)
    in if 0 `elem` shxToList sh
         then XArray (S.fromList (shxToList (shxAppend sh (shxCompleteZeros ssh2))) [])
         else case () of
           () | Dict <- lemKnownNatRankSSX ssh
              , Dict <- lemKnownNatRankSSX ssh2
              , Refl <- lemRankApp ssh ssh1
              , Refl <- lemRankApp ssh ssh2
              -> XArray (S.rerank @(Rank sh) @(Rank sh1) @(Rank sh2)
                          (\a -> let XArray r = f (XArray a) in r)
                          arr)

rerankTop :: forall sh1 sh2 sh a b.
             (Storable a, Storable b)
          => StaticShX sh1 -> StaticShX sh2 -> StaticShX sh
          -> (XArray sh1 a -> XArray sh2 b)
          -> XArray (sh1 ++ sh) a -> XArray (sh2 ++ sh) b
rerankTop ssh1 ssh2 ssh f = transpose2 ssh ssh2 . rerank ssh ssh1 ssh2 f . transpose2 ssh1 ssh

-- | The caveat about empty arrays at @rerank@ applies here too.
rerank2 :: forall sh sh1 sh2 a b c.
           (Storable a, Storable b, Storable c)
        => StaticShX sh -> StaticShX sh1 -> StaticShX sh2
        -> (XArray sh1 a -> XArray sh1 b -> XArray sh2 c)
        -> XArray (sh ++ sh1) a -> XArray (sh ++ sh1) b -> XArray (sh ++ sh2) c
rerank2 ssh ssh1 ssh2 f xarr1@(XArray arr1) (XArray arr2)
  | Dict <- lemKnownNatRankSSX (ssxAppend ssh ssh2)
  = let sh = shxTakeSSX (Proxy @sh1) ssh (shape (ssxAppend ssh ssh1) xarr1)
    in if 0 `elem` shxToList sh
         then XArray (S.fromList (shxToList (shxAppend sh (shxCompleteZeros ssh2))) [])
         else case () of
           () | Dict <- lemKnownNatRankSSX ssh
              , Dict <- lemKnownNatRankSSX ssh2
              , Refl <- lemRankApp ssh ssh1
              , Refl <- lemRankApp ssh ssh2
              -> XArray (S.rerank2 @(Rank sh) @(Rank sh1) @(Rank sh2)
                          (\a b -> let XArray r = f (XArray a) (XArray b) in r)
                          arr1 arr2)

-- | The list argument gives indices into the original dimension list.
transpose :: forall is sh a. (IsPermutation is, Rank is <= Rank sh)
          => StaticShX sh
          -> Perm is
          -> XArray sh a
          -> XArray (PermutePrefix is sh) a
transpose ssh perm (XArray arr)
  | Dict <- lemKnownNatRankSSX ssh
  , Refl <- lemRankApp (ssxPermute perm (ssxTakeLen perm ssh)) (ssxDropLen perm ssh)
  , Refl <- lemRankPermute (Proxy @(TakeLen is sh)) perm
  , Refl <- lemRankDropLen ssh perm
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
  = XArray (S.transpose (permToList' perm) arr)
#else
  = XArray (unsafeCoerce (S.transpose (permToList' perm) arr))
#endif


-- | The list argument gives indices into the original dimension list.
--
-- The permutation (the list) must have length <= @n@. If it is longer, this
-- function throws.
transposeUntyped :: forall n sh a.
                    SNat n -> StaticShX sh -> [Int]
                 -> XArray (Replicate n Nothing ++ sh) a -> XArray (Replicate n Nothing ++ sh) a
transposeUntyped sn ssh perm (XArray arr)
  | length perm <= fromSNat' sn
  , Dict <- lemKnownNatRankSSX (ssxAppend (ssxReplicate sn) ssh)
  = XArray (S.transpose perm arr)
  | otherwise
  = error "Data.Array.Mixed.transposeUntyped: Permutation longer than length of unshaped prefix of shape type"

transpose2 :: forall sh1 sh2 a.
              StaticShX sh1 -> StaticShX sh2
           -> XArray (sh1 ++ sh2) a -> XArray (sh2 ++ sh1) a
transpose2 ssh1 ssh2 (XArray arr)
  | Refl <- lemRankApp ssh1 ssh2
  , Refl <- lemRankApp ssh2 ssh1
  , Dict <- lemKnownNatRankSSX (ssxAppend ssh1 ssh2)
  , Dict <- lemKnownNatRankSSX (ssxAppend ssh2 ssh1)
  , Refl <- lemRankAppComm ssh1 ssh2
  , let n1 = ssxLength ssh1
  = XArray (S.transpose (ssxIotaFrom ssh2 n1 ++ ssxIotaFrom ssh1 0) arr)

sumFull :: (Storable a, NumElt a) => StaticShX sh -> XArray sh a -> a
sumFull _ (XArray arr) =
  S.unScalar $
    liftO1 (numEltSum1Inner (SNat @0)) $
      S.fromVector [product (S.shapeL arr)] $
        S.toVector arr

sumInner :: forall sh sh' a. (Storable a, NumElt a)
         => StaticShX sh -> StaticShX sh' -> XArray (sh ++ sh') a -> XArray sh a
sumInner ssh ssh' arr
  | Refl <- lemAppNil @sh
  = let sh' = shxDropSSX @sh @sh' ssh (shape (ssxAppend ssh ssh') arr)
        sh'F = shxFlatten sh' :$% ZSX
        ssh'F = ssxFromShX sh'F

        go :: XArray (sh ++ '[Flatten sh']) a -> XArray sh a
        go (XArray arr')
          | Refl <- lemRankApp ssh ssh'F
          , let sn = ssxRank ssh
          = XArray (liftO1 (numEltSum1Inner sn) arr')

    in go $
       transpose2 ssh'F ssh $
       reshapePartial ssh' ssh sh'F $
       transpose2 ssh ssh' $
         arr

sumOuter :: forall sh sh' a. (Storable a, NumElt a)
         => StaticShX sh -> StaticShX sh' -> XArray (sh ++ sh') a -> XArray sh' a
sumOuter ssh ssh' arr
  | Refl <- lemAppNil @sh
  = let sh = shxTakeSSX (Proxy @sh') ssh (shape (ssxAppend ssh ssh') arr)
        shF = shxFlatten sh :$% ZSX
    in sumInner ssh' (ssxFromShX shF) $
       transpose2 (ssxFromShX shF) ssh' $
       reshapePartial ssh ssh' shF $
         arr

-- | If @n@ is an 'SKnown' dimension, the list is streamed. If @n@ is unknown,
-- the list's spine must be fully materialised to compute its length before
-- constructing the array. The list can't be empty (not enough information
-- in the given shape to guess the shape of the empty array, in general).
fromListOuter :: forall n sh a. Storable a
              => StaticShX (n : sh) -> [XArray sh a] -> XArray (n : sh) a
fromListOuter ssh l
  | Dict <- lemKnownNatRankSSX (ssxTail ssh)
  , let l' = coerce @[XArray sh a] @[S.Array (Rank sh) a] l
  = case ssh of
      _ :!% ZKX ->
        fromList1 ssh (map S.unScalar l')
      _ ->
        let n = case ssh of
              SKnown m :!% _ -> fromSNat' m
              _ -> length l
        in XArray (ravelOuterN n l')

-- | This checks that the list has the given length and that all shapes in the
-- list are equal. The list must be non-empty, and is streamed.
ravelOuterN :: (KnownNat k, Storable a)
            => Int -> [S.Array k a] -> S.Array (1 + k) a
ravelOuterN 0 _ = error "ravelOuterN: N == 0"
ravelOuterN _ [] = error "ravelOuterN: empty list"
ravelOuterN k as@(a0 : _) = runST $ do
  let sh0 = S.shapeL a0
      len = product sh0
      vecSize = k * len
  vec <- VSM.unsafeNew vecSize
  let f !n a =
        if | n >= k ->
             error $ "ravelOuterN: list too long " ++ show (n, k)
               -- if we do this check just once at the end, we may
               -- crash instead of producing an accurate error message
           | S.shapeL a == sh0 -> do
             VS.unsafeCopy (VSM.slice (n * len) len vec) (S.toVector a)
             return $! n + 1
           | otherwise ->
             error $ "ravelOuterN: unequal shapes " ++ show (S.shapeL a, sh0)
  nFinal <- foldM f 0 as
  if nFinal == k
  then S.fromVector (k : sh0) <$> VS.unsafeFreeze vec
  else error $ "ravelOuterN: list too short " ++ show (nFinal, k)

toListOuter :: forall a n sh. Storable a => XArray (n : sh) a -> [XArray sh a]
toListOuter (XArray arr@(ORS.A (ORG.A _ t))) =
  case S.shapeL arr of
    [] -> error "impossible"
    0 : _ -> []
    -- using orthotope's functions here would entail using rerank, which is slow, so we don't
    [_] | Refl <- (unsafeCoerceRefl :: sh :~: '[]) -> coerce (map S.scalar $ S.toList arr)
    n : sh -> coerce $ map (ORG.A sh . OI.indexT t) [0 .. n - 1]

-- | If @n@ is an 'SKnown' dimension, the list is streamed. If @n@ is unknown,
-- the list's spine must be fully materialised to compute its length before
-- constructing the array.
fromList1 :: Storable a => StaticShX '[n] -> [a] -> XArray '[n] a
fromList1 ssh l =
  case ssh of
    SKnown m :!% _ ->
      let n = fromSNat' m  -- do length check and vector construction simultaneously so that l can be streamed
      in XArray (S.fromVector [n] (VGC.fromListNChecked n l))
    _ ->
      let n = length l  -- avoid S.fromList because it takes a length _and_ does another length check itself
      in XArray (S.fromVector [n] (VS.fromListN         n l))

toList1 :: Storable a => XArray '[n] a -> [a]
toList1 (XArray arr) = S.toList arr

-- | Throws if the given shape is not, in fact, empty.
empty :: forall sh a. Storable a => IShX sh -> XArray sh a
empty sh
  | Dict <- lemKnownNatRank sh
  , shxSize sh == 0
  = XArray (S.fromVector (shxToList sh) VS.empty)
  | otherwise
  = error $ "Data.Array.Mixed.empty: shape was not empty: " ++ show sh

slice :: SNat i -> SNat n -> XArray (Just (i + n + k) : sh) a -> XArray (Just n : sh) a
slice i n (XArray arr) = XArray (S.slice [(fromSNat' i, fromSNat' n)] arr)

sliceU :: Int -> Int -> XArray (Nothing : sh) a -> XArray (Nothing : sh) a
sliceU i n (XArray arr) = XArray (S.slice [(i, n)] arr)

rev1 :: XArray (n : sh) a -> XArray (n : sh) a
rev1 (XArray arr) = XArray (S.rev [0] arr)

-- | Throws if the given array and the target shape do not have the same number of elements.
reshape :: forall sh1 sh2 a. Storable a => StaticShX sh1 -> IShX sh2 -> XArray sh1 a -> XArray sh2 a
reshape ssh1 sh2 (XArray arr)
  | Dict <- lemKnownNatRankSSX ssh1
  , Dict <- lemKnownNatRank sh2
  = XArray (S.reshape (shxToList sh2) arr)

-- | Throws if the given array and the target shape do not have the same number of elements.
reshapePartial :: forall sh1 sh2 sh' a. Storable a => StaticShX sh1 -> StaticShX sh' -> IShX sh2 -> XArray (sh1 ++ sh') a -> XArray (sh2 ++ sh') a
reshapePartial ssh1 ssh' sh2 (XArray arr)
  | Dict <- lemKnownNatRankSSX (ssxAppend ssh1 ssh')
  , Dict <- lemKnownNatRankSSX (ssxAppend (ssxFromShX sh2) ssh')
  = XArray (S.reshape (shxToList sh2 ++ drop (ssxLength ssh1) (S.shapeL arr)) arr)

-- this was benchmarked to be (slightly) faster than S.iota, S.generate and S.fromVector(VS.enumFromTo).
iota :: (Enum a, Storable a) => SNat n -> XArray '[Just n] a
iota sn = XArray (S.fromVector [fromSNat' sn] (VS.fromListN (fromSNat' sn) [toEnum 0 .. toEnum (fromSNat' sn - 1)]))
