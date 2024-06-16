{-# LANGUAGE AllowAmbiguousTypes, ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Tensor operations implementation using the ox-arrays package.
module HordeAd.Internal.BackendOX
  ( module HordeAd.Internal.BackendOX
  ) where

import Prelude hiding (foldl')

import           Control.Arrow (second)
import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal as OI
import qualified Data.Array.Internal.RankedG as RG
import qualified Data.Array.Internal.RankedS as RS
import qualified Data.Array.Internal.ShapedG as SG
import qualified Data.Array.Internal.ShapedS as SS
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Coerce
import qualified Data.Foldable as Foldable
import           Data.Functor (void)
import           Data.Int (Int64)
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict as M
import           Data.Maybe (fromJust, listToMaybe)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VM
import           GHC.Exts (IsList (..))
import qualified GHC.IsList as IsList
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , SomeNat (..)
  , fromSNat
  , sameNat
  , someNatVal
  , type (+)
  , type (<=)
  )
import           Numeric.LinearAlgebra (Numeric)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Internal.Arith as Mixed.Internal.Arith
import qualified Data.Array.Mixed.Permutation as Permutation
import qualified Data.Array.Mixed.Shape as X
import qualified Data.Array.Mixed.Types as X
import qualified Data.Array.Mixed.XArray
import qualified Data.Array.Nested as Nested
import qualified Data.Array.Nested.Internal.Mixed as Nested.Internal
import qualified Data.Array.Nested.Internal.Ranked as Nested.Internal
import qualified Data.Array.Nested.Internal.Shape as Nested.Internal.Shape
import qualified Data.Array.Nested.Internal.Shaped as Nested.Internal

import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), FlipS)
import           HordeAd.Util.ShapedList (IndexS, ShapedNat)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

type ORArray = FlipR Nested.Ranked

type OSArray = FlipS Nested.Shaped


-- * Ranked tensor operations

-- We often debug around here, so let's add Show and obfuscate it
-- to avoid warnings that it's unused. The addition silences warnings upstream.
type NumAndShow r = (Nested.Elt r, Nested.PrimElt r, Mixed.Internal.Arith.NumElt r, Numeric r, Show r)

type IndexInt n = Index n Int64

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m a. (NumAndShow a, KnownNat n, KnownNat m)
         => Nested.Ranked (n + m) a -> [(IndexInt n, Nested.Ranked m a)]
         -> Nested.Ranked (n + m) a
updateNR arr upd =
  let values = Nested.rtoVector arr
      sh = Nested.rshape arr
      f !t (ix, u) =
        let v = Nested.rtoVector u
            i = fromIntegral $ toLinearIdx @n @m fromIntegral sh ix
        in V.concat [V.take i t, v, V.drop (i + V.length v) t]
  in Nested.rfromVector sh (foldl' f values upd)

tshapeR
  :: (NumAndShow r, KnownNat n)
  => Nested.Ranked n r -> ShapeInt n
tshapeR = Nested.rshape

tminIndexR
  :: forall n r r2. (NumAndShow r, NumAndShow r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tminIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rminIndexPrim
  in Nested.rrerank (SNat @n) ZSR f

tmaxIndexR
  :: forall n r r2. (NumAndShow r, NumAndShow r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tmaxIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rmaxIndexPrim
  in Nested.rrerank (SNat @n) ZSR f

tfloorR :: (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2, KnownNat n)
        => Nested.Ranked n r -> Nested.Ranked n r2
tfloorR = {- liftVR (V.map floor)

liftVR
  :: ( KnownNat n, Nested.Internal.PrimElt r1, Nested.Internal.PrimElt r
     , VS.Storable r, VS.Storable r1
     , Coercible (forall sh. Nested.Mixed sh r1 -> Nested.Mixed sh r)
                 (Nested.Ranked n r1 -> Nested.Ranked n r) )
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r
liftVR = -}
  coerce  -- arithPromoteRanked
    (mliftNumElt1
       (flip liftVEltwise1 (V.map floor)))

{-
-- A bit more general than Nested.Internal.arithPromoteRanked.
arithPromoteRanked :: forall n a b.
                      (Nested.Internal.PrimElt a, Nested.Internal.PrimElt b)
                   => (forall sh. Nested.Mixed sh a -> Nested.Mixed sh b)
                   -> Nested.Ranked n a -> Nested.Ranked n b
arithPromoteRanked = coerce
-}

-- A bit more general than Nested.Internal.mliftNumElt1.
mliftNumElt1 :: (Nested.Internal.PrimElt a, Nested.Internal.PrimElt b)
             => (SNat (X.Rank sh) -> OR.Array (X.Rank sh) a -> OR.Array (X.Rank sh) b) -> Nested.Mixed sh a -> Nested.Mixed sh b
mliftNumElt1 f (Nested.Internal.toPrimitive -> Nested.Internal.M_Primitive sh (Data.Array.Mixed.XArray.XArray arr)) = Nested.Internal.fromPrimitive $ Nested.Internal.M_Primitive sh (Data.Array.Mixed.XArray.XArray (f (X.shxRank sh) arr))

-- A bit more general than Mixed.Internal.Arith.liftVEltwise1.
liftVEltwise1 :: (VS.Storable a, VS.Storable b)
              => SNat n
              -> (VS.Vector a -> VS.Vector b)
              -> OR.Array n a -> OR.Array n b
liftVEltwise1 SNat f arr@(RS.A (RG.A sh (OI.T strides offset vec)))
  | Just (blockOff, blockSz) <- Mixed.Internal.Arith.stridesDense sh offset strides =
      let vec' = f (VS.slice blockOff blockSz vec)
      in RS.A (RG.A sh (OI.T strides (offset - blockOff) vec'))
  | otherwise = RS.fromVector sh (f (RS.toVector arr))

ixInBounds :: [Int64] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: forall m n r. (KnownNat m, KnownNat n, NumAndShow r)
  => Nested.Ranked (m + n) r -> IndexInt m -> Nested.Ranked n r
tindexNR v ix = let sh = Nested.rshape v
                    !_A = assert (ixInBounds (toList ix) (toList sh)
                                  `blame` (v, ix)) ()
                in Nested.rindexPartial v (fmap fromIntegral ix)
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindexNR v@(RS.A (RG.A sh OI.T{strides, offset, values})) ix =
  let l = indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = valueOf @m  -- length of prefix being indexed out of
      !_A = assert (ixInBounds l sh `blame` (ix, sh, v)) ()
  in
    RS.A (RG.A (drop plen sh) OI.T{ strides = drop plen strides
                                  , offset = linear
                                  , values })
-}

tindexZR
  :: forall m n r. (KnownNat m, KnownNat n, NumAndShow r)
  => Nested.Ranked (m + n) r -> IndexInt m -> Nested.Ranked n r
tindexZR v ix =
  let sh = Nested.rshape v
  in if ixInBounds (toList ix) (toList sh)
     then tindexNR v ix
     else Nested.rreplicateScal (dropShape @m sh) 0

tindex0R
  :: (NumAndShow r, KnownNat n)
  => Nested.Ranked n r -> IndexInt n -> r
tindex0R v ix =
  let sh = Nested.rshape v
  in if ixInBounds (toList ix) (toList sh)
     then Nested.rindex v (fmap fromIntegral ix)
     else 0
{- TODO: see above
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
-}

------ perf reviewed up to this point

tsumR
  :: forall n r. (KnownNat n, NumAndShow r)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r
{- TODO
tsumR (RS.A (RG.A (k : sh) (OI.T (_ : ss) o vt))) | V.length vt == 1 =
  RS.A (RG.A sh (OI.T ss o (V.map (* fromIntegral k) vt)))
-}
tsumR = Nested.rsumOuter1
{-
case rshape t of
-- TODO: does GHC need this?  [] -> error "tsumR: null shape"
  0 :$: sh2 -> Nested.rsumOuter1 t  -- TODO: OR.constant sh2 0  -- the shape is known from sh, so no ambiguity
  k :$: sh2 -> case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> Nested.rsumOuter1 t  -- TODO: OR.scalar $ tsum0R t
    _ -> Nested.rfromVector sh2 $ unsafePerformIO $ do  -- unsafe only due to FFI
      v <- V.unsafeThaw $ Nested.rtoVector t
      VM.unsafeWith v $ \ptr -> do
        let len2 = product sh2
        v2 <- VM.new len2
        VM.unsafeWith v2 $ \ptr2 -> do
          rowSum len2 k ptr ptr2
          void $ V.unsafeFreeze v
          V.unsafeFreeze v2
-}

-- | Sum all elements of a tensor. TODO: is this correct?
tsum0R
  :: NumAndShow r
  => Nested.Ranked n r -> r
tsum0R u = case Nested.rtoOrthotope u of
  (RS.A (RG.A sh (OI.T _ _ vt))) | V.length vt == 1 ->
    fromIntegral (product sh) * vt V.! 0
  (RS.A (RG.A sh t)) ->
    LA.sumElements $ OI.toUnorderedVectorT sh t

{-
-- | Sum the innermost dimension (at least at rank 2; TODO: generalize).
-- TODO: Or is always the second dimension a better choice?
tsumInR
  :: forall n r. (KnownNat n, Numeric r, RowSum r)
  => OR.Array (1 + n) r -> OR.Array n r
-- TODO: tsumInR t@(RS.A (RG.A _ (OI.T _ _ vt))) | V.length vt == 1 = ...
tsumInR t = case OR.shapeL t of
  [] -> error "tsumInR: null shape"
  [k2, 0] -> OR.constant [k2] 0  -- the shape is known from sh, so no ambiguity
  [k2, k] -> case t of
    RS.A (RG.A _ (OI.T (s2 : _) o vt)) | V.length vt == 1 ->
      RS.A (RG.A [k2] (OI.T [s2] o (V.map (* fromIntegral k) vt)))
    _ -> let sh2 = [k2]
         in OR.fromVector sh2 $ unsafePerformIO $ do  -- unsafe only due to FFI
           v <- V.unsafeThaw $ OR.toVector t
           VM.unsafeWith v $ \ptr -> do
             let len2 = product sh2
             v2 <- VM.new len2
             VM.unsafeWith v2 $ \ptr2 -> do
               columnSum k len2 ptr ptr2
               void $ V.unsafeFreeze v
               V.unsafeFreeze v2
  _ -> error "tsumInR: not yet generalized beyond rank 2"
-}

tdot0R
  :: NumAndShow r
  => Nested.Ranked n r -> Nested.Ranked n r -> r
tdot0R = Nested.rdot
{-
tdot0R (RS.A (RG.A sh (OI.T _ _ vt))) (RS.A (RG.A _ (OI.T _ _ vu)))
  | V.length vt == 1 && V.length vu == 1 =
      fromIntegral (product sh) * vt V.! 0 * vu V.! 0
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u)
-}

tdot1InR
  :: NumAndShow r
  => Nested.Ranked 2 r -> Nested.Ranked 2 r -> Nested.Ranked 1 r
tdot1InR t u = -- TODO: t@(RS.A (RG.A _ (OI.T _ _ vt))) u@(RS.A (RG.A _ (OI.T _ _ vu))) =
--  if V.length vt == 1 || V.length vu == 1
--  then tsumInR (t * u)
--  else
       let lt = tunravelToListR t
           lu = tunravelToListR u
           l = zipWith Nested.rdot1 lt lu
       in Nested.rfromList1 $ NonEmpty.fromList l

-- TODO: add these to orthotope, faster; factor out unravel through them
-- and think if ravelFromList makes sense
tunravelToListR :: NumAndShow r => Nested.Ranked (1 + n) r -> [Nested.Ranked n r]
tunravelToListR = Nested.rtoListOuter

tunravelToListS :: forall r n sh. (NumAndShow r, KnownNat n, KnownShS sh)
                => Nested.Shaped (n ': sh) r -> [Nested.Shaped sh r]
tunravelToListS = Nested.stoListOuter

tmatvecmulR
  :: NumAndShow r
  => Nested.Ranked 2 r -> Nested.Ranked 1 r -> Nested.Ranked 1 r
tmatvecmulR t u =
  let t2 = Nested.rtoVector t
      u2 = Nested.rtoVector u
      (trows, tcols) = case Foldable.toList $ Nested.rshape t of
        [r, c] -> (r, c)
        _ -> error "tmatvecmulR: impossible wrong shape"
  in Nested.rfromVector (IsList.fromList [trows]) $ LA.reshape tcols t2 LA.#> u2

tmatmul2R
  :: NumAndShow r
  => Nested.Ranked 2 r -> Nested.Ranked 2 r -> Nested.Ranked 2 r
tmatmul2R t u =
  let t2 = Nested.rtoVector t
      u2 = Nested.rtoVector u
      (trows, tcols) = case Foldable.toList $ Nested.rshape t of
        [r, c] -> (r, c)
        _ -> error "tmatmul2R: impossible wrong shape"
      ucols = case Foldable.toList $ Nested.rshape u of
        [_, c] -> c
        _ -> error "tmatmul2R: impossible wrong shape"
  in Nested.rfromVector (IsList.fromList [trows, ucols]) $ LA.flatten
     $ LA.reshape tcols t2 LA.<> LA.reshape ucols u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by V.concat, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZR :: forall m p n r.
              (KnownNat m, KnownNat p, KnownNat n, NumAndShow r)
           => ShapeInt (p + n) -> Nested.Ranked (m + n) r
           -> (IndexInt m -> IndexInt p)
           -> Nested.Ranked (p + n) r
tscatterZR sh t f =
  let (shm, shDropP) = splitAt_Shape @m $ Nested.rshape t
      s = product $ shapeToList shm
      g ix =
        let ix2 = f ix
        in if ixInBounds (indexToList ix2) (shapeToList sh)
           then M.insertWith (V.zipWith (+)) ix2 (Nested.rtoVector $ t `tindexNR` ix)
           else id
      ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                            | i <- [0 .. fromIntegral s - 1] ]
  in updateNR (treplicate0NR sh 0)
     $ map (second $ Nested.rfromVector shDropP)
     $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling Nested.rfromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (NumAndShow r, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> Nested.Ranked (1 + n) r -> (Int64 -> IndexInt p)
            -> Nested.Ranked (p + n) r
tscatterZ1R sh t f =
-- TODO: tscatterZ1R sh t f = case Foldable.toList $ Nested.rshape t of
--   0 : _ -> Nested.constant (shapeToList sh) 0
--  _ ->
      sum $ imap (\i ti ->
                     let ix2 = f $ fromIntegral i
                     in if ixInBounds (indexToList ix2) (shapeToList sh)
                        then updateNR (treplicate0NR sh 0) [(ix2, ti)]
                        else treplicate0NR sh 0)
          $ tunravelToListR t

tfromListR
  :: forall n r. (KnownNat n, NumAndShow r)
  => NonEmpty (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tfromListR = Nested.rfromListOuter  -- TODO: make this strict

tfromList0NR
  :: (KnownNat n, NumAndShow r)
  => ShapeInt n -> [r] -> Nested.Ranked n r
tfromList0NR sh = Nested.Internal.rfromListPrimLinear sh
  -- TODO: make this strict

tfromVectorR
  :: forall n r. (KnownNat n, NumAndShow r)
  => Data.Vector.Vector (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
-- TODO: tfromVectorR l | V.null l =
--  case sameNat (Proxy @n) (Proxy @0) of
--    Just Refl -> Nested.rfromListOuter [0] []
--    _ ->  error "tfromVectorR: shape ambiguity, no arguments"
tfromVectorR = tfromListR . NonEmpty.fromList . V.toList
-- Nested.ravel $ ORB.fromVector [V.length l] $ V.convert l

tfromVector0NR
  :: (KnownNat n, NumAndShow r)
  => ShapeInt n -> Data.Vector.Vector r -> Nested.Ranked n r
tfromVector0NR sh = tfromList0NR sh . V.toList
  -- TODO: optimize

treplicateR
  :: forall n r. (KnownNat n, NumAndShow r)
  => Int -> Nested.Ranked n r -> Nested.Ranked (1 + n) r
-- TODO: treplicateR 0 u = Nested.rfromListOuter (0 : Nested.shapeL u) []
--treplicateR s u = case sameNat (Proxy @n) (Proxy @0) of
--  Just Refl -> Nested.constant [s] (Nested.runScalar u)
--  _ -> Nested.ravel $ ORB.constant [s] u
treplicateR n u =
  case NonEmpty.nonEmpty $ replicate n u of
    Nothing -> let sh = Nested.rshape u
               in Nested.rreplicateScal (n :$: sh) 0
    Just l -> Nested.rfromListOuter l

treplicate0NR
  :: (KnownNat n, NumAndShow r)
  => ShapeInt n -> r -> Nested.Ranked n r
treplicate0NR = Nested.rreplicateScal

tappendR
  :: (KnownNat n, NumAndShow r)
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
  -> Nested.Ranked (1 + n) r
tappendR = Nested.rappend

tsliceR
  :: NumAndShow r
  => Int -> Int -> Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
tsliceR i n = Nested.rslice i n

treverseR
  :: NumAndShow r
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
treverseR = Nested.rrev1

ttransposeR
  :: (KnownNat n, NumAndShow r)
  => Permutation -> Nested.Ranked n r -> Nested.Ranked n r
ttransposeR = Nested.rtranspose

treshapeR
  :: (KnownNat n, KnownNat m, NumAndShow r)
  => ShapeInt m -> Nested.Ranked n r -> Nested.Ranked m r
treshapeR = Nested.rreshape

tbuild1R
  :: forall n r. (KnownNat n, NumAndShow r)
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tbuild1R k f =
  Nested.rfromListOuter
  $ NonEmpty.map f
  $ NonEmpty.fromList [0 .. fromIntegral k - 1]  -- hope this fuses
-- TODO: tbuild1R 0 _ = case sameNat (Proxy @n) (Proxy @0) of
--  Just Refl -> Nested.rfromListOuter [0] []  -- the only case where we can guess sh
--  _ ->  error "tbuild1R: shape ambiguity, no arguments"
--tbuild1R k f = Nested.ravel $ ORB.fromList [k]
--               $ map f [0 .. fromIntegral k - 1]  -- hope this fuses
{- TODO
tmap0NR
  :: (Numeric r, Numeric r2)
  => (Nested.Ranked 0 r -> Nested.Ranked 0 r2) -> Nested.Ranked n r -> Nested.Ranked n r2
tmap0NR f = Nested.mapA (tunScalarR . f . tscalarR)
            -- too slow: tbuildNR (tshapeR v) (\ix -> f $ v `tindexNR` ix)
            -- bad type: liftVR . LA.cmap

tzipWith0NR
  :: (Numeric r, Numeric r2, Numeric r3)
  => (Nested.Ranked 0 r -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r3)
  -> Nested.Ranked n r -> Nested.Ranked n r2 -> Nested.Ranked n r3
tzipWith0NR f = Nested.zipWithA (\x y -> tunScalarR $ f (tscalarR x) (tscalarR y))
                -- bad type: liftVR2 . Numeric.LinearAlgebra.Devel.zipVectorWith
-}

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZR
--
-- Note how tindexZR is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, NumAndShow r)
          => ShapeInt (m + n) -> Nested.Ranked (p + n) r
          -> (IndexInt m -> IndexInt p)
          -> Nested.Ranked (m + n) r
tgatherZR sh t f =
  let shm = takeShape @m sh
      s = sizeShape shm
      l = [ Nested.rtoVector $ t `tindexZR` f (fromLinearIdx fromIntegral shm i)
          | i <- [0 .. fromIntegral s - 1] ]
  in Nested.rfromVector sh $ V.concat l

tgatherZ1R :: forall p n r. (KnownNat p, KnownNat n, NumAndShow r)
           => Int -> Nested.Ranked (p + n) r -> (Int64 -> IndexInt p)
           -> Nested.Ranked (1 + n) r
-- TODO: tgatherZ1R 0 t _ = Nested.rfromListOuter (0 : drop (valueOf @p) (Nested.shapeL t)) []
tgatherZ1R k t f =
  let l = NonEmpty.map (\i -> t `tindexZR` f i)
                       (NonEmpty.fromList [0 .. fromIntegral k - 1])
  in Nested.rfromListOuter l

tcastR :: (NumAndShow r1, NumAndShow r2, KnownNat n, Real r1, Fractional r2)
       => Nested.Ranked n r1 -> Nested.Ranked n r2
tcastR =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map realToFrac)))

tfromIntegralR :: (NumAndShow r1, NumAndShow r2, KnownNat n, Integral r1)
               => Nested.Ranked n r1 -> Nested.Ranked n r2
tfromIntegralR =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map fromIntegral)))

tscalarR
  :: (Nested.Elt r, Numeric r)
  => r -> Nested.Ranked 0 r
tscalarR = Nested.rscalar

tunScalarR
  :: (Nested.Elt r, Numeric r)
  => Nested.Ranked 0 r -> r
tunScalarR = Nested.runScalar

tscaleByScalarR :: (Nested.PrimElt r, Nested.Elt r, Mixed.Internal.Arith.NumElt r, Numeric r, KnownNat n)
                => r -> Nested.Ranked n r -> Nested.Ranked n r
tscaleByScalarR s =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map (* s))))

toIndexOfR :: IndexInt n -> Index n (ORArray Int64 0)
toIndexOfR ix = FlipR . tscalarR <$> ix

fromIndexOfR :: Index n (ORArray Int64 0) -> IndexInt n
fromIndexOfR ixOf = tunScalarR . runFlipR <$> ixOf


-- * Shaped tensor operations

type Int64Sh (n :: Nat) = ShapedNat n Int64

type IndexIntSh sh = IndexS sh Int64

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r. (NumAndShow r, KnownShS sh, KnownShS (Sh.Drop n sh))
         => Nested.Shaped sh r
         -> [(IndexIntSh (Sh.Take n sh), Nested.Shaped (Sh.Drop n sh) r)]
         -> Nested.Shaped sh r
updateNS arr upd =
  let values = Nested.stoVector arr
      sh = knownShS @sh
      f !t (ix, u) =
        let v = Nested.stoVector u
            i = gcastWith (unsafeCoerce Refl
                           :: sh :~: Sh.Take n sh X.++ Sh.Drop n sh)
                $ fromIntegral
                $ ShapedList.unShapedNat
                $ ShapedList.toLinearIdx @(Sh.Take n sh) @(Sh.Drop n sh)
                                         fromIntegral sh ix
        in V.concat [V.take i t, v, V.drop (i + V.length v) t]
  in Nested.sfromVector knownShS (foldl' f values upd)

tminIndexS
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh, KnownNat n
                       , KnownShS (Sh.Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Sh.Init (n ': sh)) r2
tminIndexS =
  let f :: KnownNat m => Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead . Nested.sminIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat @shRank _proxy) ->
              gcastWith (unsafeCoerce Refl
                         :: Sh.Init (n ': sh) X.++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerce Refl
                         :: Sh.Init (n ': sh) :~: Sh.Init (n ': sh) X.++ '[]) $
              Nested.srerank @'[m] @'[] @(Sh.Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tminIndexS: impossible someNatVal error"
        Nothing -> error "tminIndexS: impossible someNatVal error"

tmaxIndexS
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh, KnownNat n
                       , KnownShS (Sh.Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Sh.Init (n ': sh)) r2
tmaxIndexS =
  let f :: KnownNat m => Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead . Nested.smaxIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat @shRank _proxy) ->
              gcastWith (unsafeCoerce Refl
                         :: Sh.Init (n ': sh) X.++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerce Refl
                         :: Sh.Init (n ': sh) :~: Sh.Init (n ': sh) X.++ '[]) $
              Nested.srerank @'[m] @'[] @(Sh.Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tmaxIndexS: impossible someNatVal error"
        Nothing -> error "tmaxIndexS: impossible someNatVal error"

tfloorS :: forall r r2 sh.
           (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2, KnownShS sh)
        => Nested.Shaped sh r -> Nested.Shaped sh r2
tfloorS =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map floor)))

tindexNS
  :: forall sh1 sh2 r. NumAndShow r
  => Nested.Shaped (sh1 X.++ sh2) r -> IndexIntSh sh1 -> Nested.Shaped sh2 r
tindexNS v ix = Nested.sindexPartial v (fmap fromIntegral ix)
{- TODO
tindexNS (SS.A (SG.A OI.T{strides, offset, values})) ix =
  let l = ShapedList.indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = length l  -- length of prefix being indexed out of
  in
    SS.A (SG.A OI.T{ strides = drop plen strides
                   , offset = linear
                   , values })
-}

-- Note that after vectorization, the index with type IndexIntSh sh1
-- may not fit within the type-level shape, which we catch in the @ixInBounds@
-- and return 0, so it's fine. Similarly in gather and scatter.
tindexZS
  :: forall sh1 sh2 r. (NumAndShow r, KnownShS sh2, KnownShS (sh1 X.++ sh2))
  => Nested.Shaped (sh1 X.++ sh2) r -> IndexIntSh sh1 -> Nested.Shaped sh2 r
tindexZS v ix =
  let sh = Nested.Internal.Shape.shsToList $ Nested.sshape v
  in if ixInBounds (ShapedList.indexToList ix) sh
     then tindexNS v ix
     else Nested.sreplicateScal knownShS 0

tindex0S
  :: NumAndShow r
  => Nested.Shaped sh r -> IndexIntSh sh -> r
tindex0S v ix =
  let sh = Nested.Internal.Shape.shsToList $ Nested.sshape v
  in if ixInBounds (ShapedList.indexToList ix) sh
     then Nested.sindex v (fmap fromIntegral ix)
     else 0
{- TODO, and check bounds, too
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

-- Sum the outermost dimension.
--
-- No NOINLINE, because apparently nothing breaks and hmatrix, etc.
-- also don't put NOINLINE in the functions using FFI.
tsumS
  :: forall n sh r. (KnownNat n, NumAndShow r, KnownShS sh)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped sh r
{- TODO
tsumS (SS.A (SG.A (OI.T (_ : ss) o vt))) | V.length vt == 1 =
  SS.A (SG.A (OI.T ss o (V.map (* valueOf @n) vt)))
-}
tsumS = Nested.ssumOuter1

{- t =
  case knownShS @(n ': sh) of
    (:$$) _ ZSS -> Nested.ssumOuter1 t  -- TODO: Nested.sscalar $ tsum0S t
    (:$$) @_ @sh2 k _ ->
      Nested.sfromVector knownShS $ unsafePerformIO $ do  -- unsafe only due to FFI
        v <- V.unsafeThaw $ Nested.stoVector t
        VM.unsafeWith v $ \ptr -> do
          let len2 = sizeT @sh2
          v2 <- VM.new len2
          VM.unsafeWith v2 $ \ptr2 -> do
            rowSum len2 (fromInteger $ fromSNat k) ptr ptr2
            void $ V.unsafeFreeze v
            V.unsafeFreeze v2
-}

{-
-- Sum the innermost dimension (at least at rank 2; TODO: generalize).
-- Or is it always the second dimension as the type suggests?
tsumInS
  :: forall m n sh r. (KnownNat n, Numeric r, KnownNat m, KnownShS sh)
  => Nested.Shaped (m ': n ': sh) r -> Nested.Shaped (m ': sh) r
tsumInS t = case OS.shapeL t of
  [] -> error "tsumInS: null shape"
  k2 : 0 : [] ->
    (Nested.sreplicateScal knownShS 0)  -- the shape is known from sh, so no ambiguity
  [k2, k] -> case t of
    SS.A (SG.A (OI.T (s2 : _) o vt)) | V.length vt == 1 ->
      SS.A (SG.A (OI.T [s2] o (V.map (* fromIntegral k) vt)))
    _ -> let sh2 = [k2]
         in OS.fromVector $ unsafePerformIO $ do  -- unsafe only due to FFI
           v <- V.unsafeThaw $ OS.toVector t
           VM.unsafeWith v $ \ptr -> do
             let len2 = product sh2
             v2 <- VM.new len2
             VM.unsafeWith v2 $ \ptr2 -> do
               columnSum k len2 ptr ptr2
               void $ V.unsafeFreeze v
               V.unsafeFreeze v2
  _ -> error "tsumInS: not yet generalized beyond rank 2"
-}

-- | Sum all elements of a tensor. TODO: is this correct?
tsum0S
  :: forall sh r. (NumAndShow r, KnownShS sh)
  => Nested.Shaped sh r -> r
tsum0S u = case Nested.stoOrthotope u of
  (SS.A (SG.A (OI.T _ _ vt))) | V.length vt == 1 ->
    fromIntegral (sizeT @sh) * vt V.! 0
  (SS.A (SG.A t)) ->
    LA.sumElements $ OI.toUnorderedVectorT (shapeT @sh) t

tdot0S
  :: forall sh r. (NumAndShow r, KnownShS sh)
  => Nested.Shaped sh r -> Nested.Shaped sh r -> r
{- TODO
tdot0S (SS.A (SG.A (OI.T _ _ vt))) (SS.A (SG.A (OI.T _ _ vu)))
  | V.length vt == 1 && V.length vu == 1 =
      fromIntegral (sizeT @sh) * vt V.! 0 * vu V.! 0
-}
tdot0S = Nested.sdot

-- TODO: sdot1In :: shaped r (sh ++ [n]) -> shaped r (sh ++ [n]) -> shaped r sh
tdot1InS
  :: (NumAndShow r, KnownNat m, KnownNat n)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[m, n] r -> Nested.Shaped '[m] r
tdot1InS t u = -- TODO: t@(SS.A (SG.A (OI.T _ _ vt))) u@(SS.A (SG.A (OI.T _ _ vu))) =
--  if V.length vt == 1 || V.length vu == Nested.sreplicateScal knownShS 1
--  then tsumInS (t * u)
--  else
    let lt = tunravelToListS t
        lu = tunravelToListS u
        l = zipWith Nested.sdot1 lt lu
    in Nested.sfromList1 SNat $ NonEmpty.fromList l

tmatvecmulS
  :: forall m n r. (NumAndShow r, KnownNat m, KnownNat n)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n] r -> Nested.Shaped '[m] r
tmatvecmulS t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.reshape (valueOf @n) t2 LA.#> u2

tmatmul2S
  :: forall m n p r. (NumAndShow r, KnownNat m, KnownNat n, KnownNat p)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n, p] r -> Nested.Shaped '[m, p] r
tmatmul2S t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by V.concat, but this is done on demand).
-- TODO: optimize updateNS and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZS :: forall r sh2 p sh.
              (NumAndShow r, KnownShS sh, KnownShS sh2, KnownShS (Sh.Drop p sh))
           => Nested.Shaped (sh2 X.++ Sh.Drop p sh) r
           -> (IndexIntSh sh2 -> IndexIntSh (Sh.Take p sh))
           -> Nested.Shaped sh r
tscatterZS t f =
  let sh2 = knownShS @sh2
      g ix =
        let ix2 = f ix
        in if ixInBounds (ShapedList.indexToList ix2) (shapeT @sh)
           then M.insertWith (V.zipWith (+)) ix2
                  (Nested.stoVector $ tindexNS @sh2 @(Sh.Drop p sh) t ix)
           else id
      ivs = foldr g M.empty [ ShapedList.fromLinearIdx fromIntegral sh2
                              $ ShapedList.shapedNat $ fromIntegral i
                            | i <- [0 .. sizeT @sh2 - 1] ]
  in updateNS (Nested.sreplicateScal knownShS 0)
     $ map (second $ Nested.sfromVector knownShS)
     $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S :: forall r n2 p sh.
               (NumAndShow r, KnownNat n2, KnownShS sh, KnownShS (Sh.Drop p sh))
            => Nested.Shaped (n2 ': Sh.Drop p sh) r
            -> (Int64Sh n2 -> IndexIntSh (Sh.Take p sh))
            -> Nested.Shaped sh r
tscatterZ1S t f =
    sum $ imap (\i ti ->
                   let ix2 = f $ ShapedList.shapedNat $ fromIntegral i
                   in if ixInBounds (ShapedList.indexToList ix2)
                                    (shapeT @sh)
                      then updateNS (Nested.sreplicateScal knownShS 0) [(ix2, ti)]
                      else Nested.sreplicateScal knownShS 0)
        $ tunravelToListS t

tfromListS
  :: forall n sh r. (NumAndShow r, KnownNat n, KnownShS sh)
  => NonEmpty (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromListS = Nested.sfromListOuter SNat  -- TODO: make this strict

tfromList0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => [r] -> Nested.Shaped sh r
tfromList0NS = Nested.Internal.sfromListPrimLinear knownShS
  -- TODO: make this strict

tfromVectorS
  :: forall n sh r. (NumAndShow r, KnownNat n, KnownShS sh)
  => Data.Vector.Vector (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromVectorS = tfromListS . NonEmpty.fromList . V.toList
  -- TODO: optimize

tfromVector0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => Data.Vector.Vector r -> Nested.Shaped sh r
tfromVector0NS = tfromList0NS . V.toList
  -- TODO: optimize

treplicateS
  :: forall n sh r. (NumAndShow r, KnownNat n, KnownShS sh)
  => Nested.Shaped sh r -> Nested.Shaped (n ': sh) r
treplicateS u =
  case NonEmpty.nonEmpty $ replicate (valueOf @n) u of
    Nothing -> Nested.sreplicateScal knownShS 0
    Just l -> Nested.sfromListOuter SNat l

treplicate0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => r -> Nested.Shaped sh r
treplicate0NS = Nested.sreplicateScal knownShS

tappendS
  :: forall r m n sh. (NumAndShow r, KnownNat m, KnownNat n, KnownShS sh)
  => Nested.Shaped (m ': sh) r -> Nested.Shaped (n ': sh) r -> Nested.Shaped ((m + n) ': sh) r
tappendS = Nested.sappend

tsliceS
  :: forall i n k sh r. (NumAndShow r, KnownNat i, KnownNat n)
  => Nested.Shaped (i + n + k ': sh) r -> Nested.Shaped (n ': sh) r
tsliceS = Nested.sslice (SNat @i) SNat

treverseS
  :: forall n sh r. (NumAndShow r, KnownNat n, KnownShS sh)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (n ': sh) r
treverseS = Nested.srev1

-- TODO: remove the conversion and overhaul the whole codebase
ttransposeS
  :: forall perm r sh.
     (NumAndShow r, PermC perm, KnownShS sh, X.Rank perm <= X.Rank sh )
  => Permutation.Perm perm -> Nested.Shaped sh r
  -> Nested.Shaped (Permutation.PermutePrefix perm sh) r
ttransposeS perm =
  gcastWith (unsafeCoerce Refl :: Compare (X.Rank perm) (X.Rank sh) :~: LT) $
  gcastWith (unsafeCoerce Refl
             :: Permutation.PermutePrefix perm sh :~: Permutation.PermutePrefix perm sh) $
  Nested.stranspose perm

treshapeS
  :: forall r sh sh2.
     (NumAndShow r, KnownShS sh, KnownShS sh2, Sh.Size sh ~ Sh.Size sh2)
  => Nested.Shaped sh r -> Nested.Shaped sh2 r
treshapeS = Nested.sreshape knownShS

tbuild1S
  :: forall n sh r. (KnownNat n, NumAndShow r, KnownShS sh)
  => (Int64Sh n -> Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tbuild1S f =
  let k = valueOf @n
  in Nested.sfromListOuter SNat
     $ NonEmpty.map (f . ShapedList.shapedNat)
     $ NonEmpty.fromList [0 .. k - 1]  -- hope this fuses

{- TODO
tmap0NS
  :: forall r r2 sh. (Numeric r, Numeric r2, KnownShS sh)
  => (Nested.Shaped '[] r -> Nested.Shaped '[] r2) -> Nested.Shaped sh r -> Nested.Shaped sh r2
tmap0NS f =
  OS.mapA (tunScalarS . f . tscalarS)
            -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)
            -- bad type: liftVS . LA.cmap

tzipWith0NS
  :: forall r1 r2 r sh. (Numeric r1, Numeric r2, Numeric r, KnownShS sh)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
tzipWith0NS f =
  OS.zipWithA (\x y -> tunScalarS $ f (tscalarS x) (tscalarS y))
                -- bad type: liftVS2 . Numeric.LinearAlgebra.Devel.zipVectorWith
-}

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZS
--
-- Note how tindexZS is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZS :: forall sh2 p sh r.
             ( NumAndShow r, KnownShS sh, KnownShS sh2, KnownShS (Sh.Drop p sh)
             , KnownShS (sh2 X.++ Sh.Drop p sh) )
          => Nested.Shaped sh r
          -> (IndexIntSh sh2 -> IndexIntSh (Sh.Take p sh))
          -> Nested.Shaped (sh2 X.++ Sh.Drop p sh) r
tgatherZS t f =
  let sh2 = knownShS @sh2
      s = sizeT @sh2
      l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh)
          $ [ Nested.stoVector
                (t `tindexZS` f (ShapedList.fromLinearIdx fromIntegral sh2
                                 $ ShapedList.shapedNat $ fromIntegral i)
                 :: Nested.Shaped (Sh.Drop p sh) r)
            | i <- [0 .. s - 1] ]
  in Nested.sfromVector knownShS $ V.concat l

tgatherZ1S :: forall n2 p sh r.
              ( NumAndShow r
              , KnownNat n2, KnownShS sh, KnownShS (Sh.Drop p sh) )
           => Nested.Shaped sh r -> (Int64Sh n2 -> IndexIntSh (Sh.Take p sh))
           -> Nested.Shaped (n2 ': Sh.Drop p sh) r
tgatherZ1S t f =
  let l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh)
          $ NonEmpty.map (\i -> t `tindexZS` f (ShapedList.shapedNat i))
                         (NonEmpty.fromList [0 .. valueOf @n2 - 1])
  in Nested.sfromListOuter SNat l

tcastS :: forall r1 r2 sh.
          (NumAndShow r1, NumAndShow r2, KnownShS sh, Real r1, Fractional r2)
       => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tcastS =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map realToFrac)))

tfromIntegralS :: forall r1 r2 sh .
                  (NumAndShow r1, NumAndShow r2, KnownShS sh, Integral r1)
               => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tfromIntegralS =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map fromIntegral)))

tscalarS
  :: (Nested.Elt r, Numeric r)
  => r -> Nested.Shaped '[] r
tscalarS = Nested.sscalar

tunScalarS
  :: (Nested.Elt r, Numeric r)
  => Nested.Shaped '[] r -> r
tunScalarS = Nested.sunScalar

tscaleByScalarS :: forall r sh. (Nested.PrimElt r, Mixed.Internal.Arith.NumElt r, Numeric r, KnownShS sh)
                => r -> Nested.Shaped sh r -> Nested.Shaped sh r
tscaleByScalarS s =
  coerce
    (mliftNumElt1
       (flip liftVEltwise1 (V.map (* s))))

toIndexOfS :: IndexIntSh sh -> IndexS sh (ORArray Int64 0)
toIndexOfS ix = FlipR . tscalarR <$> ix

fromIndexOfS :: IndexS sh (ORArray Int64 0) -> IndexIntSh sh
fromIndexOfS ixOf = tunScalarR . runFlipR <$> ixOf
