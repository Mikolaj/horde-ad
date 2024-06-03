{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Miscellaneous more or less general purpose tensor operations using
-- the orthotope package tensor representation and hmatrix package
-- (and also our own) FFI bindings.
module HordeAd.Internal.BackendConcrete
  ( module HordeAd.Internal.BackendConcrete
  , tsumR, tsum0R, tsumInR
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
import           Data.Functor (void)
import           Data.Int (Int64)
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Map as M
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable.Mutable as VM
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
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Shape as X
import qualified Data.Array.Mixed.Types as X

import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS, liftVR, liftVS)
import           HordeAd.Internal.TensorFFI
import           HordeAd.Util.ShapedList (IndexS, ShapedNat)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Ranked tensor operations

-- We often debug around here, so let's add Show and obfuscate it
-- to avoid warnings that it's unused. The addition silences warnings upstream.
type NumAndShow r = (Numeric r, Show r, Num (Vector r))

type IndexInt n = Index n Int64

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m a. (Numeric a, KnownNat n, KnownNat m)
         => OR.Array (n + m) a -> [(IndexInt n, OR.Array m a)]
         -> OR.Array (n + m) a
updateNR arr upd =
  let values = OR.toVector arr
      shRaw = OR.shapeL arr
      sh = listToShape shRaw
      f !t (ix, u) =
        let v = OR.toVector u
            i = fromIntegral $ toLinearIdx @n @m fromIntegral sh ix
        in LA.vjoin [V.take i t, v, V.drop (i + V.length v) t]
  in OR.fromVector shRaw (foldl' f values upd)

tshapeR
  :: KnownNat n
  => OR.Array n r -> ShapeInt n
tshapeR = listToShape . OR.shapeL

tminIndexR
  :: forall n r r2. (NumAndShow r, NumAndShow r2, KnownNat n)
  => OR.Array (1 + n) r -> OR.Array n r2
tminIndexR =
  let f :: OR.Array 1 r -> OR.Array 0 r2
      f = OR.scalar . fromIntegral . LA.minIndex . OR.toVector
  in case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> f
    _ -> OR.rerank f

tmaxIndexR
  :: forall n r r2. (NumAndShow r, NumAndShow r2, KnownNat n)
  => OR.Array (1 + n) r -> OR.Array n r2
tmaxIndexR =
  let f :: OR.Array 1 r -> OR.Array 0 r2
      f = OR.scalar . fromIntegral . LA.maxIndex . OR.toVector
  in case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> f
    _ -> OR.rerank f

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tfloorR :: (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2, KnownNat n)
        => OR.Array n r -> OR.Array n r2
tfloorR = liftVR (V.map floor)

ixInBounds :: [Int64] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: forall m n r. (KnownNat m, NumAndShow r)
  => OR.Array (m + n) r -> IndexInt m -> OR.Array n r
tindexNR v@(RS.A (RG.A sh OI.T{strides, offset, values})) ix =
  let l = indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = valueOf @m  -- length of prefix being indexed out of
      !_A = assert (ixInBounds l sh `blame` (ix, sh, v)) ()
  in
    RS.A (RG.A (drop plen sh) OI.T{ strides = drop plen strides
                                  , offset = linear
                                  , values })

tindexZR
  :: forall m n r. (KnownNat m, KnownNat n, NumAndShow r)
  => OR.Array (m + n) r -> IndexInt m -> OR.Array n r
tindexZR v ix =
  let sh = OR.shapeL v
  in if ixInBounds (indexToList ix) sh
     then tindexNR v ix
     else OR.constant (drop (valueOf @m) sh) 0

tindex0R
  :: Numeric r
  => OR.Array n r -> IndexInt n -> r
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way

tdot0R
  :: Numeric r
  => OR.Array n r -> OR.Array n r -> r
tdot0R (RS.A (RG.A sh (OI.T _ _ vt))) (RS.A (RG.A _ (OI.T _ _ vu)))
  | V.length vt == 1 && V.length vu == 1 =
      fromIntegral (product sh) * vt V.! 0 * vu V.! 0
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u)

tdot1InR
  :: (NumAndShow r, RowSum r)
  => OR.Array 2 r -> OR.Array 2 r -> OR.Array 1 r
tdot1InR t@(RS.A (RG.A _ (OI.T _ _ vt))) u@(RS.A (RG.A _ (OI.T _ _ vu))) =
  if V.length vt == 1 || V.length vu == 1
  then tsumInR (t * u)
  else let lt = map OR.toVector $ tunravelToListR t
           lu = map OR.toVector $ tunravelToListR u
           l = zipWith (LA.<.>) lt lu
       in OR.fromList [length l] l

-- TODO: add these to orthotope, faster; factor out unravel through them
-- and think if ravelFromList makes sense
tunravelToListR :: Numeric r => OR.Array (1 + n) r -> [OR.Array n r]
tunravelToListR t = case OR.shapeL t of
  0 : _ -> []
  _ -> ORB.toList $ OR.unravel t

tunravelToListS :: forall r n sh. (Numeric r, KnownNat n, KnownShS sh)
                => OS.Array (n ': sh) r -> [OS.Array sh r]
tunravelToListS t | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  case OS.shapeL t of
    0 : _ -> []
    _ -> OSB.toList $ OS.unravel t

tmatvecmulR
  :: Numeric r
  => OR.Array 2 r -> OR.Array 1 r -> OR.Array 1 r
tmatvecmulR t u =
  let t2 = OR.toVector t
      u2 = OR.toVector u
      (trows, tcols) = case OR.shapeL t of
        [r, c] -> (r, c)
        _ -> error "tmatvecmulR: wrong shape"
  in OR.fromVector [trows] $ LA.reshape tcols t2 LA.#> u2

tmatmul2R
  :: Numeric r
  => OR.Array 2 r -> OR.Array 2 r -> OR.Array 2 r
tmatmul2R t u =
  let t2 = OR.toVector t
      u2 = OR.toVector u
      (trows, tcols) = case OR.shapeL t of
        [r, c] -> (r, c)
        _ -> error "tmatmul2R: wrong shape"
      ucols = case OR.shapeL u of
        [_, c] -> c
        _ -> error "tmatmul2R: wrong shape"
  in OR.fromVector [trows, ucols] $ LA.flatten
     $ LA.reshape tcols t2 LA.<> LA.reshape ucols u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by LA.vjoin, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZR :: forall m p n r.
              (KnownNat m, KnownNat p, KnownNat n, NumAndShow r)
           => ShapeInt (p + n) -> OR.Array (m + n) r
           -> (IndexInt m -> IndexInt p)
           -> OR.Array (p + n) r
tscatterZR sh t f =
  let (sh2, shDropP) = splitAt (valueOf @m) $ OR.shapeL t
      s = product sh2
      shm = listToShape sh2
      g ix =
        let ix2 = f ix
        in if ixInBounds (indexToList ix2) (shapeToList sh)
           then M.insertWith (++) ix2 [OR.toVector $ t `tindexNR` ix]
           else id
      ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                            | i <- [0 .. fromIntegral s - 1] ]
  in updateNR (treplicate0NR sh 0) $ map (second $ OR.fromVector shDropP . sum)
                                   $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OR.fromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (NumAndShow r, KnownNat p, KnownNat n)
            => ShapeInt (p + n) -> OR.Array (1 + n) r -> (Int64 -> IndexInt p)
            -> OR.Array (p + n) r
tscatterZ1R sh t f = case OR.shapeL t of
  0 : _ -> OR.constant (shapeToList sh) 0
  _ ->
      sum $ imap (\i ti ->
                     let ix2 = f $ fromIntegral i
                     in if ixInBounds (indexToList ix2) (shapeToList sh)
                        then updateNR (treplicate0NR sh 0) [(ix2, ti)]
                        else treplicate0NR sh 0)
          $ tunravelToListR t

tfromListR
  :: forall n r. (KnownNat n, Numeric r)
  => NonEmpty (OR.Array n r) -> OR.Array (1 + n) r
tfromListR l = OR.ravel . ORB.fromList [NonEmpty.length l] . NonEmpty.toList $ l

tfromList0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> [r] -> OR.Array n r
tfromList0NR sh = OR.fromList (shapeToList sh)

tfromVectorR
  :: forall n r. (KnownNat n, Numeric r)
  => Data.Vector.Vector (OR.Array n r) -> OR.Array (1 + n) r
tfromVectorR l | V.null l =
  case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> OR.fromList [0] []
    _ ->  error "tfromVectorR: shape ambiguity, no arguments"
tfromVectorR l = OR.ravel $ ORB.fromVector [V.length l] $ V.convert l

tfromVector0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> Data.Vector.Vector r -> OR.Array n r
tfromVector0NR sh l = OR.fromVector (shapeToList sh) $ V.convert l

treplicateR
  :: forall n r. (KnownNat n, Numeric r)
  => Int -> OR.Array n r -> OR.Array (1 + n) r
treplicateR 0 u = OR.fromList (0 : OR.shapeL u) []
treplicateR s u = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> OR.constant [s] (OR.unScalar u)
  _ -> OR.ravel $ ORB.constant [s] u

treplicate0NR
  :: (KnownNat n, Numeric r)
  => ShapeInt n -> r -> OR.Array n r
treplicate0NR sh = OR.constant (shapeToList sh)

tappendR
  :: (KnownNat n, Numeric r)
  => OR.Array n r -> OR.Array n r -> OR.Array n r
tappendR = OR.append

tsliceR
  :: Int -> Int -> OR.Array n r -> OR.Array n r
tsliceR i n = OR.slice [(i, n)]

treverseR
  :: OR.Array (1 + n) r -> OR.Array (1 + n) r
treverseR = OR.rev [0]

ttransposeR
  :: KnownNat n
  => Permutation -> OR.Array n r -> OR.Array n r
ttransposeR = OR.transpose

treshapeR
  :: (KnownNat n, KnownNat m, Numeric r)
  => ShapeInt m -> OR.Array n r -> OR.Array m r
treshapeR sh = OR.reshape (shapeToList sh)

tbuild1R
  :: forall n r. (KnownNat n, Numeric r)
  => Int -> (Int64 -> OR.Array n r) -> OR.Array (1 + n) r
tbuild1R 0 _ = case sameNat (Proxy @n) (Proxy @0) of
  Just Refl -> OR.fromList [0] []  -- the only case where we can guess sh
  _ ->  error "tbuild1R: shape ambiguity, no arguments"
tbuild1R k f = OR.ravel $ ORB.fromList [k]
               $ map f [0 .. fromIntegral k - 1]  -- hope this fuses

tmap0NR
  :: (Numeric r, Numeric r2)
  => (OR.Array 0 r -> OR.Array 0 r2) -> OR.Array n r -> OR.Array n r2
tmap0NR f = OR.mapA (tunScalarR . f . tscalarR)
            -- too slow: tbuildNR (tshapeR v) (\ix -> f $ v `tindexNR` ix)
            -- bad type: liftVR . LA.cmap

tzipWith0NR
  :: (Numeric r, Numeric r2, Numeric r3)
  => (OR.Array 0 r -> OR.Array 0 r2 -> OR.Array 0 r3)
  -> OR.Array n r -> OR.Array n r2 -> OR.Array n r3
tzipWith0NR f = OR.zipWithA (\x y -> tunScalarR $ f (tscalarR x) (tscalarR y))
                -- bad type: liftVR2 . Numeric.LinearAlgebra.Devel.zipVectorWith

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZR
--
-- Note how tindexZR is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, NumAndShow r)
          => ShapeInt (m + n) -> OR.Array (p + n) r
          -> (IndexInt m -> IndexInt p)
          -> OR.Array (m + n) r
tgatherZR sh t f =
  let shm = takeShape @m sh
      s = sizeShape shm
      l = [ OR.toVector $ t `tindexZR` f (fromLinearIdx fromIntegral shm i)
          | i <- [0 .. fromIntegral s - 1] ]
  in OR.fromVector (shapeToList sh) $ LA.vjoin l

tgatherZ1R :: forall p n r. (KnownNat p, KnownNat n, NumAndShow r)
           => Int -> OR.Array (p + n) r -> (Int64 -> IndexInt p)
           -> OR.Array (1 + n) r
tgatherZ1R 0 t _ = OR.fromList (0 : drop (valueOf @p) (OR.shapeL t)) []
tgatherZ1R k t f =
  let l = map (\i -> t `tindexZR` f i) [0 .. fromIntegral k - 1]
  in OR.ravel $ ORB.fromList [k] l

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tcastR :: (Numeric r1, Numeric r2, KnownNat n, Real r1, Fractional r2)
       => OR.Array n r1 -> OR.Array n r2
tcastR = liftVR (V.map realToFrac)

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tfromIntegralR :: (Numeric r1, Numeric r2, KnownNat n, Integral r1)
               => OR.Array n r1 -> OR.Array n r2
tfromIntegralR = liftVR (V.map fromIntegral)

tscalarR
  :: Numeric r
  => r -> OR.Array 0 r
tscalarR = OR.scalar

tunScalarR
  :: Numeric r
  => OR.Array 0 r -> r
tunScalarR = OR.unScalar

tscaleByScalarR :: (Numeric r, KnownNat n)
                => r -> OR.Array n r -> OR.Array n r
tscaleByScalarR s = liftVR (LA.scale s)

toIndexOfR :: IndexInt n -> Index n (FlipR OR.Array Int64 0)
toIndexOfR ix = FlipR . tscalarR <$> ix

fromIndexOfR :: Index n (FlipR OR.Array Int64 0) -> IndexInt n
fromIndexOfR ixOf = tunScalarR . runFlipR <$> ixOf


-- * Shaped tensor operations

type Int64Sh (n :: Nat) = ShapedNat n Int64

type IndexIntSh sh = IndexS sh Int64

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r. (NumAndShow r, KnownShS sh, KnownShS (Sh.Drop n sh))
         => OS.Array sh r
         -> [(IndexIntSh (Sh.Take n sh), OS.Array (Sh.Drop n sh) r)]
         -> OS.Array sh r
updateNS arr upd | Dict <- lemShapeFromKnownShS (Proxy @sh)
                 , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Drop n sh)) =
  let values = OS.toVector arr
      sh = knownShS @sh
      f !t (ix, u) =
        let v = OS.toVector u
            i = gcastWith (unsafeCoerce Refl
                           :: sh :~: Sh.Take n sh X.++ Sh.Drop n sh)
                $ fromIntegral
                $ ShapedList.unShapedNat
                $ ShapedList.toLinearIdx @(Sh.Take n sh) @(Sh.Drop n sh)
                                         fromIntegral sh ix
        in LA.vjoin [V.take i t, v, V.drop (i + V.length v) t]
  in OS.fromVector (foldl' f values upd)

{- TODO
tminIndexS
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh, KnownNat n
                       , KnownShS (Sh.Init (n ': sh)) )
  => OS.Array (n ': sh) r -> OS.Array (Sh.Init (n ': sh)) r2
tminIndexS | Dict <- lemShapeFromKnownShS (Proxy @sh)
           , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Init (n ': sh))) =
  let f :: KnownNat m => OS.Array '[m] r -> OS.Array '[] r2
      f = OS.scalar . fromIntegral . LA.minIndex . OS.toVector
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat @shRank _proxy) ->
              gcastWith (unsafeCoerce Refl
                           :: Sh.Take (Sh.Rank sh) (n ': sh) X.++ '[]
                              :~: Sh.Init (n ': sh) ) $
              gcastWith (unsafeCoerce Refl
                           :: Sh.Drop (Sh.Rank sh) (n ': sh) :~: '[m]) $
              gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: shRank) $
                -- to avoid adding @KnownNat (Sh.Rank sh)@ all over the code
              OS.rerank @(Sh.Rank sh) (f @m)
            Nothing -> error "tmaxIndexS: impossible someNatVal error"
        Nothing -> error "tmaxIndexS: impossible someNatVal error"

tmaxIndexS
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh, KnownNat n
                       , KnownShS (Sh.Init (n ': sh)) )
  => OS.Array (n ': sh) r -> OS.Array (Sh.Init (n ': sh)) r2
tmaxIndexS | Dict <- lemShapeFromKnownShS (Proxy @sh)
           , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Init (n ': sh))) =
  let f :: KnownNat m => OS.Array '[m] r -> OS.Array '[] r2
      f = OS.scalar . fromIntegral . LA.maxIndex . OS.toVector
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat @shRank _proxy) ->
              gcastWith (unsafeCoerce Refl
                           :: Sh.Take (Sh.Rank sh) (n ': sh) X.++ '[]
                              :~: Sh.Init (n ': sh) ) $
              gcastWith (unsafeCoerce Refl
                           :: Sh.Drop (Sh.Rank sh) (n ': sh) :~: '[m]) $
              gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: shRank) $
                -- to avoid adding @KnownNat (Sh.Rank sh)@ all over the code
              OS.rerank @(Sh.Rank sh) (f @m)
            Nothing -> error "tmaxIndexS: impossible someNatVal error"
        Nothing -> error "tmaxIndexS: impossible someNatVal error"
-}

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tfloorS :: forall r r2 sh.
           (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2, KnownShS sh)
        => OS.Array sh r -> OS.Array sh r2
tfloorS | Dict <- lemShapeFromKnownShS (Proxy @sh) = liftVS (V.map floor)

tindexNS
  :: forall sh1 sh2 r.
     OS.Array (sh1 X.++ sh2) r -> IndexIntSh sh1 -> OS.Array sh2 r
tindexNS (SS.A (SG.A OI.T{strides, offset, values})) ix =
  let l = ShapedList.indexToList ix
      linear = offset + sum (zipWith (*) (map fromIntegral l) strides)
      plen = length l  -- length of prefix being indexed out of
  in
    SS.A (SG.A OI.T{ strides = drop plen strides
                   , offset = linear
                   , values })

-- Note that after vectorization, the index with type IndexIntSh sh1
-- may not fit within the type-level shape, which we catch in the @ixInBounds@
-- and return 0, so it's fine. Similarly in gather and scatter.
tindexZS
  :: forall sh1 sh2 r. (NumAndShow r, KnownShS sh2, KnownShS (sh1 X.++ sh2))
  => OS.Array (sh1 X.++ sh2) r -> IndexIntSh sh1 -> OS.Array sh2 r
tindexZS v ix | Dict <- lemShapeFromKnownShS (Proxy @sh2)
              , Dict <- lemShapeFromKnownShS (Proxy @(sh1 X.++ sh2)) =
  let sh = OS.shapeL v
  in if ixInBounds (ShapedList.indexToList ix) sh
     then tindexNS v ix
     else 0

tindex0S
  :: Numeric r
  => OS.Array sh r -> IndexIntSh sh -> r
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way

-- Sum the outermost dimension.
--
-- No NOINLINE, because apparently nothing breaks and hmatrix, etc.
-- also don't put NOINLINE in the functions using FFI.
tsumS
  :: forall n sh r. (KnownNat n, Numeric r, RowSum r, KnownShS sh)
  => OS.Array (n ': sh) r -> OS.Array sh r
tsumS (SS.A (SG.A (OI.T (_ : ss) o vt))) | V.length vt == 1 =
  SS.A (SG.A (OI.T ss o (V.map (* valueOf @n) vt)))
tsumS t | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  case knownShS @(n ': sh) of
    (:$$) _ ZSS -> OS.scalar $ tsum0S t
    (:$$) @_ @sh2 k _ ->
      OS.fromVector $ unsafePerformIO $ do  -- unsafe only due to FFI
        v <- V.unsafeThaw $ OS.toVector t
        VM.unsafeWith v $ \ptr -> do
          let len2 = sizeT @sh2
          v2 <- VM.new len2
          VM.unsafeWith v2 $ \ptr2 -> do
            rowSum len2 (fromInteger $ fromSNat k) ptr ptr2
            void $ V.unsafeFreeze v
            V.unsafeFreeze v2

-- Sum the innermost dimension (at least at rank 2; TODO: generalize).
tsumInS
  :: forall m n sh r. (KnownNat n, Numeric r, RowSum r, KnownNat m, KnownShS sh)
  => OS.Array (m ': n ': sh) r -> OS.Array (m ': sh) r
tsumInS t | Dict <- lemShapeFromKnownShS (Proxy @sh) = case OS.shapeL t of
  [] -> error "tsumInS: null shape"
{-
  k2 : 0 : [] ->
    0  -- the shape is known from sh, so no ambiguity
-}
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

tsum0S
  :: forall sh r. (Numeric r, KnownShS sh)
  => OS.Array sh r -> r
tsum0S (SS.A (SG.A (OI.T _ _ vt))) | V.length vt == 1 =
  fromIntegral (sizeT @sh) * vt V.! 0
-- tsumInS t@(SS.A (SG.A (OI.T _ _ vt))) | V.length vt == 1 =
tsum0S (SS.A (SG.A t)) =
  LA.sumElements $ OI.toUnorderedVectorT (shapeT @sh) t

tdot0S
  :: forall sh r. (Numeric r, KnownShS sh)
  => OS.Array sh r -> OS.Array sh r -> r
tdot0S (SS.A (SG.A (OI.T _ _ vt))) (SS.A (SG.A (OI.T _ _ vu)))
  | V.length vt == 1 && V.length vu == 1 =
      fromIntegral (sizeT @sh) * vt V.! 0 * vu V.! 0
tdot0S t u | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.toVector t LA.<.> OS.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0S (t * u)

tdot1InS
  :: (NumAndShow r, RowSum r, KnownNat m, KnownNat n)
  => OS.Array '[m, n] r -> OS.Array '[m, n] r -> OS.Array '[m] r
tdot1InS t@(SS.A (SG.A (OI.T _ _ vt))) u@(SS.A (SG.A (OI.T _ _ vu))) =
  if V.length vt == 1 || V.length vu == 1
  then tsumInS (t * u)
  else let lt = map OS.toVector $ tunravelToListS t
           lu = map OS.toVector $ tunravelToListS u
           l = zipWith (LA.<.>) lt lu
       in OS.fromList l

tmatvecmulS
  :: forall m n r. (Numeric r, KnownNat m, KnownNat n)
  => OS.Array '[m, n] r -> OS.Array '[n] r -> OS.Array '[m] r
tmatvecmulS t u =
  let t2 = OS.toVector t
      u2 = OS.toVector u
  in OS.fromVector $ LA.reshape (valueOf @n) t2 LA.#> u2

tmatmul2S
  :: forall m n p r. (Numeric r, KnownNat m, KnownNat n, KnownNat p)
  => OS.Array '[m, n] r -> OS.Array '[n, p] r -> OS.Array '[m, p] r
tmatmul2S t u =
  let t2 = OS.toVector t
      u2 = OS.toVector u
  in OS.fromVector $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by LA.vjoin, but this is done on demand).
-- TODO: optimize updateNS and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZS :: forall r sh2 p sh.
              (NumAndShow r, KnownShS sh, KnownShS sh2, KnownShS (Sh.Drop p sh))
           => OS.Array (sh2 X.++ Sh.Drop p sh) r
           -> (IndexIntSh sh2 -> IndexIntSh (Sh.Take p sh))
           -> OS.Array sh r
tscatterZS t f | Dict <- lemShapeFromKnownShS (Proxy @sh)
               , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Drop p sh)) =
  let sh2 = knownShS @sh2
      g ix =
        let ix2 = f ix
        in if ixInBounds (ShapedList.indexToList ix2) (shapeT @sh)
           then M.insertWith (++) ix2
                  [OS.toVector $ tindexNS @sh2 @(Sh.Drop p sh) t ix]
           else id
      ivs = foldr g M.empty [ ShapedList.fromLinearIdx fromIntegral sh2
                              $ ShapedList.shapedNat $ fromIntegral i
                            | i <- [0 .. sizeT @sh2 - 1] ]
  in updateNS 0 $ map (second $ OS.fromVector . sum) $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S :: forall r n2 p sh.
               (NumAndShow r, KnownNat n2, KnownShS sh, KnownShS (Sh.Drop p sh))
            => OS.Array (n2 ': Sh.Drop p sh) r
            -> (Int64Sh n2 -> IndexIntSh (Sh.Take p sh))
            -> OS.Array sh r
tscatterZ1S t f | Dict <- lemShapeFromKnownShS (Proxy @sh) =
    sum $ imap (\i ti ->
                   let ix2 = f $ ShapedList.shapedNat $ fromIntegral i
                   in if ixInBounds (ShapedList.indexToList ix2)
                                    (shapeT @sh)
                      then updateNS 0 [(ix2, ti)]
                      else 0)
        $ tunravelToListS t

tfromListS
  :: forall n sh r. (Numeric r, KnownNat n, KnownShS sh)
  => NonEmpty (OS.Array sh r) -> OS.Array (n ': sh) r
tfromListS l | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.ravel $ OSB.fromList $ NonEmpty.toList l

tfromList0NS
  :: forall r sh. (Numeric r, KnownShS sh)
  => [r] -> OS.Array sh r
tfromList0NS | Dict <- lemShapeFromKnownShS (Proxy @sh) = OS.fromList

tfromVectorS
  :: forall n sh r. (Numeric r, KnownNat n, KnownShS sh)
  => Data.Vector.Vector (OS.Array sh r) -> OS.Array (n ': sh) r
tfromVectorS l | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.ravel $ OSB.fromVector $ V.convert l

tfromVector0NS
  :: forall r sh. (Numeric r, KnownShS sh)
  => Data.Vector.Vector r -> OS.Array sh r
tfromVector0NS l | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.fromVector $ V.convert l

treplicateS
  :: forall n sh r. (Numeric r, KnownNat n, KnownShS sh)
  => OS.Array sh r -> OS.Array (n ': sh) r
treplicateS u | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  case knownShS @sh of
    ZSS -> OS.constant (OS.unScalar u)
    _ -> OS.ravel $ OSB.constant u

treplicate0NS
  :: forall r sh. (Numeric r, KnownShS sh)
  => r -> OS.Array sh r
treplicate0NS | Dict <- lemShapeFromKnownShS (Proxy @sh) = OS.constant

tappendS
  :: forall r m n sh. (Numeric r, KnownNat m, KnownNat n, KnownShS sh)
  => OS.Array (m ': sh) r -> OS.Array (n ': sh) r -> OS.Array ((m + n) ': sh) r
tappendS | Dict <- lemShapeFromKnownShS (Proxy @sh) = OS.append

tsliceS
  :: forall i n k sh r. KnownNat i
  => OS.Array (i + n + k ': sh) r -> OS.Array (n ': sh) r
tsliceS = OS.slice @'[ '(i, n) ]

treverseS
  :: forall n sh r. (KnownNat n, KnownShS sh)
  => OS.Array (n ': sh) r -> OS.Array (n ': sh) r
treverseS | Dict <- lemShapeFromKnownShS (Proxy @sh) = OS.rev @'[0]

treshapeS
  :: forall r sh sh2.
     (Numeric r, KnownShS sh, KnownShS sh2, Sh.Size sh ~ Sh.Size sh2)
  => OS.Array sh r -> OS.Array sh2 r
treshapeS | Dict <- lemShapeFromKnownShS (Proxy @sh)
          , Dict <- lemShapeFromKnownShS (Proxy @sh2) = OS.reshape

tbuild1S
  :: forall n sh r. (KnownNat n, Numeric r, KnownShS sh)
  => (Int64Sh n -> OS.Array sh r) -> OS.Array (n ': sh) r
tbuild1S f | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  let k = valueOf @n
  in OS.ravel $ OSB.fromList
     $ map (f . ShapedList.shapedNat) [0 .. k - 1]  -- hope this fuses

tmap0NS
  :: forall r r2 sh. (Numeric r, Numeric r2, KnownShS sh)
  => (OS.Array '[] r -> OS.Array '[] r2) -> OS.Array sh r -> OS.Array sh r2
tmap0NS f | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.mapA (tunScalarS . f . tscalarS)
            -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)
            -- bad type: liftVS . LA.cmap

tzipWith0NS
  :: forall r1 r2 r sh. (Numeric r1, Numeric r2, Numeric r, KnownShS sh)
  => (OS.Array '[] r1 -> OS.Array '[] r2 -> OS.Array '[] r)
  -> OS.Array sh r1 -> OS.Array sh r2 -> OS.Array sh r
tzipWith0NS f | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  OS.zipWithA (\x y -> tunScalarS $ f (tscalarS x) (tscalarS y))
                -- bad type: liftVS2 . Numeric.LinearAlgebra.Devel.zipVectorWith

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZS
--
-- Note how tindexZS is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZS :: forall sh2 p sh r.
             ( NumAndShow r, KnownShS sh, KnownShS sh2, KnownShS (Sh.Drop p sh)
             , KnownShS (sh2 X.++ Sh.Drop p sh) )
          => OS.Array sh r
          -> (IndexIntSh sh2 -> IndexIntSh (Sh.Take p sh))
          -> OS.Array (sh2 X.++ Sh.Drop p sh) r
tgatherZS t f | Dict <- lemShapeFromKnownShS (Proxy @sh)
              , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Drop p sh))
              , Dict <- lemShapeFromKnownShS
                          (Proxy @(sh2 X.++ Sh.Drop p sh)) =
  let sh2 = knownShS @sh2
      s = sizeT @sh2
      l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh)
          $ [ OS.toVector
                (t `tindexZS` f (ShapedList.fromLinearIdx fromIntegral sh2
                                 $ ShapedList.shapedNat $ fromIntegral i)
                 :: OS.Array (Sh.Drop p sh) r)
            | i <- [0 .. s - 1] ]
  in OS.fromVector $ LA.vjoin l

tgatherZ1S :: forall n2 p sh r.
              (KnownNat n2, NumAndShow r, KnownShS sh, KnownShS (Sh.Drop p sh))
           => OS.Array sh r -> (Int64Sh n2 -> IndexIntSh (Sh.Take p sh))
           -> OS.Array (n2 ': Sh.Drop p sh) r
tgatherZ1S t f | Dict <- lemShapeFromKnownShS (Proxy @sh)
               , Dict <- lemShapeFromKnownShS (Proxy @(Sh.Drop p sh)) =
  let l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh)
          $ map (\i -> t `tindexZS` f (ShapedList.shapedNat i))
                [0 .. valueOf @n2 - 1]
  in OS.ravel $ OSB.fromList l

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tcastS :: forall r1 r2 sh.
          (Numeric r1, Numeric r2, KnownShS sh, Real r1, Fractional r2)
       => OS.Array sh r1 -> OS.Array sh r2
tcastS | Dict <- lemShapeFromKnownShS (Proxy @sh) = liftVS (V.map realToFrac)

-- TODO: use Convert, fromInt/toInt and fromZ/toZ from hmatrix
tfromIntegralS :: forall r1 r2 sh .
                  (Numeric r1, Numeric r2, KnownShS sh, Integral r1)
               => OS.Array sh r1 -> OS.Array sh r2
tfromIntegralS | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  liftVS (V.map fromIntegral)

tscalarS
  :: Numeric r
  => r -> OS.Array '[] r
tscalarS = OS.scalar

tunScalarS
  :: Numeric r
  => OS.Array '[] r -> r
tunScalarS = OS.unScalar

tscaleByScalarS :: forall r sh. (Numeric r, KnownShS sh)
                => r -> OS.Array sh r -> OS.Array sh r
tscaleByScalarS s | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  liftVS (LA.scale s)

toIndexOfS :: IndexIntSh sh -> IndexS sh (FlipR OR.Array Int64 0)
toIndexOfS ix = FlipR . tscalarR <$> ix

fromIndexOfS :: IndexS sh (FlipR OR.Array Int64 0) -> IndexIntSh sh
fromIndexOfS ixOf = tunScalarR . runFlipR <$> ixOf
