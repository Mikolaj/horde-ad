{-# LANGUAGE AllowAmbiguousTypes, ImpredicativeTypes #-}
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
import qualified Data.Array.Shape as Sh
import qualified Data.Foldable as Foldable
import           Data.Int (Int64)
import           Data.List (foldl')
import           Data.List.Index (imap)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict as M
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           Data.Type.Ord (Compare)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.Exts (IsList (..))
import qualified GHC.IsList as IsList
import           GHC.TypeLits
  (KnownNat, Nat, SomeNat (..), someNatVal, type (+), type (<=))
import           Numeric.LinearAlgebra (Numeric)
import qualified Numeric.LinearAlgebra as LA
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Internal.Arith as Mixed.Internal.Arith
import qualified Data.Array.Mixed.Permutation as Permutation
import qualified Data.Array.Mixed.Shape as X
import qualified Data.Array.Mixed.Types as X
import qualified Data.Array.Nested as Nested
import qualified Data.Array.Nested.Internal.Mixed as Nested.Internal.Mixed
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


-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t


-- * Ranked tensor operations

-- We often debug around here, so let's add Show and obfuscate it
-- to avoid warnings that it's unused. The addition silences warnings upstream.
type NumAndShow r = (Nested.Elt r, Nested.PrimElt r, Mixed.Internal.Arith.NumElt r, Num r, Show r)

type IndexInt n = Index n Int64

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m a. NumAndShow a
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
  :: NumAndShow r
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

tfloorR :: (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2)
        => Nested.Ranked n r -> Nested.Ranked n r2
tfloorR = liftVR (V.map floor)

liftVR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r
liftVR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftNumElt1
       (flip Mixed.Internal.Arith.liftVEltwise1 f))

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

-- | Sum the outermost dimension.
tsumR
  :: forall n r. NumAndShow r
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r
tsumR = Nested.rsumOuter1

-- | Sum all elements of a tensor.
tsum0R
  :: NumAndShow r
  => Nested.Ranked n r -> r
tsum0R = Nested.rsumAllPrim

tdot0R
  :: NumAndShow r
  => Nested.Ranked n r -> Nested.Ranked n r -> r
tdot0R = Nested.rdot
{-
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

tunravelToListR :: NumAndShow r => Nested.Ranked (1 + n) r -> [Nested.Ranked n r]
tunravelToListR = Nested.rtoListOuter

tmatvecmulR
  :: (NumAndShow r, Numeric r)
  => Nested.Ranked 2 r -> Nested.Ranked 1 r -> Nested.Ranked 1 r
tmatvecmulR t u =
  let t2 = Nested.rtoVector t
      u2 = Nested.rtoVector u
      (trows, tcols) = case Foldable.toList $ Nested.rshape t of
        [r, c] -> (r, c)
        _ -> error "tmatvecmulR: impossible wrong shape"
  in Nested.rfromVector (IsList.fromList [trows])
     $ LA.reshape tcols t2 LA.#> u2

tmatmul2R
  :: (NumAndShow r, Numeric r)
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
              (KnownNat m, KnownNat n, NumAndShow r)
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
tscatterZ1R :: NumAndShow r
            => ShapeInt (p + n) -> Nested.Ranked (1 + n) r -> (Int64 -> IndexInt p)
            -> Nested.Ranked (p + n) r
tscatterZ1R sh t f =
  sum $ imap (\i ti ->
                 let ix2 = f $ fromIntegral i
                 in if ixInBounds (indexToList ix2) (shapeToList sh)
                    then updateNR (treplicate0NR sh 0) [(ix2, ti)]
                    else treplicate0NR sh 0)
      $ tunravelToListR t

tfromListR
  :: forall n r. NumAndShow r
  => NonEmpty (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tfromListR = Nested.rfromListOuter  -- TODO: make this strict

tfromList0NR
  :: NumAndShow r
  => ShapeInt n -> [r] -> Nested.Ranked n r
tfromList0NR sh = Nested.Internal.rfromListPrimLinear sh
  -- TODO: make this strict

tfromVectorR
  :: forall n r. NumAndShow r
  => Data.Vector.Vector (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tfromVectorR = tfromListR . NonEmpty.fromList . V.toList

tfromVector0NR
  :: NumAndShow r
  => ShapeInt n -> Data.Vector.Vector r -> Nested.Ranked n r
tfromVector0NR sh = tfromList0NR sh . V.toList

treplicateR
  :: forall n r. NumAndShow r
  => Int -> Nested.Ranked n r -> Nested.Ranked (1 + n) r
treplicateR n = Nested.rreplicate (n :$: ZSR)

treplicate0NR
  :: NumAndShow r
  => ShapeInt n -> r -> Nested.Ranked n r
treplicate0NR = Nested.rreplicateScal

tappendR
  :: NumAndShow r
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
  -> Nested.Ranked (1 + n) r
tappendR = Nested.rappend

tsliceR
  :: NumAndShow r
  => Int -> Int -> Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
tsliceR = Nested.rslice

treverseR
  :: NumAndShow r
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
treverseR = Nested.rrev1

ttransposeR
  :: NumAndShow r
  => Permutation.PermR -> Nested.Ranked n r -> Nested.Ranked n r
ttransposeR = Nested.rtranspose

treshapeR
  :: NumAndShow r
  => ShapeInt m -> Nested.Ranked n r -> Nested.Ranked m r
treshapeR = Nested.rreshape

tbuild1R
  :: forall n r. NumAndShow r
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tbuild1R k f =
  Nested.rfromListOuter
  $ NonEmpty.map f
  $ NonEmpty.fromList [0 .. fromIntegral k - 1]  -- hope this fuses

tmap0NR
  :: (Nested.Elt r1, Nested.Elt r, Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r) -> Nested.Ranked n r1 -> Nested.Ranked n r
tmap0NR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftPrim
       (\x -> Nested.runScalar $ f (Nested.rscalar x)))
          -- too slow: tbuildNR (tshapeR v) (\ix -> f $ v `tindexNR` ix)

tzipWith0NR
  :: (Nested.Elt r, Nested.Elt r1, Nested.Elt r2, Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2 -> Nested.Ranked n r
tzipWith0NR f =
  Nested.Internal.arithPromoteRanked2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.runScalar $ f (Nested.rscalar x) (Nested.rscalar y)))

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
tgatherZ1R k t f =
  let l = NonEmpty.map (\i -> t `tindexZR` f i)
                       (NonEmpty.fromList [0 .. fromIntegral k - 1])
  in Nested.rfromListOuter l

tcastR :: (NumAndShow r1, NumAndShow r2, Real r1, Fractional r2)
       => Nested.Ranked n r1 -> Nested.Ranked n r2
tcastR = liftVR (V.map realToFrac)

tfromIntegralR :: (NumAndShow r1, NumAndShow r2, Integral r1)
               => Nested.Ranked n r1 -> Nested.Ranked n r2
tfromIntegralR = liftVR (V.map fromIntegral)

tscalarR
  :: Nested.Elt r
  => r -> Nested.Ranked 0 r
tscalarR = Nested.rscalar

tunScalarR
  :: Nested.Elt r
  => Nested.Ranked 0 r -> r
tunScalarR = Nested.runScalar

tscaleByScalarR :: (Nested.PrimElt r, Num r)
                => r -> Nested.Ranked n r -> Nested.Ranked n r
tscaleByScalarR s = liftVR (V.map (* s))

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
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh
                       , KnownShS (Sh.Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Sh.Init (n ': sh)) r2
tminIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
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
  :: forall n sh r r2. ( NumAndShow r, NumAndShow r2, KnownShS sh
                       , KnownShS (Sh.Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Sh.Init (n ': sh)) r2
tmaxIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
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
           (NumAndShow r, RealFrac r, NumAndShow r2, Integral r2)
        => Nested.Shaped sh r -> Nested.Shaped sh r2
tfloorS = liftVS (V.map floor)

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
liftVS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftNumElt1
       (flip Mixed.Internal.Arith.liftVEltwise1 f))

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
  :: forall sh1 sh2 r. (NumAndShow r, KnownShS sh2)
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
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

-- | Sum the outermost dimension.
tsumS
  :: forall n sh r. NumAndShow r
  => Nested.Shaped (n ': sh) r -> Nested.Shaped sh r
tsumS = Nested.ssumOuter1

-- | Sum all elements of a tensor.
tsum0S
  :: forall sh r. NumAndShow r
  => Nested.Shaped sh r -> r
tsum0S = Nested.ssumAllPrim

tdot0S
  :: forall sh r. NumAndShow r
  => Nested.Shaped sh r -> Nested.Shaped sh r -> r
tdot0S = Nested.sdot

-- TODO: sdot1In :: shaped r (sh ++ [n]) -> shaped r (sh ++ [n]) -> shaped r sh
tdot1InS
  :: (NumAndShow r, KnownNat m)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[m, n] r -> Nested.Shaped '[m] r
tdot1InS t u = -- TODO: t@(SS.A (SG.A (OI.T _ _ vt))) u@(SS.A (SG.A (OI.T _ _ vu))) =
--  if V.length vt == 1 || V.length vu == Nested.sreplicateScal knownShS 1
--  then tsumInS (t * u)
--  else
    let lt = tunravelToListS t
        lu = tunravelToListS u
        l = zipWith Nested.sdot1 lt lu
    in Nested.sfromList1 SNat $ NonEmpty.fromList l

tunravelToListS :: forall r n sh. NumAndShow r
                => Nested.Shaped (n ': sh) r -> [Nested.Shaped sh r]
tunravelToListS = Nested.stoListOuter

tmatvecmulS
  :: forall m n r. (NumAndShow r, KnownNat m, KnownNat n, Numeric r)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n] r -> Nested.Shaped '[m] r
tmatvecmulS t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.reshape (valueOf @n) t2 LA.#> u2

tmatmul2S
  :: forall m n p r. (NumAndShow r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
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
               (NumAndShow r, KnownShS sh, KnownShS (Sh.Drop p sh))
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
  :: forall n sh r. (NumAndShow r, KnownNat n)
  => NonEmpty (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromListS = Nested.sfromListOuter SNat  -- TODO: make this strict

tfromList0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => [r] -> Nested.Shaped sh r
tfromList0NS = Nested.Internal.sfromListPrimLinear knownShS
  -- TODO: make this strict

tfromVectorS
  :: forall n sh r. (NumAndShow r, KnownNat n)
  => Data.Vector.Vector (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromVectorS = tfromListS . NonEmpty.fromList . V.toList

tfromVector0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => Data.Vector.Vector r -> Nested.Shaped sh r
tfromVector0NS = tfromList0NS . V.toList

treplicateS
  :: forall n sh r. (NumAndShow r, KnownNat n)
  => Nested.Shaped sh r -> Nested.Shaped (n ': sh) r
treplicateS = Nested.sreplicate (SNat @n :$$ ZSS)

treplicate0NS
  :: forall r sh. (NumAndShow r, KnownShS sh)
  => r -> Nested.Shaped sh r
treplicate0NS = Nested.sreplicateScal knownShS

tappendS
  :: forall r m n sh. NumAndShow r
  => Nested.Shaped (m ': sh) r -> Nested.Shaped (n ': sh) r -> Nested.Shaped ((m + n) ': sh) r
tappendS = Nested.sappend

tsliceS
  :: forall i n k sh r. (NumAndShow r, KnownNat i, KnownNat n)
  => Nested.Shaped (i + n + k ': sh) r -> Nested.Shaped (n ': sh) r
tsliceS = Nested.sslice (SNat @i) SNat

treverseS
  :: forall n sh r. NumAndShow r
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (n ': sh) r
treverseS = Nested.srev1

-- TODO: remove the conversion and overhaul the whole codebase
ttransposeS
  :: forall perm r sh.
     (NumAndShow r, PermC perm, X.Rank perm <= X.Rank sh )
  => Permutation.Perm perm -> Nested.Shaped sh r
  -> Nested.Shaped (Permutation.PermutePrefix perm sh) r
ttransposeS perm =
  gcastWith (unsafeCoerce Refl :: Compare (X.Rank perm) (X.Rank sh) :~: LT) $
  gcastWith (unsafeCoerce Refl
             :: Permutation.PermutePrefix perm sh :~: Permutation.PermutePrefix perm sh) $
  Nested.stranspose perm

treshapeS
  :: forall r sh sh2.
     (NumAndShow r, KnownShS sh2, Sh.Size sh ~ Sh.Size sh2)
  => Nested.Shaped sh r -> Nested.Shaped sh2 r
treshapeS = Nested.sreshape knownShS

tbuild1S
  :: forall n sh r. (KnownNat n, NumAndShow r)
  => (Int64Sh n -> Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tbuild1S f =
  let k = valueOf @n
  in Nested.sfromListOuter SNat
     $ NonEmpty.map (f . ShapedList.shapedNat)
     $ NonEmpty.fromList [0 .. k - 1]  -- hope this fuses

tmap0NS
  :: forall r1 r sh. (Nested.Elt r1, Nested.Elt r, Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
tmap0NS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftPrim
       (\x -> Nested.sunScalar $ f (Nested.sscalar x)))
          -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.Elt r, Nested.Elt r1, Nested.Elt r2, Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
tzipWith0NS f =
  Nested.Internal.arithPromoteShaped2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.sunScalar $ f (Nested.sscalar x) (Nested.sscalar y)))

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZS
--
-- Note how tindexZS is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZS :: forall sh2 p sh r.
             ( NumAndShow r, KnownShS sh2, KnownShS (Sh.Drop p sh)
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
              (NumAndShow r, KnownNat n2, KnownShS (Sh.Drop p sh))
           => Nested.Shaped sh r -> (Int64Sh n2 -> IndexIntSh (Sh.Take p sh))
           -> Nested.Shaped (n2 ': Sh.Drop p sh) r
tgatherZ1S t f =
  let l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Sh.Take p sh X.++ Sh.Drop p sh)
          $ NonEmpty.map (\i -> t `tindexZS` f (ShapedList.shapedNat i))
                         (NonEmpty.fromList [0 .. valueOf @n2 - 1])
  in Nested.sfromListOuter SNat l

tcastS :: forall r1 r2 sh.
          (NumAndShow r1, NumAndShow r2, Real r1, Fractional r2)
       => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tcastS = liftVS (V.map realToFrac)

tfromIntegralS :: forall r1 r2 sh .
                  (NumAndShow r1, NumAndShow r2, Integral r1)
               => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tfromIntegralS = liftVS (V.map fromIntegral)

tscalarS
  :: Nested.Elt r
  => r -> Nested.Shaped '[] r
tscalarS = Nested.sscalar

tunScalarS
  :: Nested.Elt r
  => Nested.Shaped '[] r -> r
tunScalarS = Nested.sunScalar

tscaleByScalarS :: forall r sh. (Nested.PrimElt r, Num r)
                => r -> Nested.Shaped sh r -> Nested.Shaped sh r
tscaleByScalarS s = liftVS (V.map (* s))

toIndexOfS :: IndexIntSh sh -> IndexS sh (ORArray Int64 0)
toIndexOfS ix = FlipR . tscalarR <$> ix

fromIndexOfS :: IndexS sh (ORArray Int64 0) -> IndexIntSh sh
fromIndexOfS ixOf = tunScalarR . runFlipR <$> ixOf
