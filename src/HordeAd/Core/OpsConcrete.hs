{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.OpsConcrete
  () where

import Prelude hiding (foldl')

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Foldable qualified as Foldable
import Data.Function ((&))
import Data.Int (Int64)
import Data.List (foldl', mapAccumL, mapAccumR)
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import GHC.Exts (IsList (..))
import GHC.IsList qualified as IsList
import GHC.TypeLits
  (KnownNat, sameNat, type (+))
import Numeric.LinearAlgebra (Numeric)
import Numeric.LinearAlgebra qualified as LA
import Type.Reflection (typeRep)
import Data.Vector.Strict qualified as Data.Vector

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise1)
import Data.Array.Mixed.Lemmas
import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal
import Data.Array.Mixed.Types (Init, unsafeCoerceRefl)
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Permutation qualified as Permutation

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Unwind
import HordeAd.Core.OpsADVal
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.ConvertTensor

-- * Tensor classes instance

instance LetTensor RepN where
  ttlet = (&)
  toShare = id
  tunshare = id
  tD _stk t DummyDualTarget{} = t
  tfold k _ stk f x0 as = foldl' f x0 (tunravelToListShare k stk as)
  tscan k@(SNat @k) nstk stk f x0 as =
    tfromVector (SNat @(1 + k)) nstk
    $ V.scanl' f x0 (V.fromList $ tunravelToListShare k stk as)

instance ShareTensor RepN where
  tshare = id
  tunpair (RepN (t1, t2)) = (RepN t1, RepN t2)

instance BaseTensor RepN where
  -- Ranked ops
  rshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.rshape . unRepN
  rlength @_ @r | Dict <- eltDictRep (knownSTK @r) =
    sNatValue . Nested.rrank . unRepN
  trfromVector @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rfromListOuter . NonEmpty.fromList . V.toList . V.map unRepN
  trfromVector0N @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    RepN . tfromVector0NR sh . V.map unRepN
  trunravelToList @_ @r | Dict <- eltDictRep (knownSTK @r) =
    map RepN . Nested.rtoListOuter . unRepN
  trsum t = case tftk knownSTK t of
    FTKR _ FTKScalar ->  -- optimized
      RepN . Nested.rsumOuter1 . unRepN $ t
    FTKR _ x ->
      let l = trunravelToList t
          sh = shrTail $ rshape t
      in foldr (taddTarget knownSTK) (tconstantTarget 0 (FTKR sh x)) l
        -- RepN has a ShareTensor instance, so taddTarget arguments
        -- don't need to be duplicable
  trsum0 @_ @r t = case knownSTK @r of
    STKScalar ->  -- optimized
      RepN . Nested.rscalar . Nested.rsumAllPrim . unRepN $ t
    _ -> trsum . rflatten $ t
  {-# INLINE trdot0 #-}  -- this doesn't want to specialize
  trdot0 u v = RepN $ Nested.rscalar $ Nested.rdot (unRepN u) (unRepN v)
  trdot1In u v = RepN $ Nested.rdot1Inner (unRepN u) (unRepN v)
  {-# INLINE trmatvecmul #-}  -- this doesn't want to specialize
  trmatvecmul m v = trsum (rtr (trreplicate (rwidth m) v * m))
  trmatmul2 m1 m2 = RepN $ tmatmul2R (unRepN m1) (unRepN m2)
  trreplicate @_ @r k | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rreplicate (k :$: ZSR) . unRepN
  trreplicate0N @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rreplicate sh . unRepN
  trindex = tindexZR
  trindex0 = tindex0R
  trscatter = tscatterZR
  trscatter1 = tscatterZ1R
  trgather = tgatherZR
  trgather1 = tgatherZ1R
  trconcrete = RepN
  trfloor = RepN . liftVR (V.map floor) . unRepN
  trfromIntegral = RepN . liftVR (V.map fromIntegral) . unRepN
  {-# INLINE trcast #-}  -- this doesn't want to specialize
  trcast = RepN . liftVR (V.map realToFrac) . unRepN
  trminIndex = RepN . tminIndexR . unRepN
  trmaxIndex = RepN . tmaxIndexR . unRepN
  triota n = RepN $ Nested.rfromList1 $ NonEmpty.map fromInteger
             $ NonEmpty.fromList [0 .. fromIntegral n - 1]
  trappend @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    RepN $ Nested.rappend (unRepN u) (unRepN v)
  trslice @_ @r i n | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rslice i n . unRepN
  trreverse @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rrev1 . unRepN
  trtranspose @_ @r perm | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rtranspose perm . unRepN
  trreshape @_ @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rreshape sh . unRepN
  trbuild1 @_ @r k f | Dict <- eltDictRep (knownSTK @r) =
    RepN $ tbuild1R k (unRepN . f . RepN)
  trmap0N @_ @r @r1 f t = case (knownSTK @r1, knownSTK @r) of
    (STKScalar, STKScalar) -> RepN $ tmap0NR (unRepN . f . RepN) (unRepN t)
    _ ->  -- TODO: how to call the default implementation?
      rbuild (rshape t) (f . trindex t)
  trzipWith0N @_ @r1 @r2 @r f t u =
    case (knownSTK @r1, knownSTK @r2, knownSTK @r) of
      (STKScalar, STKScalar, STKScalar) ->
        RepN $ tzipWith0NR (\v w -> unRepN $ f (RepN v) (RepN w))
                           (unRepN t) (unRepN u)
      _ ->  -- TODO: how to call the default implementation?
        rbuild (rshape u) (\ix -> f (trindex t ix) (trindex u ix))

  -- Shaped ops
  sshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.sshape . unRepN
  slength @_ @r | Dict <- eltDictRep (knownSTK @r) =
    sNatValue . Nested.srank . unRepN
  tsfromVector @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.sfromListOuter SNat . NonEmpty.fromList . V.toList
    . V.map unRepN
  tsfromVector0N @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . tfromVector0NS . V.map unRepN
  tsunravelToList @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    map RepN . Nested.stoListOuter . unRepN
  tssum t = case tftk knownSTK t of
    FTKS _ FTKScalar ->  -- optimized
      RepN . Nested.ssumOuter1 . unRepN $ t
    FTKS _ x ->
      let l = tsunravelToList t
          sh = shsTail $ sshape t
      in foldr (taddTarget knownSTK) (tconstantTarget 0 (FTKS sh x)) l
  tssum0 @sh @r t | SNat <- shsProduct (knownShS @sh) = case knownSTK @r of
    STKScalar ->  -- optimized
      RepN . Nested.sscalar . Nested.ssumAllPrim . unRepN $ t
    _ -> tssum . sflatten $ t
  {-# INLINE tsdot0 #-}  -- this doesn't want to specialize
  tsdot0 u v  =
    RepN $ Nested.sscalar $ Nested.sdot (unRepN u) (unRepN v)
  tsdot1In (SNat @n) u v =
    RepN $ Nested.sdot1Inner (Proxy @n) (unRepN u) (unRepN v)
  {-# INLINE tsmatvecmul #-}  -- this doesn't want to specialize
  tsmatvecmul m v = tssum (str (tsreplicate knownShS v * m))
  tsmatmul2 m1 m2 = RepN $ tmatmul2S (unRepN m1) (unRepN m2)
  tsindex = tindexZS
  tsindex0 = tindex0S
  -- Performance depends a lot on the number and size of tensors.
  -- If tensors are not tiny, memory taken by underlying vectors matters most
  -- and this implementation is probbaly optimal in this respect
  -- (the only new vectors are created by V.concat, but this is done on demand).
  -- TODO: optimize updateNS and make it consume and forget arguments
  -- one by one to make the above true
  --
  -- Note how ix being in bounds is checked. The semantics of the operation
  -- permits index out of bounds and then no tensors is added at such an index.
  tsscatter @shm @shn @shp t f =
    let shpshn = knownShS @shp `shsAppend` knownShS @shn
    in withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
       case tftk knownSTK t of
         FTKS _ x@FTKScalar ->  -- optimized
           gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
           gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
           let zero = tconstantTarget 0 (FTKS shpshn x)
               shm = knownShS @shm
               s = shsSize shm
               g ix =
                 let ix2 = f $ fmap RepN ix
                 in if ixInBounds (map unRepN $ toList $ ix2)
                                  (shsToList shpshn)
                    then M.insertWith (V.zipWith (+)) ix2
                           (Nested.stoVector
                            $ tindexNS @_ @shm @shn (unRepN t) ix)
                    else id
               ivs = foldr g M.empty [ fromLinearIdxS fromIntegral shm
                                       $ fromIntegral i
                                     | i <- [0 .. s - 1] ]
           in withKnownShS shpshn $
              updateNS @(Rank shp) zero
              $ map (second $ RepN . Nested.sfromVector (knownShS @shn))
              $ M.assocs ivs
         FTKS _ x | Dict <- eltDictRep (ftkToSTK x) ->
           gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
           gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
           let zero = tconstantTarget 0 (FTKS shpshn x)
               shm = knownShS @shm
               s = shsSize shm
               g ix =
                 let ix2 = f $ fmap RepN ix
                 in if ixInBounds (map unRepN $ toList $ ix2)
                                  (shsToList shpshn)
                    then M.insertWith (taddTarget knownSTK) ix2
                           (RepN
                            $ tindexNS @_ @shm @shn (unRepN t) ix)
                    else id
               ivs = foldr g M.empty [ fromLinearIdxS fromIntegral shm
                                       $ fromIntegral i
                                     | i <- [0 .. s - 1] ]
           in withKnownShS shpshn $
              updateNS @(Rank shp) zero
              $ M.assocs ivs
  tsscatter1 = tscatterZ1S
  -- The semantics of the operation permits index out of bounds
  -- and the result of such indexing is def.
  tsgather @shm @shn @_ @r t f =
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
    case knownSTK @r of
      STKScalar ->  -- optimized
        let shm = knownShS @shm
            s = shsSize shm
            l = [ stoVector
                  $ tsindex @_ @_ @shn
                      t (f (fmap RepN
                            $ fromLinearIdxS fromIntegral shm i))
                | i <- [0 .. fromIntegral s - 1] ]
        in RepN $ Nested.sfromVector (knownShS @shm `shsAppend` knownShS @shn)
           $ V.concat l
      _ ->
        withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
        sbuild @(Rank shm) (\ix -> t `tsindex` f ix)
  tsgather1 = tgatherZ1S
  tsconcrete = RepN
  tsfloor = RepN . liftVS (V.map floor) . unRepN
  tsfromIntegral = RepN . tfromIntegralS . unRepN
  {-# INLINE tscast #-}  -- this doesn't want to specialize
  tscast = RepN . liftVS (V.map realToFrac) . unRepN
  tsminIndex a = RepN . tminIndexS . unRepN $ a
  tsmaxIndex a = RepN . tmaxIndexS . unRepN $ a
  tsiota @n = case NonEmpty.nonEmpty [0 .. valueOf @n - 1] of
    Nothing -> case sameNat (Proxy @n) (Proxy @0) of
      Just Refl -> RepN $ Nested.semptyArray ZSS
      Nothing -> error "siota: wrong rank"
    Just l -> RepN $ Nested.sfromList1 SNat $ NonEmpty.map fromInteger l
  tsappend @_ @_ @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    RepN $ Nested.sappend (unRepN u) (unRepN v)
  tsslice @_ @_ @_ @_ @r i n _ | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.sslice i n . unRepN
  tsreverse @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.srev1 . unRepN
  tsbuild1 @_ @_ @r f | Dict <- eltDictRep (knownSTK @r) =
    RepN $ tbuild1S (unRepN . f . RepN)
  tsmap0N @sh @r @r1 f v = case (knownSTK @r1, knownSTK @r) of
    (STKScalar, STKScalar) ->
      RepN $ tmap0NS (unRepN . f . RepN) (unRepN v)
    _ | Refl <- lemAppNil @sh ->
      -- TODO: how to call the default implementation?
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
      $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
      $ sbuild @(Rank sh) (f . tsindex v)
  tszipWith0N @sh @r1 @r2 @r f t u =
    case (knownSTK @r1, knownSTK @r2, knownSTK @r) of
      (STKScalar, STKScalar, STKScalar) ->
        RepN $ tzipWith0NS (\v w -> unRepN $ f (RepN v) (RepN w))
                           (unRepN t) (unRepN u)
      _ | Refl <- lemAppNil @sh ->
        -- TODO: how to call the default implementation?
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
        $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
        $ sbuild @(Rank sh) (\ix -> f (tsindex t ix) (tsindex u ix))

  -- Shaped ops
  xshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.mshape . unRepN
  xlength @_ @r | Dict <- eltDictRep (knownSTK @r) =
    sNatValue . Nested.mrank . unRepN
  txfromVector @n @sh @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mcast (Nested.SKnown (SNat @n) :!% knownShX @sh)
    . Nested.mfromListOuter . NonEmpty.fromList . V.toList
    . V.map unRepN
  txfromVector0N @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    RepN . tfromVector0NX sh . V.map unRepN
  txunravelToList @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    map RepN . Nested.mtoListOuter . unRepN
  txsum t = case tftk knownSTK t of
    FTKX _ FTKScalar ->  -- optimized
      RepN . Nested.msumOuter1 . unRepN $ t
    FTKX _ x ->
      let l = txunravelToList t
          sh = shxTail $ xshape t
      in foldr (taddTarget knownSTK) (tconstantTarget 0 (FTKX sh x)) l
  txsum0 @_ @r t =
   case knownSTK @r of
    STKScalar ->  -- optimized
      RepN . Nested.mscalar . Nested.msumAllPrim . unRepN $ t
    _ -> withSNat (shxSize $ xshape t) $ \snat ->
      txsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  {-# INLINE txdot0 #-}  -- this doesn't want to specialize
  txdot0 u v =
    RepN $ Nested.mscalar $ Nested.mdot (unRepN u) (unRepN v)
  txdot1In @_ @n u v =
    RepN $ Nested.mdot1Inner (Proxy @(Just n)) (unRepN u) (unRepN v)
  txmatvecmul mm mn m v =
    withKnownShX (ssxFromShape $ mn :$% ZSX) $
    withKnownShX (ssxFromShape $ mm :$% mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @m) ->
    withSNat (fromSMayNat' mn) $ \(SNat @n) ->
      xmcast (ssxFromShape (mm :$% ZSX))
      $ txsum (xtr (txreplicate @_ @m
                      (xmcast (ssxFromShape (Nested.SKnown (SNat @n)
                                             :$% ZSX)) v)
                    * xmcast (ssxFromShape (Nested.SKnown (SNat @m)
                                            :$% Nested.SKnown (SNat @n)
                                            :$% ZSX)) m))
  {-# INLINE txmatvecmul #-}  -- this doesn't want to specialize
  txmatmul2 m1 m2 = RepN $ tmatmul2X (unRepN m1) (unRepN m2)
  txreplicate @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mreplicate (Nested.SKnown SNat :$% ZSX) . unRepN
  txreplicate0N @sh @r sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mreplicate sh . unRepN
  txindex = tindexZX
  txindex0 = tindex0X
  txscatter @shm @shn @shp sh t f =
    withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
    gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
    case tftk knownSTK t of
      FTKX _ x@FTKScalar ->  -- optimized
        let zero = tconstantTarget 0 (FTKX sh x)
            shm = shxTakeSSX (Proxy @shn) (xshape t) (knownShX @shm)
            shDropP = shxDropSSX (xshape t) (knownShX @shm)
            s = shxSize shm
            g ix =
              let ix2 = f $ fmap RepN ix
              in if ixInBounds (map unRepN $ toList $ ix2) (shxToList sh)
                 then M.insertWith (V.zipWith (+)) ix2
                        (Nested.mtoVector
                         $ tindexNX @_ @shm @shn (unRepN t) ix)
                 else id
            ivs = foldr g M.empty [ fromLinearIdxX fromIntegral shm
                                    $ fromIntegral i
                                  | i <- [0 .. s - 1] ]
        in updateNX @(Rank shp) zero
           $ map (second $ RepN . Nested.mfromVector shDropP)
           $ M.assocs ivs
      FTKX _ x | Dict <- eltDictRep (ftkToSTK x) ->
        let zero = tconstantTarget 0 (FTKX sh x)
            shm = shxTakeSSX (Proxy @shn) (xshape t) (knownShX @shm)
            s = shxSize shm
            g ix =
              let ix2 = f $ fmap RepN ix
              in if ixInBounds (map unRepN $ toList $ ix2) (shxToList sh)
                 then M.insertWith (taddTarget knownSTK) ix2
                        (RepN
                         $ tindexNX @_ @shm @shn (unRepN t) ix)
                 else id
            ivs = foldr g M.empty [ fromLinearIdxX fromIntegral shm
                                    $ fromIntegral i
                                  | i <- [0 .. s - 1] ]
        in updateNX @(Rank shp) zero
           $ M.assocs ivs
  txscatter1 = tscatterZ1X
  txgather @shm @shn @_ @r sh t f =
    gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
    case knownSTK @r of
      STKScalar ->  -- optimized
        let shm = shxTakeSSX (Proxy @shn) sh (knownShX @shm)
            s = shxSize shm
            l = [ xtoVector
                  $ txindex @_ @_ @shn
                      t (f (fmap RepN
                            $ fromLinearIdxX fromIntegral shm i))
                | i <- [0 .. fromIntegral s - 1] ]
        in RepN $ Nested.mfromVector sh $ V.concat l
      _ ->
        withKnownShX (ssxFromShape sh) $
        xbuild @(Rank shm) sh (\ix -> t `txindex` f ix)
  txgather1 = tgatherZ1X
  txconcrete = RepN
  txfloor = RepN . liftVX (V.map floor) . unRepN
  txfromIntegral = RepN . liftVX (V.map fromIntegral) . unRepN
  {-# INLINE txcast #-}  -- this doesn't want to specialize
  txcast = RepN . liftVX (V.map realToFrac) . unRepN
  txminIndex = RepN . tminIndexX . unRepN
  txmaxIndex = RepN . tmaxIndexX . unRepN
  txiota @n = let n = valueOf @n
                  t = Nested.mfromList1 $ NonEmpty.map fromInteger
                      $ NonEmpty.fromList [0 .. n - 1]
              in RepN $ Nested.mcast (Nested.SKnown (SNat @n) :!% ZKX) t
  txappend @_ @_ @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    RepN $ Nested.mappend (unRepN u) (unRepN v)
  txslice @_ @_ @_ @_ @r i n _ | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mslice i n . unRepN
  txreverse @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mrev1 . unRepN
  txtranspose @perm @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mtranspose (Permutation.makePerm @perm) . unRepN
  txreshape @_ @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mreshape sh . unRepN
  txbuild1 @_ @_ @r f | Dict <- eltDictRep (knownSTK @r) =
    RepN $ tbuild1X (unRepN . f . RepN)

  -- Scalar ops
  tkconcrete = RepN
  tkfloor = RepN . floor . unRepN
  tkfromIntegral = RepN . fromIntegral . unRepN
  tkcast = RepN . realToFrac . unRepN

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk (RepN t) = tftkG stk t
  tconcrete _ = id
  tpair !u !v = RepN (unRepN u, unRepN v)
  tproject1 = RepN . fst . unRepN
  tproject2 = RepN . snd . unRepN
  tsreplicate @_ @_ @x _sh | Dict <- eltDictRep (knownSTK @x) =
    RepN . Nested.sreplicate (SNat :$$ ZSS) . unRepN
  tsreplicate0N @sh @r sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.sreplicate sh . unRepN
  tstranspose @_ @_ @r perm | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.stranspose perm . unRepN
  tsreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    RepN . Nested.sreshape sh . unRepN
  -- The eta-expansion below is needed for typing.
  tmapAccumRDer _ k _ bftk eftk f _df _rf acc0 es =
    oRtmapAccumR k bftk eftk (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es
  tmapAccumLDer _ k _ bftk eftk f _df _rf acc0 es =
    oRtmapAccumL k bftk eftk (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es
  tApply f x = RepN $ f $ unRepN x
  tlambda _ f x = unRepN $ unHFun f $ RepN x
  tcond _ b u v = if b then u else v
  tprimalPart = id
  tdualPart stk t = DummyDualTarget (tftk stk t)
  tfromPrimal _ t = t
  tfromDual (DummyDualTarget ftk) = tconstantTarget 0 ftk
  tScale _ _ t = t
  -- The code for trevDt and tfwd in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  trev @x xftk h =
    let rf :: RepORArray x -> RepORArray (ADTensorKind x)
        rf !a = unRepN $ fst $ crevOnHVector Nothing (unHFun h)
                                             xftk (RepN a)
    in rf
  trevDt @x @z xftk h =
    let rf :: RepORArray (TKProduct (ADTensorKind z) x) -> RepORArray (ADTensorKind x)
        rf !db_a = unRepN $ fst
                   $ crevOnHVector (Just $ RepN $ fst db_a) (unHFun h)
                                   xftk (RepN $ snd db_a)
    in rf
  tfwd @x @z xftk h =
    let df :: RepORArray (TKProduct (ADTensorKind x) x)
          -> RepORArray (ADTensorKind z)
        df !da_a = unRepN $ fst
                   $ cfwdOnHVector xftk (RepN $ snd da_a)
                                   (unHFun h) (RepN $ fst da_a)
    in df

  tfromVector snat@SNat stk v = assert (V.length v == sNatValue snat)
                                $ case stk of
    STKScalar -> tsfromVector $ V.map sfromK v
    STKR SNat x | Dict <- lemKnownSTK x -> trfromVector v
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsfromVector v
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txfromVector v
    STKProduct stk1 stk2 ->
      let (v1, v2) = V.unzip $ V.map tunpair v
      in tpair (tfromVector snat stk1 v1) (tfromVector snat stk2 v2)

  tconstantTarget = constantTarget
  tdefTarget = defTarget
  taddTarget = addTarget
  tmultTarget = multTarget
  tdotTarget = dotTarget

instance ConvertTensor RepN where
  rzip (RepN (a, b)) = RepN $ Nested.rzip a b
  runzip a = let (!a1, !a2) = Nested.runzip $ unRepN a
             in RepN (a1, a2)
  szip (RepN (a, b)) = RepN $ Nested.szip a b
  sunzip a = let (!a1, !a2) = Nested.sunzip $ unRepN a
             in RepN (a1, a2)
  xzip (RepN (a, b)) = RepN $ Nested.mzip a b
  xunzip a = let (!a1, !a2) = Nested.munzip $ unRepN a
             in RepN (a1, a2)

  tfromS ystk zstk v = case (ystk, zstk) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> v
    (STKS ZSS (STKScalar @ry), STKScalar @rz) ->
      case testEquality (typeRep @ry) (typeRep @rz) of
        Just Refl -> kfromS v
        Nothing -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKR nx zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          rfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shx $
          xfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKProduct ystk1 ystk2, STKProduct zstk1 zstk2) ->
        let (u1, u2) = tunpair v
        in tpair (tfromS ystk1 zstk1 u1) (tfromS ystk2 zstk2 u2)
    _ -> error "tfromS: wrong tensor kinds"

  kfromR = RepN . Nested.runScalar . unRepN
  kfromS = RepN . Nested.sunScalar . unRepN
  kfromX = RepN . Nested.munScalar . unRepN
  rfromK = RepN . Nested.rscalar . unRepN
  rfromS @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.stoRanked . unRepN
  {-# SPECIALIZE rfromS :: KnownShS sh => RepN (TKS sh Double) -> RepN (TKR (Rank sh) Double) #-}
  {-# SPECIALIZE rfromS :: KnownShS sh => RepN (TKS sh Float) -> RepN (TKR (Rank sh) Float) #-}
  rfromX @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.mtoRanked . unRepN
  sfromK = RepN . Nested.sscalar . unRepN
  sfromR @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . flip Nested.rcastToShaped knownShS . unRepN
  sfromX @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . flip Nested.mcastToShaped knownShS . unRepN
  xfromK = RepN . Nested.mscalar . unRepN
  xfromR @sh @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.rcastToMixed (knownShX @sh) . unRepN
  xfromS @_ @sh' @r | Dict <- eltDictRep (knownSTK @r) =
    RepN . Nested.scastToMixed (knownShX @sh') . unRepN

  xnestR @sh1 @m @x sh | Dict <- eltDictRep (knownSTK @x)
                       , Refl <- lemRankReplicate (SNat @m) =
    RepN
    . Nested.castCastable
        @(Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing) (RepORArray x)))
        (Nested.CastXX (Nested.CastXR Nested.CastId))
    . Nested.mnest sh
    . unRepN
  xnestS @sh1 @sh2 @x sh | Dict <- eltDictRep (knownSTK @x) =
    RepN
    . Nested.castCastable
        @(Nested.Mixed sh1 (Nested.Mixed (MapJust sh2) (RepORArray x)))
        (Nested.CastXX (Nested.CastXS Nested.CastId))
    . Nested.mnest sh
    . unRepN
  xnest @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    RepN . Nested.mnest sh . unRepN
  xunNestR @sh1 @m @x | Dict <- eltDictRep (knownSTK @x) =
    RepN
    . Nested.munNest
    . Nested.castCastable
        @(Nested.Mixed sh1 (Nested.Ranked m (RepORArray x)))
        (Nested.CastXX (Nested.CastRX Nested.CastId))
    . unRepN
  xunNestS @sh1 @sh2 @x | Dict <- eltDictRep (knownSTK @x) =
    RepN
    . Nested.munNest
    . Nested.castCastable
        @(Nested.Mixed sh1 (Nested.Shaped sh2 (RepORArray x)))
        (Nested.CastXX (Nested.CastSX Nested.CastId))
    . unRepN
  xunNest = RepN . Nested.munNest . unRepN

  tpairConv = tpair
  tunpairConv = tunpair


-- * MapAccum internal definitions

ravel :: forall k y.
         SNat k -> SingletonTK y -> [RepN y]
      -> RepN (BuildTensorKind k y)
ravel k stk l = tfromVector k stk (V.fromList l)

unravel :: forall k y.
           SNat k -> SingletonTK y -> RepN (BuildTensorKind k y)
        -> [RepN y]
unravel = tunravelToListShare

oRtmapAccumR
  :: forall k accy by ey.
     SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> (RepN accy -> RepN ey -> RepN (TKProduct accy by))
  -> RepN accy
  -> RepN (BuildTensorKind k ey)
  -> RepN (TKProduct accy (BuildTensorKind k by))
oRtmapAccumR k bftk eftk f acc0 es = case sNatValue k of
  0 -> tpair acc0 (treplicate k (ftkToSTK bftk) (tconstantTarget 0 bftk))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumR g acc0 (unravel k (ftkToSTK eftk) es)
    in tpair xout (ravel k (ftkToSTK bftk) lout)
      -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRtmapAccumL
  :: forall k accy by ey.
     SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> (RepN accy -> RepN ey -> RepN (TKProduct accy by))
  -> RepN accy
  -> RepN (BuildTensorKind k ey)
  -> RepN (TKProduct accy (BuildTensorKind k by))
oRtmapAccumL k bftk eftk f acc0 es = case sNatValue k of
  0 -> tpair acc0 (treplicate k (ftkToSTK bftk) (tconstantTarget 0 bftk))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumL g acc0 (unravel k (ftkToSTK eftk) es)
    in tpair xout (ravel k (ftkToSTK bftk) lout)


-- * Ranked internal definitions

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t
{-
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u) -}

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m x. (KnownNat n, KnownNat m, KnownSTK x)
         => RepN (TKR2 (n + m) x) -> [(IxROf RepN n, RepN (TKR2 m x))]
         -> RepN (TKR2 (n + m) x)
updateNR arr upd = case knownSTK @x of
  STKScalar ->  -- optimized
    let values = rtoVector arr
        sh = rshape arr
        f !t (ix, u) =
          let v = rtoVector u
              i = fromIntegral $ unRepN $ toLinearIdx @n @m fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.rfromVector sh (foldl' f values upd)
  _ ->
    let arrNested = rnest (SNat @n) arr
        shNested = rshape arrNested
        f i v = case lookup (fromLinearIdx
                               @n (RepN . fromIntegral)
                               shNested ((RepN . fromIntegral) i)) upd of
          Just u -> rnest (SNat @0) u
          Nothing -> v
    in runNest $ trfromVector0N shNested $ V.fromList
       $ imap f $ trunravelToList $ rflatten arrNested

tminIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tminIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . ixrHead . Nested.rminIndexPrim
  in Nested.rrerank SNat ZSR f v

tmaxIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tmaxIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . ixrHead . Nested.rmaxIndexPrim
  in Nested.rrerank SNat ZSR f v

-- We could generalize by unwinding and only then doing the PrimElt things,
-- but we'd need a type family that says "replace this underlying scalars
-- by this one", which makes things too complicated.
--
-- We could also expose `liftVR` in the user API, but in addition
-- to the main function argument such as floor or cast, it'd need the function's
-- derivative, just as with mapAccums. Maybe it's better to generalize even more
-- and permit arbitrary extra ops if given their derivatives.
liftVR
  :: (Nested.PrimElt r1, Nested.PrimElt r2)
  => (VS.Vector r1 -> VS.Vector r2)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2
liftVR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))
{-# SPECIALIZE liftVR :: (VS.Vector Double -> VS.Vector Double) -> Nested.Ranked n Double -> Nested.Ranked n Double #-}
{-# SPECIALIZE liftVR :: (VS.Vector Float -> VS.Vector Float) -> Nested.Ranked n Float -> Nested.Ranked n Float #-}
{-# SPECIALIZE liftVR :: (VS.Vector Double -> VS.Vector Float) -> Nested.Ranked n Double -> Nested.Ranked n Float #-}
{-# SPECIALIZE liftVR :: (VS.Vector Float -> VS.Vector Double) -> Nested.Ranked n Float -> Nested.Ranked n Double #-}

ixInBounds :: [Int64] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: (Nested.Elt r, Show r, KnownNat m, KnownNat n)
  => Nested.Ranked (m + n) r -> IxR m Int64 -> Nested.Ranked n r
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
  :: forall r m n. (KnownSTK r, KnownNat m, KnownNat n)
  => RepN (TKR2 (m + n) r) -> IxROf RepN m -> RepN (TKR2 n r)
tindexZR v ixRepN | Dict <- showDictRep (knownSTK @r)
                  , Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in case tftk knownSTK v of
    FTKR sh x ->
     if ixInBounds (Foldable.toList ix) (Foldable.toList sh)
     then RepN $ tindexNR (unRepN v) ix
     else tdefTarget (FTKR (dropShape @m sh) x)

tindex0R
  :: forall r m. (KnownSTK r, KnownNat m)
  => RepN (TKR2 m r) -> IxROf RepN m -> RepN (TKR2 0 r)
tindex0R v ixRepN | Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in case tftk knownSTK v of
    FTKR sh x ->
      if ixInBounds (toList ix) (toList sh)
      then let arr = Nested.rscalar
                     $ Nested.rindex (unRepN v) (fmap fromIntegral ix)
           in RepN arr
      else tdefTarget (FTKR ZSR x)
{- TODO: see above
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
-}

tmatmul2R
  :: (Nested.PrimElt r, Numeric r)
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
              (KnownNat p, KnownNat m, KnownNat n, KnownSTK r)
           => IShR (p + n) -> RepN (TKR2 (m + n) r)
           -> (IxROf RepN m -> IxROf RepN p)
           -> RepN (TKR2 (p + n) r)
tscatterZR sh t f
 | Dict <- eltDictRep (knownSTK @r) = case tftk knownSTK t of
  FTKR _ x@FTKScalar ->  -- optimized
    let zero = tconstantTarget 0 (FTKR sh x)
        (shm, shDropP) = splitAt_Shape @m $ rshape t
        s = shrSize shm
        g ix =
          let ix2 = f $ fmap RepN ix
          in if ixInBounds (map unRepN $ toList ix2) (toList sh)
             then M.insertWith (V.zipWith (+)) ix2
                               (Nested.rtoVector $ unRepN t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ map (second $ RepN . Nested.rfromVector shDropP)
       $ M.assocs ivs
  FTKR _ x | Dict <- showDictRep (ftkToSTK x) ->
    let zero = tconstantTarget 0 (FTKR sh x)
        (shm, _) = splitAt_Shape @m $ rshape t
        s = shrSize shm
        g ix =
          let ix2 = f $ fmap RepN ix
          in if ixInBounds (map unRepN $ toList ix2) (toList sh)
             then M.insertWith (taddTarget knownSTK) ix2
                               (RepN $ unRepN t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling Nested.rfromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (KnownSTK r, KnownNat p, KnownNat n)
            => IShR (p + n) -> RepN (TKR2 (1 + n) r)
            -> (IntOf RepN -> IxROf RepN p)
            -> RepN (TKR2 (p + n) r)
tscatterZ1R sh t f = case tftk knownSTK t of
  FTKR _ x ->
    let zero = tconstantTarget 0 (FTKR sh x)
        lt = trunravelToList t
        g i ti = let ix2 = f $ RepN $ fromIntegral i
                 in if ixInBounds (map unRepN $ toList ix2) (toList sh)
                    then updateNR zero [(ix2, ti)]
                    else zero
        lu = imap g lt
    in foldr (taddTarget knownSTK) zero lu

tfromVector0NR
  :: Nested.KnownElt r
  => IShR n -> Data.Vector.Vector (Nested.Ranked 0 r) -> Nested.Ranked n r
tfromVector0NR sh l = case NonEmpty.nonEmpty $ V.toList l of
  Nothing -> Nested.rreshape sh Nested.remptyArray
  Just nl -> Nested.rfromListLinear sh $ NonEmpty.map Nested.runScalar nl

tbuild1R
  :: forall r n. (Nested.KnownElt r, KnownNat n)
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tbuild1R k f = case NonEmpty.nonEmpty [0 .. fromIntegral k - 1] of
  Nothing -> case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> Nested.remptyArray
    Nothing -> error "rbuild1: shape ambiguity"
  Just l -> Nested.rfromListOuter $ NonEmpty.map f l  -- hope this fuses

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r) -> Nested.Ranked n r1 -> Nested.Ranked n r
tmap0NR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.mliftPrim (Nested.runScalar . f . Nested.rscalar ))
      -- too slow: tbuildNR (Nested.rshape v) (\ix -> f $ v `tindexNR` ix)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2 -> Nested.Ranked n r
tzipWith0NR f =
  Nested.Internal.arithPromoteRanked2
    (Nested.Internal.mliftPrim2
       (\x y -> Nested.runScalar $ f (Nested.rscalar x) (Nested.rscalar y)))

-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is def.
tgatherZR :: forall m p n r.
             (KnownNat m, KnownNat p, KnownNat n, KnownSTK r)
          => IShR (m + n) -> RepN (TKR2 (p + n) r)
          -> (IxROf RepN m -> IxROf RepN p)
          -> RepN (TKR2 (m + n) r)
tgatherZR sh t f = case knownSTK @r of
  STKScalar ->  -- optimized
    let shm = takeShape @m sh
        s = shrSize shm
        l = [ rtoVector
              $ t `trindex` f (fmap RepN $ fromLinearIdx fromIntegral shm i)
            | i <- [0 .. fromIntegral s - 1] ]
    in RepN $ Nested.rfromVector sh $ V.concat l
  _ -> rbuild sh (\ix -> t `trindex` f ix)

tgatherZ1R :: forall p n r.
              (KnownNat p, KnownNat n, KnownSTK r)
           => Int -> RepN (TKR2 (p + n) r)
           -> (IntOf RepN -> IxROf RepN p)
           -> RepN (TKR2 (1 + n) r)
tgatherZ1R k t f = case knownSTK @r of
  STKScalar ->  -- optimized
    trfromVector $ V.fromList $ map (\i -> t `trindex` f (RepN i))
                                    [0 .. fromIntegral k - 1]
  _ -> trbuild1 k (\ix -> t `trindex` f ix)


-- * Shaped internal definitions

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r.
            ( KnownSTK r, KnownShS sh, KnownShS (Drop n sh)
            , KnownShS (Take n sh) )
         => RepN (TKS2 sh r)
         -> [(IxSOf RepN (Take n sh), RepN (TKS2 (Drop n sh) r))]
         -> RepN (TKS2 sh r)
updateNS arr upd = case knownSTK @r of
  STKScalar ->
    let values = stoVector arr
        sh = knownShS @sh
        f !t (ix, u) =
          let v = stoVector u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unRepN
                  $ toLinearIdxS @(Take n sh) @(Drop n sh)
                                 fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.sfromVector knownShS (foldl' f values upd)
  _ -> case shsProduct (knownShS @(Take n sh)) of
    SNat ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = snest (knownShS @(Take n sh)) arr
          shNested = sshape arrNested
          f i v = case lookup (fromLinearIdxS
                                 @(Take n sh) (RepN . fromIntegral)
                                 shNested ((RepN . fromIntegral) i)) upd of
            Just u -> snest (knownShS @'[]) u
            Nothing -> v
      in sunNest @_ @(Take n sh) $ tsfromVector0N $ V.fromList
         $ imap f $ tsunravelToList $ sflatten arrNested

tfromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2)
               => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tfromIntegralS = liftVS (V.map fromIntegral)

tminIndexS
  :: forall n sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tminIndexS v | sh1@(_ :$$ sh) <- Nested.sshape v =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . ixsHead . Nested.sminIndexPrim
  in case sh of
    ZSS -> f @n v
    _ | SNat @m <- shsLast sh1 ->
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) ++ '[m] :~: n ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
      Nested.srerank @'[m] @'[] @(Init (n ': sh))
                     (shsInit sh1) ZSS (f @m) v

tmaxIndexS
  :: forall n sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tmaxIndexS v | sh1@(_ :$$ sh) <- Nested.sshape v =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . ixsHead . Nested.smaxIndexPrim
  in case sh of
    ZSS -> f @n v
    _ | SNat @m <- shsLast sh1 ->
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) ++ '[m] :~: n ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
      Nested.srerank @'[m] @'[] @(Init (n ': sh))
                     (shsInit sh1) ZSS (f @m) v

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
liftVS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))
{-# SPECIALIZE liftVS :: (VS.Vector Double -> VS.Vector Double) -> Nested.Shaped sh Double -> Nested.Shaped sh Double #-}
{-# SPECIALIZE liftVS :: (VS.Vector Float -> VS.Vector Float) -> Nested.Shaped sh Float -> Nested.Shaped sh Float #-}
{-# SPECIALIZE liftVS :: (VS.Vector Double -> VS.Vector Float) -> Nested.Shaped sh Double -> Nested.Shaped sh Float #-}
{-# SPECIALIZE liftVS :: (VS.Vector Float -> VS.Vector Double) -> Nested.Shaped sh Float -> Nested.Shaped sh Double #-}

tindexNS
  :: Nested.Elt r
  => Nested.Shaped (sh1 ++ sh2) r -> IxS sh1 Int64 -> Nested.Shaped sh2 r
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

-- Note that after vectorization, the index may not fit within
-- the type-level shape, which we catch in the @ixInBounds@
-- and return def, so it's fine. Similarly in gather and scatter.
tindexZS
  :: forall r sh1 sh2. (KnownSTK r, KnownShS sh1, KnownShS sh2)
  => RepN (TKS2 (sh1 ++ sh2) r) -> IxSOf RepN sh1 -> RepN (TKS2 sh2 r)
tindexZS v ixRepN | Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
     case tftk knownSTK v of
       FTKS sh x ->
         if ixInBounds (Foldable.toList ix) (shsToList sh)
         then RepN $ tindexNS (unRepN v) ix
         else tdefTarget (FTKS knownShS x)

tindex0S
  :: forall r sh. (KnownSTK r, KnownShS sh)
  => RepN (TKS2 sh r) -> IxSOf RepN sh -> RepN (TKS2 '[] r)
tindex0S v ixRepN | Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in case tftk knownSTK v of
    FTKS sh x ->
      if ixInBounds (toList ix) (toList sh)
      then let arr = Nested.sscalar
                     $ Nested.sindex (unRepN v) (fmap fromIntegral ix)
           in RepN arr
      else tdefTarget (FTKS ZSS x)
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

tmatmul2S
  :: forall m n p r.
     (Nested.PrimElt r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n, p] r -> Nested.Shaped '[m, p] r
tmatmul2S t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S
  :: forall r n2 shn shp.
     (KnownSTK r, KnownNat n2, KnownShS shn, KnownShS shp)
  => RepN (TKS2 (n2 ': shn) r)
  -> (IntOf RepN -> IxSOf RepN shp)
  -> RepN (TKS2 (shp ++ shn) r)
tscatterZ1S t f = case tftk knownSTK t of
  FTKS _ x ->
    gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
    let shpshn = knownShS @shp `shsAppend` knownShS @shn
        zero = tconstantTarget 0 (FTKS shpshn x)
        lt = tsunravelToList t
        g i ti = let ix2 = f $ RepN $ fromIntegral i
                 in if ixInBounds (map unRepN $ Foldable.toList ix2)
                                  (shsToList shpshn)
                    then withKnownShS shpshn $
                         updateNS @(Rank shp) zero [(ix2, ti)]
                    else zero
        lu = imap g lt
    in foldr (taddTarget (STKS shpshn (knownSTK @r))) zero lu

tfromVector0NS
  :: forall r sh. (Nested.KnownElt r, KnownShS sh)
  => Data.Vector.Vector (Nested.Shaped '[] r) -> Nested.Shaped sh r
tfromVector0NS l = case NonEmpty.nonEmpty $ V.toList l of
  Nothing -> case testEquality (shsProduct (knownShS @sh)) (SNat @0) of
    Just Refl -> Nested.sreshape (knownShS @sh)
                 $ Nested.semptyArray (knownShS @sh)
    Nothing -> error "tfromListLinearS: empty list, but not shape"
  Just nl -> Nested.sfromListLinear knownShS $ NonEmpty.map Nested.sunScalar nl

tbuild1S
  :: forall k sh r. (KnownNat k, KnownShS sh, Nested.KnownElt r)
  => (Int64 -> Nested.Shaped sh r) -> Nested.Shaped (k ': sh) r
tbuild1S f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
  Nothing -> gcastWith (unsafeCoerceRefl :: k :~: 0) $
             Nested.semptyArray knownShS
  Just l -> Nested.sfromListOuter SNat $ NonEmpty.map f l  -- hope this fuses

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
tmap0NS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.mliftPrim (Nested.sunScalar . f . Nested.sscalar))
      -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
tzipWith0NS f =
  Nested.Internal.arithPromoteShaped2
    (Nested.Internal.mliftPrim2
       (\x y -> Nested.sunScalar $ f (Nested.sscalar x) (Nested.sscalar y)))

tgatherZ1S
  :: forall r n2 shn shp.
     (KnownSTK r, KnownNat n2, KnownShS shn, KnownShS shp)
  => RepN (TKS2 (shp ++ shn) r)
  -> (IntOf RepN -> IxSOf RepN shp)
  -> RepN (TKS2 (n2 ': shn) r)
tgatherZ1S t f =
  case knownSTK @r of
    STKScalar ->  -- optimized
      tsfromVector $ V.fromList $ map (\i -> t `tsindex` f (RepN i))
                                      [0 .. valueOf @n2 - 1]
    _ -> tsbuild1 (\ix -> t `tsindex` f ix)


-- * Mixed internal definitions

updateNX :: forall n sh r.
            (KnownSTK r, KnownShX (Drop n sh), KnownShX (Take n sh))
         => RepN (TKX2 sh r)
         -> [(IxXOf RepN (Take n sh), RepN (TKX2 (Drop n sh) r))]
         -> RepN (TKX2 sh r)
updateNX arr upd = case knownSTK @r of
  STKScalar ->
    let values = xtoVector arr
        sh = xshape arr
        f !t (ix, u) =
          let v = xtoVector u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unRepN
                  $ toLinearIdxX @(Take n sh) @(Drop n sh)
                                 fromIntegral sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in RepN $ Nested.mfromVector (xshape arr) (foldl' f values upd)
  _ | Dict <- eltDictRep (knownSTK @r) ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = xnest (knownShX @(Take n sh)) arr
          shNested = xshape arrNested
          f i v = case lookup (fromLinearIdxX
                                 @(Take n sh) (RepN . fromIntegral)
                                 shNested ((RepN . fromIntegral) i)) upd of
            Just u -> xnest ZKX u
            Nothing -> v
      in withSNat (shxSize shNested) $ \snat ->
           xunNest @_ @(Take n sh) $ txfromVector0N shNested $ V.fromList
           $ imap f $ txunravelToList
           $ RepN $ Nested.mcast (Nested.SKnown snat :!% ZKX)
           $ unRepN $ xflatten arrNested

tminIndexX
  :: forall mn sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
tminIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead
          . Nested.mminIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.mrerank @'[Just m] @'[] @(Init (mn ': sh))
                     (ssxFromShape $ shxInit sh1) ZSX (f @(Just m)) v

tmaxIndexX
  :: forall mn sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
tmaxIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead
          . Nested.mmaxIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.mrerank @'[Just m] @'[] @(Init (mn ': sh))
                     (ssxFromShape $ shxInit sh1) ZSX (f @(Just m)) v

liftVX
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Mixed sh r1 -> Nested.Mixed sh r
liftVX f =
  Nested.Internal.mliftNumElt1
    (`Mixed.Internal.Arith.liftVEltwise1` f)
{-# SPECIALIZE liftVX :: (VS.Vector Double -> VS.Vector Double) -> Nested.Mixed sh Double -> Nested.Mixed sh Double #-}
{-# SPECIALIZE liftVX :: (VS.Vector Float -> VS.Vector Float) -> Nested.Mixed sh Float -> Nested.Mixed sh Float #-}
{-# SPECIALIZE liftVX :: (VS.Vector Double -> VS.Vector Float) -> Nested.Mixed sh Double -> Nested.Mixed sh Float #-}
{-# SPECIALIZE liftVX :: (VS.Vector Float -> VS.Vector Double) -> Nested.Mixed sh Float -> Nested.Mixed sh Double #-}

tindexNX
  :: Nested.Elt r
  => Nested.Mixed (sh1 ++ sh2) r -> IxX sh1 Int64 -> Nested.Mixed sh2 r
tindexNX v ix = Nested.mindexPartial v (fmap fromIntegral ix)

tindexZX
  :: forall r sh1 sh2. (KnownSTK r, KnownShX sh1, KnownShX sh2)
  => RepN (TKX2 (sh1 ++ sh2) r) -> IxXOf RepN sh1 -> RepN (TKX2 sh2 r)
tindexZX v ixRepN | Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
     case tftk knownSTK v of
       FTKX sh x ->
         if ixInBounds (Foldable.toList ix) (shxToList sh)
         then RepN $ tindexNX (unRepN v) ix
         else tdefTarget (FTKX (shxDropSSX sh (knownShX @sh1)) x)

tindex0X
  :: forall r sh. (KnownSTK r, KnownShX sh)
  => RepN (TKX2 sh r) -> IxXOf RepN sh -> RepN (TKX2 '[] r)
tindex0X v ixRepN | Dict <- eltDictRep (knownSTK @r) =
  let ix = fmap unRepN ixRepN
  in case tftk knownSTK v of
    FTKX sh x ->
      if ixInBounds (toList ix) (toList sh)
      then let arr = Nested.mscalar
                     $ Nested.mindex (unRepN v) (fmap fromIntegral ix)
           in RepN arr
      else tdefTarget (FTKX ZSX x)

tmatmul2X
  :: forall m n p r.
     (Nested.PrimElt r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
  => Nested.Mixed '[Just m, Just n] r -> Nested.Mixed '[Just n, Just p] r
  -> Nested.Mixed '[Just m, Just p] r
tmatmul2X t u =
  let t2 = Nested.mtoVector t
      u2 = Nested.mtoVector u
  in Nested.mfromVector (IsList.fromList [valueOf @m, valueOf @p]) $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

tscatterZ1X
  :: forall r n2 shn shp.
     (KnownSTK r, KnownNat n2, KnownShX shn, KnownShX shp)
  => IShX (shp ++ shn) -> RepN (TKX2 (Just n2 ': shn) r)
  -> (IntOf RepN -> IxXOf RepN shp)
  -> RepN (TKX2 (shp ++ shn) r)
tscatterZ1X sh t f =
  case tftk knownSTK t of
    FTKX _ x ->
      withKnownShX (ssxFromShape sh) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
      let zero = tconstantTarget 0 (FTKX sh x)
          lt = txunravelToList t
          g i ti = let ix2 = f $ RepN $ fromIntegral i
                   in if ixInBounds (map unRepN $ Foldable.toList ix2)
                                    (shxToList sh)
                      then updateNX @(Rank shp) zero [(ix2, ti)]
                      else zero
          lu = imap g lt
      in foldr (taddTarget knownSTK) zero lu

tfromVector0NX
  :: forall r sh. Nested.KnownElt r
  => IShX sh -> Data.Vector.Vector (Nested.Mixed '[] r) -> Nested.Mixed sh r
tfromVector0NX sh l = case NonEmpty.nonEmpty $ V.toList l of
  Nothing -> if shxSize sh == 0
             then Nested.mreshape sh $ Nested.memptyArray sh
             else error "tfromListLinearS: empty list, but not shape"
  Just nl -> Nested.mfromListLinear sh $ NonEmpty.map Nested.munScalar nl

tbuild1X
  :: forall k sh r. (KnownNat k, KnownShX sh, Nested.KnownElt r)
  => (Int64 -> Nested.Mixed sh r)
  -> Nested.Mixed (Just k ': sh) r
tbuild1X f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
  Nothing -> case testEquality (knownShX @sh) ZKX of
    Just Refl -> gcastWith (unsafeCoerceRefl :: k :~: 0) $
                 Nested.memptyArray ZSX
    Nothing -> error "xbuild1: shape ambiguity"
  Just l -> Nested.mcast (Nested.SKnown (SNat @k) :!% knownShX)
            $ Nested.mfromListOuter $ NonEmpty.map f l  -- hope this fuses

tgatherZ1X
  :: forall r n2 shn shp.
     (KnownSTK r, KnownShX shn, KnownShX shp)
  => SNat n2 -> RepN (TKX2 (shp ++ shn) r)
  -> (IntOf RepN -> IxXOf RepN shp)
  -> RepN (TKX2 (Just n2 ': shn) r)
tgatherZ1X SNat t f =
  case knownSTK @r of
    STKScalar ->  -- optimized
      txfromVector $ V.fromList $ map (\i -> t `txindex` f (RepN i))
                                      [0 .. valueOf @n2 - 1]
    _ -> txbuild1 @_ @n2 (\ix -> t `txindex` f ix)
