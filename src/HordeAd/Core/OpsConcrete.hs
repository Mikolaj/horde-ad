{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete arrays backed
-- by 'Data.Vector.Storable.Vector'
-- and defined in @ox-arrays@ on the basis of @orthotope@.
module HordeAd.Core.OpsConcrete
  () where

import Prelude hiding (foldl')

import Control.Monad (forM_, when)
import Control.Monad.ST
import Data.Array.Internal.ShapedS qualified as SS
import Data.Coerce (coerce)
import Data.Default
import Data.Function ((&))
import Data.IntMap.Strict qualified as IM
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import GHC.TypeLits (KnownNat, Nat, type (+))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (shxFromShR, shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked qualified as Ranked
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped qualified as Shaped
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init, unsafeCoerceRefl)
import Data.Array.Strided.Orthotope (liftVEltwise1)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.UnwindNum

-- * Tensor classes instance

instance LetTensor Concrete where
  ttlet = (&)
  ttletPrimal = (&)
  ttletPlain = (&)
  toShare = id
  tunshare = id
  tD _stk t DummyDualTarget{} = t
  {-# INLINE tfold #-}
  tfold k _ stk f x0 es = foldl' f x0 (tunravelToListShare k stk es)
   {- This is worse than the above when the vector needs to be allocated
      due to complex strides. Apparently this happens often enough
      and checking strides is costly for small folds (but do we care?
      but then, how often do big folds work on rank 1 arrays anyway?).
   case stk of
    STKScalar ->
      let g !yn !ym = f yn (Concrete ym)
      in VS.foldl' g x0 (stoVector es)
    STKR (SNat' @0) STKScalar ->
      let g !yn !ym = f yn (rfromK $ Concrete ym)
      in VS.foldl' g x0 (rtoVector es)
    STKS ZSS STKScalar ->
      let g !yn !ym = f yn (sfromK $ Concrete ym)
      in VS.foldl' g x0 (stoVector es)
    STKX ZKX STKScalar ->
      let g !yn !ym = f yn (xfromK $ Concrete ym)
      in VS.foldl' g x0 (xtoVector es)
    _ -> foldl' f x0 (tunravelToListShare k stk es) -}
  {-# INLINE tscan #-}
  tscan k nstk stk f x0 as =
    tfromList (snatSucc k) nstk $ scanl' f x0 $ tunravelToListShare k stk as

instance ShareTensor Concrete where
  tshare = id
  {-# INLINE tunpair #-}
  tunpair (Concrete (t1, t2)) = (Concrete t1, Concrete t2)

instance BaseTensor Concrete where
  {-# INLINE rshape #-}
  rshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.rshape . unConcrete
  {-# INLINE sshape #-}
  sshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.sshape . unConcrete
  {-# INLINE xshape #-}
  xshape @_ @x | Dict <- eltDictRep (knownSTK @x) = Nested.mshape . unConcrete
  {-# INLINE tftk #-}
  tftk stk (Concrete t) = tftkG stk t
  {-# INLINE tpair #-}
  tpair !u !v = Concrete (unConcrete u, unConcrete v)
  {-# INLINE tproject1 #-}
  tproject1 = Concrete . fst . unConcrete
  {-# INLINE tproject2 #-}
  tproject2 = Concrete . snd . unConcrete
  {-# INLINE tcond #-}
  tcond _ b u v = if unConcrete b then u else v
  tkconcrete = Concrete
  trconcrete = Concrete
  tsconcrete = Concrete
  txconcrete = Concrete
  tconcrete _ = id
  {-# INLINE tkunravelToList #-}
  tkunravelToList =
    fmapConcrete . SS.toList . Nested.stoOrthotope . unConcrete
  {-# INLINE trfromVector #-}
  trfromVector @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.rfromListOuterN (V.length v) l
      Nothing -> error "rfromVector: empty vector"
  {-# INLINE trunravelToList #-}
  trunravelToList @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.rtoListOuter . unConcrete
  {-# INLINE tsfromVector #-}
  tsfromVector @_ @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.sfromListOuter SNat l
      Nothing -> error "sfromVector: empty vector"
  {-# INLINE tsunravelToList #-}
  tsunravelToList @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.stoListOuter . unConcrete
  {-# INLINE txfromVector #-}
  txfromVector @n @_ @x v | Dict <- eltDictRep (knownSTK @x) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.mfromListOuterSN (SNat @n) l
      Nothing -> error "xfromVector: empty vector"
  {-# INLINE txunravelToList #-}
  txunravelToList @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    fmapConcrete . Nested.mtoListOuter . unConcrete
  {-# INLINE tfromVector #-}
  tfromVector snat@SNat stk v = case stk of
    STKScalar -> Concrete $ Nested.sfromList1Prim snat
                 $ fmapUnConcrete $ V.toList v
    STKR SNat x | Dict <- lemKnownSTK x -> trfromVector v
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsfromVector v
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txfromVector v
    STKProduct stk1 stk2 ->
      let (v1, v2) = V.unzip $ V.map tunpair v
      in tpair (tfromVector snat stk1 v1) (tfromVector snat stk2 v2)
  {-# INLINE tfromList #-}
  tfromList snat@SNat stk l = case stk of
    STKScalar -> Concrete $ Nested.sfromList1Prim snat $ fmapUnConcrete l
    STKR SNat x | Dict <- eltDictRep x ->
      case NonEmpty.nonEmpty $ fmapUnConcrete l of
        Just nl -> Concrete $ Nested.rfromListOuterN (sNatValue snat) nl
        Nothing -> error "tfromList: empty list"
    STKS _sh x | Dict <- eltDictRep x ->
      case NonEmpty.nonEmpty $ fmapUnConcrete l of
        Just nl -> Concrete $ Nested.sfromListOuter snat nl
        Nothing -> error "tfromList: empty list"
    STKX _sh x | Dict <- eltDictRep x ->
      case NonEmpty.nonEmpty $ fmapUnConcrete l of
        Just nl -> Concrete $ Nested.mfromListOuterSN snat nl
        Nothing -> error "tfromList: empty list"
    STKProduct stk1 stk2 ->
      let (l1, l2) = unzip $ map tunpair l
      in tpair (tfromList snat stk1 l1) (tfromList snat stk2 l2)
  {-# INLINE trsum #-}
  trsum t = case tftk knownSTK t of
    FTKR _ (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.rsumOuter1Prim . unConcrete $ t  -- optimized
    FTKR _ x ->
      let l = trunravelToList t
          sh = shrTail $ rshape t
      in foldr (taddTarget knownSTK) (tdefTarget (FTKR sh x)) l
        -- Concrete has a ShareTensor instance, so taddTarget arguments
        -- don't need to be duplicable
  {-# INLINE trsum0 #-}
  trsum0 = Concrete . Nested.rsumAllPrim . unConcrete
  {-# INLINE trdot0 #-}
  trdot0 u v = Concrete $ Nested.rdot (unConcrete u) (unConcrete v)
  {-# INLINE trdot1In #-}
  trdot1In u v = Concrete $ Nested.rdot1Inner (unConcrete u) (unConcrete v)
  {-# INLINE trmatvecmul #-}
  trmatvecmul m v = trdot1In m (trreplicate (rwidth m) v)
  {-# INLINE trmatmul2 #-}
  trmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR ->
      trdot1In (trtranspose [1, 0] (trreplicate width2 m1))
               (trtranspose [0, 2, 1] (trreplicate (rwidth m1) m2))
  {-# INLINE trreplicate #-}
  trreplicate @_ @x k | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rreplicate (k :$: ZSR) . unConcrete
  {-# INLINE trreplicate0N #-}
  trreplicate0N @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rreplicate sh . unConcrete
  {-# INLINE tssum #-}
  tssum t = case tftk knownSTK t of
    FTKS _ (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.ssumOuter1Prim . unConcrete $ t  -- optimized
    FTKS _ x ->
      let l = tsunravelToList t
          sh = shsTail $ sshape t
      in foldr (taddTarget knownSTK) (tdefTarget (FTKS sh x)) l
  {-# INLINE tssum0 #-}
  tssum0 = Concrete . Nested.ssumAllPrim . unConcrete
  {-# INLINE tsdot0 #-}
  tsdot0 u v = Concrete $ Nested.sdot (unConcrete u) (unConcrete v)
  {-# INLINE tsdot1In #-}
  tsdot1In @_ (SNat @n) u v =
    Concrete $ Nested.sdot1Inner (Proxy @n) (unConcrete u) (unConcrete v)
  {-# INLINE tsmatvecmul #-}
  tsmatvecmul m v = tsdot1In SNat m (tsreplicate SNat knownShS v)
  {-# INLINE tsmatmul2 #-}
  tsmatmul2 m1 m2 =
    tsdot1In SNat
             (tstranspose (Permutation.makePerm @'[1, 0])
                          (tsreplicate SNat knownShS m1))
             (tstranspose (Permutation.makePerm @'[0, 2, 1])
                          (tsreplicate SNat knownShS m2))
  {-# INLINE tsreplicate #-}
  tsreplicate @_ @_ @x snat@SNat _sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreplicate (snat :$$ ZSS) . unConcrete
  {-# INLINE tsreplicate0N #-}
  tsreplicate0N @sh @x sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreplicate sh . unConcrete
  {-# INLINE txsum #-}
  txsum t = case tftk knownSTK t of
    FTKX _ (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
      Concrete . Nested.msumOuter1Prim . unConcrete $ t  -- optimized
    FTKX _ x ->
      let l = txunravelToList t
          sh = shxTail $ xshape t
      in foldr (taddTarget knownSTK) (tdefTarget (FTKX sh x)) l
  {-# INLINE txsum0 #-}
  txsum0 = Concrete . Nested.msumAllPrim . unConcrete
  {-# INLINE txdot0 #-}
  txdot0 u v = Concrete $ Nested.mdot (unConcrete u) (unConcrete v)
  {-# INLINE txdot1In #-}
  txdot1In @_ (SNat @n) u v =
    Concrete $ Nested.mdot1Inner (Proxy @(Just n)) (unConcrete u) (unConcrete v)
  {-# INLINE txmatvecmul #-}
  txmatvecmul mm mn m v =
    withKnownShX (ssxFromShX $ mn :$% ZSX) $
    withKnownShX (ssxFromShX $ mm :$% mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @m) ->
    withSNat (fromSMayNat' mn) $ \(SNat @n) ->
      xmcast (ssxFromShX (mm :$% ZSX))
      $ txsum (xtr (txreplicate (SNat @m) knownShX
                      (xmcast (ssxFromShX (Nested.SKnown (SNat @n)
                                             :$% ZSX)) v)
                    * xmcast (ssxFromShX (Nested.SKnown (SNat @m)
                                            :$% Nested.SKnown (SNat @n)
                                            :$% ZSX)) m))
  {-# INLINE txmatmul2 #-}
  txmatmul2 m1 m2 =
    txdot1In SNat
             (txtranspose (Permutation.makePerm @'[1, 0])
                          (txreplicate SNat knownShX m1))
             (txtranspose (Permutation.makePerm @'[0, 2, 1])
                          (txreplicate SNat knownShX m2))
  {-# INLINE txreplicate #-}
  txreplicate @_ @_ @x snat _sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mreplicate (Nested.SKnown snat :$% ZSX) . unConcrete
  {-# INLINE txreplicate0N #-}
  txreplicate0N @sh @x sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mreplicate sh . unConcrete
  trindex = tindexZR
  trindex0 = tindex0R
  troneHot = toneHotR
  trscatter = tscatterZR
  -- no meaningful optimization here so far: trscatter1 = tscatterZ1R
  trgather = tgatherZR
  trgather1 = tgatherZ1R
  tsindex = tindexZS
  tsindex0 = tindex0S
  tsoneHot = toneHotS
  tsscatter @shm @shn = tscatterZS @shm @shn
  tsgather @shm @shn = tgatherZS @shm @shn
  tsgather1 = tgatherZ1S
  txindex = tindexZX
  txindex0 = tindex0X
  txoneHot = toneHotX
  txscatter @shm @shn = tscatterZX @shm @shn
  txgather @shm @shn = tgatherZX @shm @shn
  txgather1 = tgatherZ1X
  {-# INLINE tkfloor #-}
  tkfloor = Concrete . floor . unConcrete
  {-# INLINE tkfromIntegral #-}
  tkfromIntegral = fromIntegral . unConcrete
  {-# INLINE tkcast #-}
  tkcast = Concrete . realToFrac . unConcrete
  {-# INLINE trfloor #-}
  trfloor = Concrete . liftVR (V.map floor) . unConcrete
  {-# INLINE trfromIntegral #-}
  trfromIntegral = Concrete . liftVR (V.map fromIntegral) . unConcrete
  {-# INLINE trcast #-}
  trcast = Concrete . liftVR (V.map realToFrac) . unConcrete
  {-# INLINE trminIndex #-}
  trminIndex = Concrete . tminIndexR . unConcrete
  {-# INLINE trmaxIndex #-}
  trmaxIndex = Concrete . tmaxIndexR . unConcrete
  {-# INLINE triota #-}
  triota n = trfromIntegral $ Concrete $ Nested.riota @Int n
  {-# INLINE tsfloor #-}
  tsfloor = Concrete . liftVS (V.map floor) . unConcrete
  {-# INLINE tsfromIntegral #-}
  tsfromIntegral = Concrete . liftVS (V.map fromIntegral) . unConcrete
  {-# INLINE tscast #-}
  tscast = Concrete . liftVS (V.map realToFrac) . unConcrete
  {-# INLINE tsminIndex #-}
  tsminIndex = Concrete . tminIndexS . unConcrete
  {-# INLINE tsmaxIndex #-}
  tsmaxIndex = Concrete . tmaxIndexS . unConcrete
  {-# INLINE tsiota #-}
  tsiota @n = tsfromIntegral $ Concrete $ Nested.siota @Int (SNat @n)
  {-# INLINE txfloor #-}
  txfloor = Concrete . liftVX (V.map floor) . unConcrete
  {-# INLINE txfromIntegral #-}
  txfromIntegral = Concrete . liftVX (V.map fromIntegral) . unConcrete
  {-# INLINE txcast #-}
  txcast = Concrete . liftVX (V.map realToFrac) . unConcrete
  {-# INLINE txminIndex #-}
  txminIndex = Concrete . tminIndexX . unConcrete
  {-# INLINE txmaxIndex #-}
  txmaxIndex = Concrete . tmaxIndexX . unConcrete
  {-# INLINE txiota #-}
  txiota @n = txfromIntegral $ Concrete $ Nested.miota @Int (SNat @n)
  {-# INLINE trappend #-}
  trappend @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.rappend (unConcrete u) (unConcrete v)
  {-# INLINE trslice #-}
  trslice @_ @x i n | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rslice i n . unConcrete
  {-# INLINE trreverse #-}
  trreverse @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rrev1 . unConcrete
  {-# INLINE trtranspose #-}
  trtranspose @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rtranspose perm . unConcrete
  {-# INLINE trreshape #-}
  trreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rreshape sh . unConcrete
  {-# INLINE tsappend #-}
  tsappend @_ @_ @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.sappend (unConcrete u) (unConcrete v)
  {-# INLINE tsslice #-}
  tsslice @_ @_ @_ @_ @x i n _ | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sslice i n . unConcrete
  {-# INLINE tsreverse #-}
  tsreverse @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.srev1 . unConcrete
  {-# INLINE tstranspose #-}
  tstranspose @_ @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.stranspose perm . unConcrete
  {-# INLINE tsreshape #-}
  tsreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreshape sh . unConcrete
  {-# INLINE txappend #-}
  txappend @_ @_ @_ @x u v | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ Nested.mappend (unConcrete u) (unConcrete v)
  {-# INLINE txslice #-}
  txslice @_ @_ @_ @_ @x i n _ | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.msliceSN i n . unConcrete
  {-# INLINE txreverse #-}
  txreverse @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mrev1 . unConcrete
  {-# INLINE txtranspose #-}
  txtranspose @_ @_ @x perm | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mtranspose perm . unConcrete
  {-# INLINE txreshape #-}
  txreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mreshape sh . unConcrete
  {-# INLINE tkbuild1 #-}
  tkbuild1 @k f =
    let g i = unConcrete $ f (Concrete i)
    in Concrete $ Nested.sfromVector (SNat :$$ ZSS)
       $ VS.generate (valueOf @k) g
  {-# INLINE tkbuild #-}
  tkbuild @sh f =
    let g ix = unConcrete $ f (fmapConcrete ix)
        shTake = knownShS @sh
    in Concrete $ Nested.sgeneratePrim shTake g
  {-# INLINE trbuild1 #-}
  trbuild1 @n @x k f =
    let g :: Int -> RepConcrete (TKR2 n x)
        g i = unConcrete $ f (Concrete i)
    in case knownSTK @x of
      STKScalar | SNat' @0 <- SNat @n ->
        Concrete $ Nested.rfromVector (k :$: ZSR)
        $ VS.generate k (Nested.runScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) -> case k of
        0 ->
          Concrete $ Nested.runNest $ Nested.remptyArray
        _ ->
          Concrete $ Nested.rfromListOuterN k $ NonEmpty.fromList
          $ map g [0 .. k - 1]
  {-# INLINE trbuild #-}
  trbuild @_ @n @x sh f =
    let g ix = unConcrete $ f (fmapConcrete ix)
        shTake = shrTake sh
    in case knownSTK @x of
      STKScalar | SNat' @0 <- SNat @n ->
        Concrete $ Nested.rgeneratePrim sh (Nested.runScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) ->
        Concrete $ Nested.runNest
        $ Nested.rgenerate shTake $ \ix -> g ix
  {-# INLINE trmap0N #-}
  trmap0N f t = Concrete $ tmap0NR (unConcrete . f . Concrete) (unConcrete t)
  {-# INLINE trzipWith0N #-}
  trzipWith0N f t u =
    Concrete
    $ tzipWith0NR (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                  (unConcrete t) (unConcrete u)
  {-# INLINE tsbuild1 #-}
  tsbuild1 @k @sh @x f =
    let g :: Int -> RepConcrete (TKS2 sh x)
        g i = unConcrete $ f (Concrete i)
    in case knownSTK @x of
      STKScalar | ZSS <- knownShS @sh ->
        tkbuild1 (Concrete . Nested.sunScalar . unConcrete . f)
      _ | Dict <- eltDictRep (knownSTK @x) -> case SNat @k of
        SNat' @0 ->
          Concrete $ Nested.semptyArray knownShS
        _ ->
          Concrete $ Nested.sfromListOuter SNat $ NonEmpty.fromList
          $ map g [0 .. valueOf @k - 1]
  {-# INLINE tsbuild #-}
  tsbuild @m @sh @x _ f =
    gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh) $
    let h ix = unConcrete $ f (fmapConcrete ix)
        shTake = knownShS @(Take m sh)
    in case knownSTK @x of
      STKScalar | ZSS <- knownShS @(Drop m sh)
                , Refl <- lemAppNil @(Take m sh) ->
        tkbuild (Concrete . Nested.sunScalar . unConcrete . f)
      _ | Dict <- eltDictRep (knownSTK @x) ->
        Concrete $ Nested.sunNest
        $ Nested.sgenerate shTake $ \ix -> h ix
  {-# INLINE tsmap0N #-}
  tsmap0N f v = Concrete $ tmap0NS (unConcrete . f . Concrete) (unConcrete v)
  {-# INLINE tszipWith0N #-}
  tszipWith0N f t u =
    Concrete
    $ tzipWith0NS (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                  (unConcrete t) (unConcrete u)
  {-# INLINE txbuild1 #-}
  txbuild1 @k @sh @x f =
    let g :: Int -> RepConcrete (TKX2 sh x)
        g i = unConcrete $ f (Concrete i)
    in case knownSTK @x of
      STKScalar | ZKX <- knownShX @sh ->
        Concrete $ Nested.mfromVector (Nested.SKnown SNat :$% ZSX)
        $ VS.generate (valueOf @k) (Nested.munScalar . g)
          -- this is somewhat faster and not much more complex than if
          -- done with mgeneratePrim
      _ | Dict <- eltDictRep (knownSTK @x) -> case SNat @k of
        SNat' @0 ->
          Concrete $ Nested.munNest $ Nested.memptyArray ZSX
        _ ->
          Concrete $ Nested.mfromListOuterSN SNat $ NonEmpty.fromList
          $ map g [0 .. valueOf @k - 1]
  {-# INLINE txbuild #-}
  txbuild @m @sh @x _ sh f =
    gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh) $
    let g ix = unConcrete $ f (fmapConcrete ix)
        shTake = shxTakeSSX (Proxy @(Drop m sh)) (knownShX @(Take m sh)) sh
    in case knownSTK @x of
      STKScalar | ZKX <- knownShX @(Drop m sh)
                , Refl <- lemAppNil @(Take m sh) ->
        Concrete $ Nested.mgeneratePrim sh (Nested.munScalar . g)
      _ | Dict <- eltDictRep (knownSTK @x) ->
        Concrete $ Nested.munNest
        $ Nested.mgenerate shTake $ \ix -> g ix
  {-# INLINE tmapAccumRDer #-}
  tmapAccumRDer _ k _ bftk eftk f _df _rf = oRtmapAccumR k bftk eftk f
  {-# INLINE tmapAccumLDer #-}
  tmapAccumLDer _ k _ bftk eftk f _df _rf = oRtmapAccumL k bftk eftk f
  {-# INLINE tapply #-}
  tapply f = Concrete . f . unConcrete
  {-# INLINE tlambda #-}
  tlambda _ f = unConcrete . unHFun f . Concrete
  -- The code for tvjp and tjvp in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  {-# INLINE tgrad #-}
  tgrad @_ @r xftk h | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    unConcrete . snd . crevOnParams Nothing (unHFun h) xftk . Concrete
  {-# INLINE tvjp #-}
  tvjp xftk h = \db_a ->
    unConcrete $ snd
    $ crevOnParamsDt (Concrete $ fst db_a) (unHFun h) xftk (Concrete $ snd db_a)
  {-# INLINE tjvp #-}
  tjvp xftk h = \da_a ->
    unConcrete $ snd
    $ cfwdOnParams xftk (Concrete $ snd da_a) (unHFun h) (Concrete $ fst da_a)
  tprimalPart = id
  {-# INLINE tdualPart #-}
  tdualPart stk t = DummyDualTarget (tftk stk t)
  tplainPart = id
  tfromPrimal _ t = t
  {-# INLINE tfromDual #-}
  tfromDual (DummyDualTarget ftk) = tdefTarget ftk
  tfromPlain _ t = t
  tScale _ _ t = t
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target


instance ConvertTensor Concrete where
  {-# INLINE tconvert #-}
  tconvert c astk a | Dict <- eltDictRep astk
                    , Dict <- eltDictRep (convertSTK c astk) =
    Concrete $ Nested.convert (interpretTKConversion c) (unConcrete a)

  {-# INLINE kfromR #-}
  kfromR = Concrete . Nested.runScalar . unConcrete
  {-# INLINE kfromS #-}
  kfromS = Concrete . Nested.sunScalar . unConcrete
  {-# INLINE kfromX #-}
  kfromX = Concrete . Nested.munScalar . unConcrete
  {-# INLINE rfromK #-}
  rfromK = Concrete . Nested.rscalar . unConcrete
  {-# INLINE rfromS #-}
  rfromS @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.stoRanked . unConcrete
  {-# INLINE rfromX #-}
  rfromX @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mtoRanked . unConcrete
  {-# INLINE sfromK #-}
  sfromK = Concrete . Nested.sscalar . unConcrete
  {-# INLINE sfromR #-}
  sfromR @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . flip Nested.rcastToShaped knownShS . unConcrete
  {-# INLINE sfromX #-}
  sfromX @_ @_ @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mcastToShaped knownShS . unConcrete
  {-# INLINE xfromK #-}
  xfromK = Concrete . Nested.mscalar . unConcrete
  {-# INLINE xfromR #-}
  xfromR @sh @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.rcastToMixed (knownShX @sh) . unConcrete
  {-# INLINE xfromS #-}
  xfromS @_ @sh' @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.scastToMixed (knownShX @sh') . unConcrete

  {-# INLINE rzip #-}
  rzip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.rzip a b
  {-# INLINE runzip #-}
  runzip a = let (!a1, !a2) = Nested.runzip $ unConcrete a
             in Concrete (a1, a2)
  {-# INLINE szip #-}
  szip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.szip a b
  {-# INLINE sunzip #-}
  sunzip a = let (!a1, !a2) = Nested.sunzip $ unConcrete a
             in Concrete (a1, a2)
  {-# INLINE xzip #-}
  xzip @y @z (Concrete (a, b)) | Dict <- eltDictRep (knownSTK @y)
                               , Dict <- eltDictRep (knownSTK @z) =
    Concrete $ Nested.mzip a b
  {-# INLINE xunzip #-}
  xunzip a = let (!a1, !a2) = Nested.munzip $ unConcrete a
             in Concrete (a1, a2)

  {-# INLINE xnestR #-}
  xnestR @sh1 @m @x sh | Dict <- eltDictRep (knownSTK @x)
                       , Refl <- lemRankReplicate (SNat @m) =
    Concrete
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing) (RepConcrete x)))
        (Nested.ConvXX Nested.ConvXR)
    . Nested.mnest sh
    . unConcrete
  {-# INLINE xnestS #-}
  xnestS @sh1 @sh2 @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Mixed (MapJust sh2) (RepConcrete x)))
        (Nested.ConvXX Nested.ConvXS)
    . Nested.mnest sh
    . unConcrete
  {-# INLINE xnest #-}
  xnest @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.mnest sh . unConcrete
  {-# INLINE xunNestR #-}
  xunNestR @sh1 @m @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.munNest
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Ranked m (RepConcrete x)))
        (Nested.ConvXX Nested.ConvRX)
    . unConcrete
  {-# INLINE xunNestS #-}
  xunNestS @sh1 @sh2 @x | Dict <- eltDictRep (knownSTK @x) =
    Concrete
    . Nested.munNest
    . Nested.convert
        @(Nested.Mixed sh1 (Nested.Shaped sh2 (RepConcrete x)))
        (Nested.ConvXX Nested.ConvSX)
    . unConcrete
  {-# INLINE xunNest #-}
  xunNest = Concrete . Nested.munNest . unConcrete

  tpairConv = tpair
  tunpairConv = tunpair

interpretTKConversion :: TKConversion a b
                      -> Nested.Conversion (RepConcrete a) (RepConcrete b)
interpretTKConversion c0 = case c0 of
  ConvId -> Nested.ConvId
  ConvCmp c1 c2 -> Nested.ConvCmp (interpretTKConversion c1)
                                  (interpretTKConversion c2)
  ConvRX -> Nested.ConvRX
  ConvSX -> Nested.ConvSX
  ConvXR stk | Dict <- eltDictRep stk -> Nested.ConvXR
  ConvXS -> Nested.ConvXS
  ConvXS' (FTKS sh' ftk) | Dict <- eltDictRep (ftkToSTK ftk) ->
    Nested.ConvXS' sh'
  ConvXX' (FTKX shx ftk) | Dict <- eltDictRep (ftkToSTK ftk) ->
    Nested.ConvXX' (ssxFromShX shx)
  ConvRR c -> Nested.ConvRR (interpretTKConversion c)
  ConvSS c -> Nested.ConvSS (interpretTKConversion c)
  ConvXX c -> Nested.ConvXX (interpretTKConversion c)
  ConvT2 c1 c2 ->
    Nested.ConvT2 (interpretTKConversion c1) (interpretTKConversion c2)
  Conv0X stk | Dict <- eltDictRep stk -> Nested.Conv0X
  ConvX0 -> Nested.ConvX0
  ConvNest (STKX sh x) | Dict <- eltDictRep x -> Nested.ConvNest sh
  ConvUnnest -> Nested.ConvUnnest
  ConvZip stk1 stk2 | Dict <- eltDictRep stk1
                    , Dict <- eltDictRep stk2 -> Nested.ConvZip
  ConvUnzip stk1 stk2 | Dict <- eltDictRep stk1
                      , Dict <- eltDictRep stk2 -> Nested.ConvUnzip


-- * Misc

fmapConcrete :: f (RepConcrete y) -> f (Concrete y)
fmapConcrete = unsafeCoerce

fmapUnConcrete :: f (Concrete y) -> f (RepConcrete y)
fmapUnConcrete = unsafeCoerce

ixInBoundsR :: IxROf Concrete n -> IShR n -> Bool
{-# INLINE ixInBoundsR #-}
ixInBoundsR ZIR _ = True
ixInBoundsR (Concrete i :.: ixs) (dim :$: dims) =
  if 0 <= i && i < dim then ixInBoundsR ixs dims else False

ixInBoundsS :: IxSOf Concrete sh -> ShS sh -> Bool
{-# INLINE ixInBoundsS #-}
ixInBoundsS ZIS _ = True
ixInBoundsS (Concrete i :.$ ixs) (dim :$$ dims) =
  if 0 <= i && i < sNatValue dim then ixInBoundsS ixs dims else False

ixInBoundsX :: IxXOf Concrete sh -> IShX sh -> Bool
{-# INLINE ixInBoundsX #-}
ixInBoundsX ZIX _ = True
ixInBoundsX (Concrete i :.% ixs) (dim :$% dims) =
  if 0 <= i && i < fromSMayNat' dim then ixInBoundsX ixs dims else False

oRtmapAccumR
  :: forall k accy by ey.
     SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> ((RepConcrete accy, RepConcrete ey) -> RepConcrete (TKProduct accy by))
  -> Concrete accy
  -> Concrete (BuildTensorKind k ey)
  -> Concrete (TKProduct accy (BuildTensorKind k by))
{-# INLINE oRtmapAccumR #-}
oRtmapAccumR k bftk eftk f acc0 es = case sNatValue k of
  0 -> tpair acc0 (tdefTarget (buildFTK k bftk))
  _ -> let (xout, lout) =
             mapAccumR (curry $ coerce f) acc0
                       (tunravelToListShare k (ftkToSTK eftk) es)
       in tpair xout (tfromList k (ftkToSTK bftk) lout)

oRtmapAccumL
  :: forall k accy by ey.
     SNat k
  -> FullShapeTK by
  -> FullShapeTK ey
  -> ((RepConcrete accy, RepConcrete ey) -> RepConcrete (TKProduct accy by))
  -> Concrete accy
  -> Concrete (BuildTensorKind k ey)
  -> Concrete (TKProduct accy (BuildTensorKind k by))
{-# INLINE oRtmapAccumL #-}
oRtmapAccumL k bftk eftk f acc0 es = case sNatValue k of
  0 -> tpair acc0 (tdefTarget (buildFTK k bftk))
  _ -> let (xout, lout) =
             mapAccumL (curry $ coerce f) acc0
                       (tunravelToListShare k (ftkToSTK eftk) es)
       in tpair xout (tfromList k (ftkToSTK bftk) lout)


-- * Ranked internal definitions

{-
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u) -}

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t

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
{-# INLINE liftVR #-}
liftVR f = Ranked.liftRanked1 (Mixed.mliftNumElt1 (`liftVEltwise1` f))

manyHotNR :: forall m n x. (KnownNat m, KnownSTK x)
          => FullShapeTK (TKR2 (m + n) x)
          -> [(Int, Concrete (TKR2 n x))]
          -> Concrete (TKR2 (m + n) x)
{-# INLINE manyHotNR #-}
manyHotNR (FTKR shRanked x) upd | Dict <- eltDictRep (knownSTK @x)
                                , Refl <- lemRankReplicate (Proxy @(m + n))
                                , Refl <- lemReplicatePlusApp
                                            (SNat @m)
                                            (Proxy @n)
                                            (Proxy @(Nothing @Nat)) = runST $ do
  let zero = unConcrete $ tdefTarget x
      sh = shxFromShR shRanked
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, v) ->
    Mixed.mvecsWritePartialLinear
      (Proxy @(Replicate m Nothing)) ix (Nested.rtoMixed $ unConcrete v) vecs
  Concrete . Nested.mtoRanked <$> Mixed.mvecsUnsafeFreeze sh vecs

tindexNR
  :: Nested.Elt x
  => Nested.Ranked (m + n) x -> IIxR m -> Nested.Ranked n x
{-# INLINE tindexNR #-}  -- the function is just a wrapper
tindexNR v ix = Nested.rindexPartial v ix

tindexZR :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
         => Concrete (TKR2 (m + n) x) -> IxROf Concrete m -> Concrete (TKR2 n x)
{-# INLINE tindexZR #-}  -- the function is just a wrapper
tindexZR v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in if ixInBoundsR ixConcrete (shrTake @m $ Nested.rshape uv)
     then Concrete $ tindexNR uv ix
     else case tftk knownSTK v of
       FTKR sh x -> tdefTarget (FTKR (shrDrop @m sh) x)

tindex0R :: GoodScalar r
         => Concrete (TKR m r) -> IxROf Concrete m -> Concrete (TKScalar r)
{-# INLINE tindex0R #-}  -- the function is just a wrapper
tindex0R v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete
     $ if ixInBoundsR ixConcrete (Nested.rshape uv)
       then Nested.rindex uv ix
       else def

toneHotR :: forall m n x. (KnownNat n, KnownSTK x)
         => IShR m -> Concrete (TKR2 n x) -> IxROf Concrete m
         -> Concrete (TKR2 (m + n) x)
{-# INLINE toneHotR #-}
toneHotR sh1 v ix = case tftk knownSTK v of
  FTKR sh2 x ->
    let ftk = FTKR (sh1 `shrAppend` sh2) x
    in if ixInBoundsR ix sh1
       then case shrRank sh1 of
         SNat -> manyHotNR ftk [(unConcrete $ ixrToLinear sh1 ix, v)]
       else tdefTarget ftk

-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensor is added at such an index.
tscatterZR :: forall m n p x.
              (KnownNat m, KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
           => IShR (p + n) -> Concrete (TKR2 (m + n) x)
           -> (IxROf Concrete m -> IxROf Concrete p)
           -> Concrete (TKR2 (p + n) x)
{-# INLINE tscatterZR #-}   -- this function takes a function as an argument
tscatterZR sh t f | Dict <- eltDictRep (knownSTK @x) =
  let shm = shrTake @m $ rshape t
      shp = shrTake @p sh
  in case (SNat @n, tftk knownSTK t) of
       (SNat' @0, FTKR _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum
                                                      (Proxy @r) -> runST $ do
         -- Optimized: using (+) instead of taddTarget and using trindex0.
         vec <- VSM.replicate (shrSize shp) 0
         forM_ (shrEnum shm) $ \ix -> do
           let ix2 = f $ fmapConcrete ix
           when (ixInBoundsR ix2 shp) $ do
             let v = unConcrete $ trindex0 t $ fmapConcrete ix
                 i2 = unConcrete $ ixrToLinear shp ix2
             v2 <- VSM.read vec i2
             VSM.write vec i2 (v + v2)
         Concrete . Nested.rfromVector shp <$> VS.unsafeFreeze vec
       (_, FTKR _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r) ->
         -- Optimized: using (+) instead of taddTarget.
         let ftk = FTKR sh FTKScalar
             g :: IIxR m
               -> IM.IntMap (Concrete (TKR2 n x))
               -> IM.IntMap (Concrete (TKR2 n x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsR ix2 shp
                  then IM.insertWith (+)
                         (unConcrete $ ixrToLinear shp ix2)
                         (Concrete $ tindexNR (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shrEnum shm)
         in manyHotNR ftk $ IM.assocs ivs
       (_, FTKR _ x) ->
         let ftk = FTKR sh x
             g :: IIxR m
               -> IM.IntMap (Concrete (TKR2 n x))
               -> IM.IntMap (Concrete (TKR2 n x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsR ix2 shp
                  then IM.insertWith (taddTarget knownSTK)
                         (unConcrete $ ixrToLinear shp ix2)
                         (Concrete $ tindexNR (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shrEnum shm)
         in manyHotNR ftk $ IM.assocs ivs

-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is def, which is 0.
tgatherZR :: forall m n p x. (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
          => IShR (m + n) -> Concrete (TKR2 (p + n) x)
          -> (IxROf Concrete m -> IxROf Concrete p)
          -> Concrete (TKR2 (m + n) x)
{-# INLINE tgatherZR #-}   -- this function takes a function as an argument
tgatherZR sh t f = case (SNat @n, knownSTK @x) of
  (SNat' @0, STKScalar) ->  -- an optimized common case
    let g ix = unConcrete $ t `trindex0` (f $ fmapConcrete ix)
    in Concrete $ Nested.rgeneratePrim sh g
  _ -> trbuild sh (\ix -> t `trindex` f ix)

tgatherZ1R :: forall n p x. (KnownNat n, KnownNat p, KnownSTK x)
           => Int -> Concrete (TKR2 (p + n) x)
           -> (IntOf Concrete -> IxROf Concrete p)
           -> Concrete (TKR2 (1 + n) x)
{-# INLINE tgatherZ1R #-}   -- this function takes a function as an argument
tgatherZ1R k t f = case (SNat @n, knownSTK @x) of
  (SNat' @0, STKScalar) ->  -- an optimized common case
    let shm = k :$: shrDrop (rshape t)
        g i = unConcrete $ t `trindex0` (f $ Concrete i)
    in Concrete $ Nested.rfromVector shm $ VS.generate k g
  _ -> trbuild1 k (\ix -> t `trindex` f ix)

tminIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
{-# INLINE tminIndexR #-}
tminIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . ixrHead . Nested.rminIndexPrim
  in Nested.runNest $ Nested.rrerankPrim ZSR f (Nested.rnest SNat v)

tmaxIndexR
  :: forall r r2 n.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
{-# INLINE tmaxIndexR #-}
tmaxIndexR v | SNat <- Nested.rrank v =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . ixrHead . Nested.rmaxIndexPrim
  in Nested.runNest $ Nested.rrerankPrim ZSR f (Nested.rnest SNat v)

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (r1 -> r) -> Nested.Ranked n r1 -> Nested.Ranked n r
{-# INLINE tmap0NR #-}
tmap0NR f = Ranked.liftRanked1 (Mixed.mliftPrim f)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (r1 -> r2 -> r) -> Nested.Ranked n r1 -> Nested.Ranked n r2
  -> Nested.Ranked n r
{-# INLINE tzipWith0NR #-}
tzipWith0NR f = Ranked.liftRanked2 (Mixed.mliftPrim2 f)


-- * Shaped internal definitions

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
{-# INLINE liftVS #-}
liftVS f = Shaped.liftShaped1 (Mixed.mliftNumElt1 (`liftVEltwise1` f))

manyHotNS :: forall sh1 sh2 x. (KnownShS sh1, KnownShS sh2, KnownSTK x)
          => FullShapeTK x
          -> [(Int, Concrete (TKS2 sh2 x))]
          -> Concrete (TKS2 (sh1 ++ sh2) x)
{-# INLINE manyHotNS #-}
manyHotNS x upd | Dict <- eltDictRep (knownSTK @x)
                , let shShaped = knownShS @sh1 `shsAppend` knownShS @sh2
                , Refl <- lemRankMapJust shShaped
                , Refl <- lemMapJustApp (knownShS @sh1)
                                        (Proxy @sh2) = runST $ do
  let zero = unConcrete $ tdefTarget x
      sh = shxFromShS shShaped
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, v) ->
    Mixed.mvecsWritePartialLinear
      (Proxy @(MapJust sh1)) ix (Nested.stoMixed $ unConcrete v) vecs
  Concrete . Nested.mcastToShaped shShaped <$> Mixed.mvecsUnsafeFreeze sh vecs

tindexNS
  :: Nested.Elt x
  => Nested.Shaped (sh1 ++ sh2) x -> IxS sh1 Int -> Nested.Shaped sh2 x
{-# INLINE tindexNS #-}  -- the function is just a wrapper
tindexNS v ix = Nested.sindexPartial v ix

-- Note that after vectorization, the index may not fit within
-- the type-level shape, which we catch in the @ixInBounds@
-- and return def, so it's fine. Similarly in gather and scatter.
tindexZS :: forall shm shn x. (KnownShS shm, KnownShS shn, KnownSTK x)
         => Concrete (TKS2 (shm ++ shn) x) -> IxSOf Concrete shm
         -> Concrete (TKS2 shn x)
{-# INLINE tindexZS #-}  -- the function is just a wrapper
tindexZS v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in if ixInBoundsS ixConcrete (knownShS @shm)
         then Concrete $ tindexNS uv ix
         else case tftk (STKS (knownShS @shm `shsAppend` knownShS @shn)
                              (knownSTK @x)) v of
           FTKS _sh x -> tdefTarget (FTKS knownShS x)

tindex0S :: GoodScalar r
         => Concrete (TKS sh1 r) -> IxSOf Concrete sh1 -> Concrete (TKScalar r)
{-# INLINE tindex0S #-}  -- the function is just a wrapper
tindex0S v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete
     $ if ixInBoundsS ixConcrete (Nested.sshape uv)
       then Nested.sindex uv ix
       else def

toneHotS :: forall sh1 sh2 x. (KnownShS sh1, KnownShS sh2, KnownSTK x)
         => Concrete (TKS2 sh2 x) -> IxSOf Concrete sh1
         -> Concrete (TKS2 (sh1 ++ sh2) x)
{-# INLINE toneHotS #-}
toneHotS v ix = case tftk knownSTK v of
  FTKS sh2 x ->
    let ftk = FTKS (knownShS @sh1 `shsAppend` sh2) x
    in if ixInBoundsS ix (knownShS @sh1)
       then manyHotNS @sh1 x [(unConcrete $ ixsToLinear (knownShS @sh1) ix, v)]
       else tdefTarget ftk

-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensor is added at such an index.
tscatterZS :: (KnownShS shm, KnownShS shn, KnownShS shp, TKAllNum x, KnownSTK x)
           => Concrete (TKS2 (shm ++ shn) x)
           -> (IxSOf Concrete shm -> IxSOf Concrete shp)
           -> Concrete (TKS2 (shp ++ shn) x)
{-# INLINE tscatterZS #-}  -- this function takes a function as an argument
tscatterZS @shm @shn @shp @x t f =
  let shm = knownShS @shm
      shp = knownShS @shp
  in withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
     case (knownShS @shn, tftk knownSTK t) of
       (ZSS, FTKS _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r)
                                    , Refl <- lemAppNil @shp
                                    , Refl <- lemAppNil @shm -> runST $ do
         -- Optimized: using (+) instead of taddTarget and using txindex0.
         vec <- VSM.replicate (shsSize shp) 0
         forM_ (shsEnum shm) $ \ix -> do
           let ix2 = f $ fmapConcrete ix
           when (ixInBoundsS ix2 shp) $ do
             let v = unConcrete $ tsindex0 t $ fmapConcrete ix
                 i2 = unConcrete $ ixsToLinear shp ix2
             v2 <- VSM.read vec i2
             VSM.write vec i2 (v + v2)
         Concrete . Nested.sfromVector shp <$> VS.unsafeFreeze vec
       (_, FTKS _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r) ->
         -- Optimized: using (+) instead of taddTarget.
         let g :: IxS shm Int
               -> IM.IntMap (Concrete (TKS2 shn x))
               -> IM.IntMap (Concrete (TKS2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsS ix2 shp
                  then IM.insertWith (+)
                         (unConcrete $ ixsToLinear shp ix2)
                         (Concrete $ tindexNS @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shsEnum shm)
         in manyHotNS @shp FTKScalar $ IM.assocs ivs
       (_, FTKS _ x) | Dict <- eltDictRep (ftkToSTK x) ->
         let g :: IxS shm Int
               -> IM.IntMap (Concrete (TKS2 shn x))
               -> IM.IntMap (Concrete (TKS2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsS ix2 shp
                  then IM.insertWith (taddTarget knownSTK)
                         (unConcrete $ ixsToLinear shp ix2)
                         (Concrete $ tindexNS @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shsEnum shm)
         in manyHotNS @shp x $ IM.assocs ivs

tgatherZS :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x)
          => Concrete (TKS2 (shp ++ shn) x)
          -> (IxSOf Concrete shm -> IxSOf Concrete shp)
          -> Concrete (TKS2 (shm ++ shn) x)
{-# INLINE tgatherZS #-}  -- this function takes a function as an argument
tgatherZS @shm @shn @shp @x t f =
  gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
  case (knownShS @shn, knownSTK @x) of
    (ZSS, STKScalar) | Refl <- lemAppNil @shm
                     , Refl <- lemAppNil @shp ->  -- an optimized common case
      let g ix = t `tsindex0` f ix
      in tkbuild g
    _ ->
      withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
      case shsRank (knownShS @shm) of
        SNat -> -- needed only for GHC 9.10
          tsbuild @_ @(Rank shm) SNat (\ix -> t `tsindex` f ix)

tgatherZ1S
  :: (KnownNat k, KnownShS shn, KnownShS shp, KnownSTK x)
  => Concrete (TKS2 (shp ++ shn) x)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS2 (k ': shn) x)
{-# INLINE tgatherZ1S #-}   -- this function takes a function as an argument
tgatherZ1S @_ @shn @shp @x t f = case (knownShS @shn, knownSTK @x) of
  (ZSS, STKScalar) | Refl <- lemAppNil @shp ->  -- an optimized common case
    tkbuild1 (\ix -> t `tsindex0` f ix)
  _ ->
    tsbuild1 (\ix -> t `tsindex` f ix)

tminIndexS
  :: forall n sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
{-# INLINE tminIndexS #-}
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
      Nested.sunNest $
        Nested.srerankPrim @'[m] @'[] @(Init (n ': sh)) ZSS (f @m) $
          Nested.snest (shsInit sh1) v

tmaxIndexS
  :: forall n sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
{-# INLINE tmaxIndexS #-}
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
      Nested.sunNest $
        Nested.srerankPrim @'[m] @'[] @(Init (n ': sh)) ZSS (f @m) $
          Nested.snest (shsInit sh1) v

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (r1 -> r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
{-# INLINE tmap0NS #-}
tmap0NS f = Shaped.liftShaped1 (Mixed.mliftPrim f)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (r1 -> r2 -> r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r2
  -> Nested.Shaped sh r
{-# INLINE tzipWith0NS #-}
tzipWith0NS f = Shaped.liftShaped2 (Mixed.mliftPrim2 f)


-- * Mixed internal definitions

liftVX
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Mixed sh r1 -> Nested.Mixed sh r
{-# INLINE liftVX #-}
liftVX f = Mixed.mliftNumElt1 (`liftVEltwise1` f)

manyHotNX :: forall sh1 sh2 x. KnownSTK x
          => FullShapeTK (TKX2 (sh1 ++ sh2) x)
          -> [(Int, Concrete (TKX2 sh2 x))]
          -> Concrete (TKX2 (sh1 ++ sh2) x)
{-# INLINE manyHotNX #-}
manyHotNX (FTKX sh x) upd | Dict <- eltDictRep (knownSTK @x) = runST $ do
  let zero = unConcrete $ tdefTarget x
  vecs <- Mixed.mvecsReplicate sh zero
    -- this avoids the slow case of mvecsReplicate if x is TKScalar
  forM_ upd $ \(ix, v) ->
    Mixed.mvecsWritePartialLinear (Proxy @sh1) ix (unConcrete v) vecs
  Concrete <$> Mixed.mvecsUnsafeFreeze sh vecs

tindexNX
  :: Nested.Elt x
  => Nested.Mixed (sh1 ++ sh2) x -> IIxX sh1 -> Nested.Mixed sh2 x
{-# INLINE tindexNX #-}  -- the function is just a wrapper
tindexNX v ix = Nested.mindexPartial v ix

tindexZX :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
         => Concrete (TKX2 (sh1 ++ sh2) x) -> IxXOf Concrete sh1
         -> Concrete (TKX2 sh2 x)
{-# INLINE tindexZX #-}  -- the function is just a wrapper
tindexZX @sh1 @sh2 @x v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in if ixInBoundsX ixConcrete (shxTakeSSX (Proxy @sh2) (knownShX @sh1) (Nested.mshape uv))
     then Concrete $ tindexNX uv ix
     else case tftk (STKX (knownShX @sh1 `ssxAppend` knownShX @sh2)
                          (knownSTK @x)) v of
       FTKX sh x -> tdefTarget (FTKX (shxDropSSX (knownShX @sh1) sh) x)

tindex0X :: GoodScalar r
         => Concrete (TKX sh1 r) -> IxXOf Concrete sh1 -> Concrete (TKScalar r)
{-# INLINE tindex0X #-}  -- the function is just a wrapper
tindex0X v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete
     $ if ixInBoundsX ixConcrete (Nested.mshape uv)
       then Nested.mindex uv ix
       else def

toneHotX :: forall sh1 sh2 x. (KnownShX sh2, KnownSTK x)
         => IShX sh1 -> Concrete (TKX2 sh2 x) -> IxXOf Concrete sh1
         -> Concrete (TKX2 (sh1 ++ sh2) x)
{-# INLINE toneHotX #-}
toneHotX sh1 v ix = case tftk knownSTK v of
  FTKX sh2 x ->
    let ftk = FTKX (sh1 `shxAppend` sh2) x
    in if ixInBoundsX ix sh1
       then manyHotNX @sh1 ftk [(unConcrete $ ixxToLinear sh1 ix, v)]
       else tdefTarget ftk

tscatterZX :: (KnownShX shm, KnownShX shn, KnownShX shp, TKAllNum x, KnownSTK x)
           => IShX (shp ++ shn) -> Concrete (TKX2 (shm ++ shn) x)
           -> (IxXOf Concrete shm -> IxXOf Concrete shp)
           -> Concrete (TKX2 (shp ++ shn) x)
{-# INLINE tscatterZX #-}  -- this function takes a function as an argument
tscatterZX @shm @shn @shp @x sh t f =
  let shm = shxTakeSSX (Proxy @shn) (knownShX @shm) (xshape t)
      shp = shxTakeSSX (Proxy @shn) (knownShX @shp) sh
  in withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
     case (knownShX @shn, tftk knownSTK t) of
       (ZKX, FTKX _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r)
                                    , Refl <- lemAppNil @shp
                                    , Refl <- lemAppNil @shm -> runST $ do
         -- Optimized: using (+) instead of taddTarget and using tsindex0.
         vec <- VSM.replicate (shxSize shp) 0
         forM_ (shxEnum shm) $ \ix -> do
           let ix2 = f $ fmapConcrete ix
           when (ixInBoundsX ix2 shp) $ do
             let v = unConcrete $ txindex0 t $ fmapConcrete ix
                 i2 = unConcrete $ ixxToLinear shp ix2
             v2 <- VSM.read vec i2
             VSM.write vec i2 (v + v2)
         Concrete . Nested.mfromVector shp <$> VS.unsafeFreeze vec
       (_, FTKX _ (FTKScalar @r)) | Dict0 <- numFromTKAllNum (Proxy @r) ->
         -- Optimized: using (+) instead of taddTarget.
         -- TODO: write to vecs and use a bitmap to record the written indexes
         -- and the intmap only for subsequent writes
         let ftk = FTKX sh FTKScalar
             g :: IIxX shm
               -> IM.IntMap (Concrete (TKX2 shn x))
               -> IM.IntMap (Concrete (TKX2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsX ix2 shp
                  then IM.insertWith (+)
                         (unConcrete $ ixxToLinear shp ix2)
                         (Concrete $ tindexNX @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shxEnum shm)
         in manyHotNX @shp ftk $ IM.assocs ivs
       (_, FTKX _ x) | Dict <- eltDictRep (ftkToSTK x) ->
         -- TODO: write to vecs and use a bitmap to record the written indexes
         -- and the intmap only for subsequent writes
         let ftk = FTKX sh x
             g :: IIxX shm
               -> IM.IntMap (Concrete (TKX2 shn x))
               -> IM.IntMap (Concrete (TKX2 shn x))
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBoundsX ix2 shp
                  then IM.insertWith (taddTarget knownSTK)
                         (unConcrete $ ixxToLinear shp ix2)
                         (Concrete $ tindexNX @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g IM.empty (shxEnum shm)
         in manyHotNX @shp ftk $ IM.assocs ivs

tgatherZX :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
          => IShX (shm ++ shn)
          -> Concrete (TKX2 (shp ++ shn) x)
          -> (IxXOf Concrete shm -> IxXOf Concrete shp)
          -> Concrete (TKX2 (shm ++ shn) x)
{-# INLINE tgatherZX #-}  -- this function takes a function as an argument
tgatherZX @shm @shn @shp @x sh t f =
  gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
  case (knownShX @shn, knownSTK @x) of
    (ZKX, STKScalar) | Refl <- lemAppNil @shm
                     , Refl <- lemAppNil @shp ->  -- an optimized common case
      let g ix = unConcrete $ t `txindex0` (f $ fmapConcrete ix)
      in Concrete $ Nested.mgeneratePrim sh g
    _ ->
      withKnownShX (ssxFromShX sh) $
      case ssxRank (knownShX @shm) of
        SNat -> -- needed only for GHC 9.10
          txbuild @_ @(Rank shm) SNat sh (\ix -> t `txindex` f ix)

tgatherZ1X :: forall k shn shp x.
              (KnownNat k, KnownShX shn, KnownShX shp, KnownSTK x)
           => SNat k -> Concrete (TKX2 (shp ++ shn) x)
           -> (IntOf Concrete -> IxXOf Concrete shp)
           -> Concrete (TKX2 (Just k ': shn) x)
{-# INLINE tgatherZ1X #-}   -- this function takes a function as an argument
tgatherZ1X _ t f = case (knownShX @shn, knownSTK @x) of
  (ZKX, STKScalar) | Refl <- lemAppNil @shp ->  -- an optimized common case
    let shm = SKnown SNat :$% shxDropSSX (knownShX @shp) (xshape t)
        g i = unConcrete $ t `txindex0` (f $ Concrete i)
    in Concrete $ Nested.mfromVector shm $ VS.generate (valueOf @k) g
  _ -> txbuild1 @_ @k (\ix -> t `txindex` f ix)

tminIndexX
  :: forall mn sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
{-# INLINE tminIndexX #-}
tminIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead . Nested.mminIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.munNest $
        Nested.mrerankPrim @'[Just m] @'[] @(Init (mn ': sh))
                           ZSX (f @(Just m)) $
          Nested.mnest (ssxFromShX $ shxInit sh1) v

tmaxIndexX
  :: forall mn sh r r2.
     (Nested.PrimElt r, Nested.NumElt r, Nested.PrimElt r2, Num r2)
  => Nested.Mixed (mn ': sh) r -> Nested.Mixed (Init (mn ': sh)) r2
{-# INLINE tmaxIndexX #-}
tmaxIndexX v | sh1@(_ :$% sh) <- Nested.mshape v =
  let f :: Nested.Mixed '[mm] r -> Nested.Mixed '[] r2
      f = Nested.mscalar . fromIntegral . ixxHead . Nested.mmaxIndexPrim
  in case sh of
    ZSX -> f @mn v
    _ -> withSNat (fromSMayNat' (shxLast sh1)) $ \(_ :: SNat m) ->
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) ++ '[Just m] :~: mn ': sh) $
      gcastWith (unsafeCoerceRefl
                 :: Init (mn ': sh) :~: Init (mn ': sh) ++ '[]) $
      Nested.munNest $
        Nested.mrerankPrim @'[Just m] @'[] @(Init (mn ': sh))
                           ZSX (f @(Just m)) $
          Nested.mnest (ssxFromShX $ shxInit sh1) v
