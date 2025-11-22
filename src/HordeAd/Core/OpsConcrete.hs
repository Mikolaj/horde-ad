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

import Control.Arrow (second)
import Data.Array.Internal.ShapedS qualified as SS
import Data.Coerce (Coercible, coerce)
import Data.Default
import Data.Function ((&))
import Data.Functor.WithIndex (imap)
import Data.Int (Int64)
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, type (+))

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
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
import HordeAd.Core.Unwind
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
  rshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.rshape . unConcrete
  {-# INLINE sshape #-}
  sshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.sshape . unConcrete
  {-# INLINE xshape #-}
  xshape @_ @r | Dict <- eltDictRep (knownSTK @r) = Nested.mshape . unConcrete
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
    map Concrete . SS.toList . Nested.stoOrthotope . unConcrete
  {-# INLINE trfromVector #-}
  trfromVector @_ @r v | Dict <- eltDictRep (knownSTK @r) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.rfromListOuterN (V.length v) l
      Nothing -> error "rfromVector: empty vector"
  {-# INLINE trunravelToList #-}
  trunravelToList @_ @r | Dict <- eltDictRep (knownSTK @r) =
    fmapConcrete . Nested.rtoListOuter . unConcrete
  {-# INLINE tsfromVector #-}
  tsfromVector @_ @_ @r v | Dict <- eltDictRep (knownSTK @r) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.sfromListOuter SNat l
      Nothing -> error "sfromVector: empty vector"
  {-# INLINE tsunravelToList #-}
  tsunravelToList @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    fmapConcrete . Nested.stoListOuter . unConcrete
  {-# INLINE txfromVector #-}
  txfromVector @n @_ @r v | Dict <- eltDictRep (knownSTK @r) =
    case NonEmpty.nonEmpty $ V.toList $ fmapUnConcrete v of
      Just l -> Concrete $ Nested.mfromListOuterSN (SNat @n) l
      Nothing -> error "xfromVector: empty vector"
  {-# INLINE txunravelToList #-}
  txunravelToList @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
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
    STKScalar -> Concrete $ Nested.sfromList1Prim snat
                 $ fmapUnConcrete l
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
  trsum0 @_ @r t = case knownSTK @r of
    STKScalar @r2 | Dict0 <- numFromTKAllNum (Proxy @r2) ->  -- optimized
      Concrete . Nested.rscalar . Nested.rsumAllPrim . unConcrete $ t
    _ -> trsum . rflatten $ t
  {-# INLINE trdot0 #-}
  trdot0 u v =
    Concrete $ Nested.rscalar $ Nested.rdot (unConcrete u) (unConcrete v)
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
  trreplicate @_ @r k | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rreplicate (k :$: ZSR) . unConcrete
  {-# INLINE trreplicate0N #-}
  trreplicate0N @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
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
  tssum0 @sh @r t | SNat <- shsProduct (knownShS @sh) = case knownSTK @r of
    STKScalar @r2 | Dict0 <- numFromTKAllNum (Proxy @r2) ->  -- optimized
      Concrete . Nested.sscalar . Nested.ssumAllPrim . unConcrete $ t
    _ -> tssum . sflatten $ t
  {-# INLINE tsdot0 #-}
  tsdot0 u v  =
    Concrete $ Nested.sscalar $ Nested.sdot (unConcrete u) (unConcrete v)
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
  tsreplicate0N @sh @r sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @r) =
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
  txsum0 @_ @r t =
    case knownSTK @r of
      STKScalar @r2 | Dict0 <- numFromTKAllNum (Proxy @r2) ->  -- optimized
        Concrete . Nested.mscalar . Nested.msumAllPrim . unConcrete $ t
      _ -> withSNat (shxSize $ xshape t) $ \snat ->
        txsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  {-# INLINE txdot0 #-}
  txdot0 u v =
    Concrete $ Nested.mscalar $ Nested.mdot (unConcrete u) (unConcrete v)
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
  txreplicate @_ @_ @r snat _sh | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mreplicate (Nested.SKnown snat :$% ZSX) . unConcrete
  {-# INLINE txreplicate0N #-}
  txreplicate0N @sh @r sh | Refl <- lemAppNil @sh
                          , Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mreplicate sh . unConcrete
  trindex = tindexZR
  trindex0 = tindex0R
  trscatter = tscatterZR
  trscatter1 = tscatterZ1R
  trgather = tgatherZR
  trgather1 = tgatherZ1R
  tsindex = tindexZS
  tsindex0 = tindex0S
  tsscatter @shm @shn = tscatterZS @shm @shn
  tsscatter1 = tscatterZ1S
  tsgather @shm @shn = tgatherZS @shm @shn
  tsgather1 = tgatherZ1S
  txindex = tindexZX
  txindex0 = tindex0X
  txscatter @shm @shn = tscatterZX @shm @shn
  txscatter1 = tscatterZ1X
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
  trappend @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ Nested.rappend (unConcrete u) (unConcrete v)
  {-# INLINE trslice #-}
  trslice @_ @r i n | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rslice i n . unConcrete
  {-# INLINE trreverse #-}
  trreverse @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rrev1 . unConcrete
  {-# INLINE trtranspose #-}
  trtranspose @_ @r perm | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rtranspose perm . unConcrete
  {-# INLINE trreshape #-}
  trreshape @_ @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rreshape sh . unConcrete
  {-# INLINE tsappend #-}
  tsappend @_ @_ @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ Nested.sappend (unConcrete u) (unConcrete v)
  {-# INLINE tsslice #-}
  tsslice @_ @_ @_ @_ @r i n _ | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.sslice i n . unConcrete
  {-# INLINE tsreverse #-}
  tsreverse @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.srev1 . unConcrete
  {-# INLINE tstranspose #-}
  tstranspose @_ @_ @r perm | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.stranspose perm . unConcrete
  {-# INLINE tsreshape #-}
  tsreshape @_ @_ @x sh | Dict <- eltDictRep (knownSTK @x) =
    Concrete . Nested.sreshape sh . unConcrete
  {-# INLINE txappend #-}
  txappend @_ @_ @_ @r u v | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ Nested.mappend (unConcrete u) (unConcrete v)
  {-# INLINE txslice #-}
  txslice @_ @_ @_ @_ @r i n _ | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.msliceSN i n . unConcrete
  {-# INLINE txreverse #-}
  txreverse @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mrev1 . unConcrete
  {-# INLINE txtranspose #-}
  txtranspose @_ @_ @r perm | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mtranspose perm . unConcrete
  {-# INLINE txreshape #-}
  txreshape @_ @_ @r sh | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mreshape sh . unConcrete
  {-# INLINE trbuild1 #-}
  trbuild1 @_ @r k f | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ tbuild1R k (unConcrete . f . Concrete)
  {-# INLINE trbuild #-}
  trbuild @_ @_ @r k f | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ tbuildR k (unConcrete . f . fmapConcrete)
  {-# INLINE trmap0N #-}
  trmap0N @_ @r @r1 f t = case (knownSTK @r1, knownSTK @r) of
    (STKScalar, STKScalar) ->
      Concrete $ tmap0NR (unConcrete . f . Concrete) (unConcrete t)
    _ ->  -- this is the default implementation from the class
      trbuild (rshape t) (f . trindex t)
  {-# INLINE trzipWith0N #-}
  trzipWith0N @_ @r1 @r2 @r f t u =
    case (knownSTK @r1, knownSTK @r2, knownSTK @r) of
      (STKScalar, STKScalar, STKScalar) ->
        Concrete
        $ tzipWith0NR (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                      (unConcrete t) (unConcrete u)
      _ ->  -- this is the default implementation from the class
        trbuild (rshape u) (\ix -> f (trindex t ix) (trindex u ix))
  {-# INLINE tsbuild1 #-}
  tsbuild1 @_ @_ @r f | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ tbuild1S (unConcrete . f . Concrete)
  {-# INLINE tsbuild #-}
  tsbuild @m @sh @x _ f | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ tbuildS @m @sh (unConcrete . f . fmapConcrete)
  {-# INLINE tsmap0N #-}
  tsmap0N @sh @r @r1 f v = case (knownSTK @r1, knownSTK @r) of
    (STKScalar, STKScalar) ->
      Concrete $ tmap0NS (unConcrete . f . Concrete) (unConcrete v)
    _ | Refl <- lemAppNil @sh ->
      -- this is the default implementation from the class
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
      gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
      case shsRank (knownShS @sh) of  -- needed only for GHC 9.10
        SNat ->
          tsbuild @_ @(Rank sh) SNat (f . tsindex v)
  {-# INLINE tszipWith0N #-}
  tszipWith0N @sh @r1 @r2 @r f t u =
    case (knownSTK @r1, knownSTK @r2, knownSTK @r) of
      (STKScalar, STKScalar, STKScalar) ->
        Concrete
        $ tzipWith0NS (\v w -> unConcrete $ f (Concrete v) (Concrete w))
                      (unConcrete t) (unConcrete u)
      _ | Refl <- lemAppNil @sh ->
        -- this is the default implementation from the class
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[]) $
        gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh) $
        case shsRank (knownShS @sh) of  -- needed only for GHC 9.10
          SNat ->
            tsbuild @_ @(Rank sh) SNat (\ix -> f (tsindex t ix) (tsindex u ix))
  {-# INLINE txbuild1 #-}
  txbuild1 @_ @_ @r f | Dict <- eltDictRep (knownSTK @r) =
    Concrete $ tbuild1X (unConcrete . f . Concrete)
  {-# INLINE txbuild #-}
  txbuild @m @sh @x _ sh f | Dict <- eltDictRep (knownSTK @x) =
    Concrete $ tbuildX @m @sh sh (unConcrete . f . fmapConcrete)
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
  treplTarget = replTarget
  tdefTarget = defTarget
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
  rfromS @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.stoRanked . unConcrete
  {-# INLINE rfromX #-}
  rfromX @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mtoRanked . unConcrete
  {-# INLINE sfromK #-}
  sfromK = Concrete . Nested.sscalar . unConcrete
  {-# INLINE sfromR #-}
  sfromR @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . flip Nested.rcastToShaped knownShS . unConcrete
  {-# INLINE sfromX #-}
  sfromX @_ @_ @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.mcastToShaped knownShS . unConcrete
  {-# INLINE xfromK #-}
  xfromK = Concrete . Nested.mscalar . unConcrete
  {-# INLINE xfromR #-}
  xfromR @sh @r | Dict <- eltDictRep (knownSTK @r) =
    Concrete . Nested.rcastToMixed (knownShX @sh) . unConcrete
  {-# INLINE xfromS #-}
  xfromS @_ @sh' @r | Dict <- eltDictRep (knownSTK @r) =
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

fmapConcrete :: Coercible (f (RepConcrete y)) (f (Concrete y))
               => f (RepConcrete y) -> f (Concrete y)
fmapConcrete = coerce

fmapUnConcrete :: Coercible (f (Concrete y)) (f (RepConcrete y))
               => f (Concrete y) -> f (RepConcrete y)
fmapUnConcrete = coerce

ixInBounds :: [Int64] -> [Int] -> Bool
{-# INLINE ixInBounds #-}
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

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

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m x. (KnownNat n, KnownNat m, KnownSTK x)
         => Concrete (TKR2 (n + m) x)
         -> [(IxROf Concrete n, Concrete (TKR2 m x))]
         -> Concrete (TKR2 (n + m) x)
{-# INLINE updateNR #-}
updateNR arr upd = case knownSTK @x of
  STKScalar ->  -- optimized
    let values = rtoVector arr
        sh = rshape arr
        f !t (ix, u) =
          let v = rtoVector u
              i = fromIntegral $ unConcrete $ toLinearIdxR @n @m sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in Concrete $ Nested.rfromVector sh (foldl' f values upd)
  _ ->
    let arrNested = rnest (SNat @n) arr
        shNested = rshape arrNested
        f i v = case lookup (fromLinearIdxR @n shNested (fromIntegral i)) upd of
          Just u -> rnest (SNat @0) u
          Nothing -> v
    in runNest $ tfromListLinearR shNested
       $ imap f $ trunravelToList $ rflatten arrNested

tfromListLinearR
  :: forall n x. KnownSTK x
  => IShR n -> [Concrete (TKR2 0 x)] -> Concrete (TKR2 n x)
{-# INLINE tfromListLinearR #-}
tfromListLinearR sh l | Dict <- eltDictRep (knownSTK @x) = Concrete $
  case NonEmpty.nonEmpty $ fmapUnConcrete l of
    Nothing -> Nested.rreshape sh Nested.remptyArray
    Just nl -> Nested.rfromListLinear sh $ NonEmpty.map Nested.runScalar nl

tindexNR
  :: Nested.Elt x
  => Nested.Ranked (m + n) x -> IxR m Int64 -> Nested.Ranked n x
{-# INLINE tindexNR #-}  -- the function is just a wrapper
tindexNR v ix = Nested.rindexPartial v (fmap fromIntegral ix)
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

tindexZR :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
         => Concrete (TKR2 (m + n) x) -> IxROf Concrete m -> Concrete (TKR2 n x)
{-# INLINE tindexZR #-}  -- the function is just a wrapper
tindexZR v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in if ixInBounds (toList ix) (toList $ Nested.rshape uv)
     then Concrete $ tindexNR uv ix
     else case tftk knownSTK v of
       FTKR sh x -> tdefTarget (FTKR (shrDrop @m sh) x)

tindex0R :: (KnownNat m, GoodScalar r)
         => Concrete (TKR m r) -> IxROf Concrete m -> Concrete (TKScalar r)
{-# INLINE tindex0R #-}  -- the function is just a wrapper
tindex0R v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete $ if ixInBounds (toList ix) (toList $ Nested.rshape uv)
                then Nested.rindex uv (fmap fromIntegral ix)
                else def
{- TODO: see above
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
-}

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probably optimal in this respect
-- (the only new vectors are created by V.concat, but this is done on demand).
-- TODO: optimize updateNR and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZR :: forall m n p x.
              (KnownNat m, KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
           => IShR (p + n) -> Concrete (TKR2 (m + n) x)
           -> (IxROf Concrete m -> IxROf Concrete p)
           -> Concrete (TKR2 (p + n) x)
{-# INLINE tscatterZR #-}   -- this function takes a function as an argument
tscatterZR sh t f
 | Dict <- eltDictRep (knownSTK @x) = case tftk knownSTK t of
  FTKR _ x@(FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
    -- Optimized.
    let zero = tdefTarget (FTKR sh x)
        (shm, shDropP) = shrSplitAt @m $ rshape t
        s = shrSize shm
        g :: IxR m Int64
          -> M.Map (IxROf Concrete p) (VS.Vector r)
          -> M.Map (IxROf Concrete p) (VS.Vector r)
        g ix =
          let ix2 = f $ fmapConcrete ix
          in if ixInBounds (fmapUnConcrete $ toList ix2) (toList sh)
             then M.insertWith (V.zipWith (+)) ix2
                               (Nested.rtoVector $ unConcrete t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdxR shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ map (second $ Concrete . Nested.rfromVector shDropP)
       $ M.assocs ivs
  FTKR _ x ->
    let zero = tdefTarget (FTKR sh x)
        (shm, _) = shrSplitAt @m $ rshape t
        s = shrSize shm
        g ix =
          let ix2 = f $ fmapConcrete ix
          in if ixInBounds (fmapUnConcrete $ toList ix2) (toList sh)
             then M.insertWith (taddTarget knownSTK) ix2
                               (Concrete $ unConcrete t `tindexNR` ix)
             else id
        ivs = foldr g M.empty [ fromLinearIdxR shm i
                              | i <- [0 .. fromIntegral s - 1] ]
    in updateNR zero
       $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling Nested.rfromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (KnownNat n, KnownNat p, TKAllNum x, KnownSTK x)
            => IShR (p + n) -> Concrete (TKR2 (1 + n) x)
            -> (IntOf Concrete -> IxROf Concrete p)
            -> Concrete (TKR2 (p + n) x)
{-# INLINE tscatterZ1R #-}   -- this function takes a function as an argument
tscatterZ1R sh t f = case tftk knownSTK t of
  FTKR _ x ->
    let zero = tdefTarget (FTKR sh x)
        lt = trunravelToList t
        g i ti = let ix2 = f $ fromIntegral i
                 in if ixInBounds (fmapUnConcrete $ toList ix2) (toList sh)
                    then updateNR zero [(ix2, ti)]
                    else zero
        lu = imap g lt
    in foldr (taddTarget knownSTK) zero lu

-- The semantics of the operation permits index out of bounds
-- and the result of such indexing is def, which is 0.
tgatherZR :: forall m n p x. (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
          => IShR (m + n) -> Concrete (TKR2 (p + n) x)
          -> (IxROf Concrete m -> IxROf Concrete p)
          -> Concrete (TKR2 (m + n) x)
{-# INLINE tgatherZR #-}   -- this function takes a function as an argument
tgatherZR sh t f = case (SNat @n, knownSTK @x) of
  (SNat' @0, STKScalar) ->  -- an optimized common case
    let shm = sh
        s = shrSize shm
        l = [ unConcrete $
              t `trindex0` f (fmapConcrete $ fromLinearIdxR shm i)
            | i <- [0 .. fromIntegral s - 1] ]
    in Concrete $ Nested.rfromListPrimLinear shm l
  _ -> trbuild sh (\ix -> t `trindex` f ix)

tgatherZ1R :: forall n p x. (KnownNat n, KnownNat p, KnownSTK x)
           => Int -> Concrete (TKR2 (p + n) x)
           -> (IntOf Concrete -> IxROf Concrete p)
           -> Concrete (TKR2 (1 + n) x)
{-# INLINE tgatherZ1R #-}   -- this function takes a function as an argument
tgatherZ1R k t f = case (SNat @n, knownSTK @x) of
  (SNat' @0, STKScalar) ->  -- an optimized common case
    let l = [ unConcrete $ t `trindex0` (f (Concrete i))
            | i <- [0 .. fromIntegral (k - 1)] ]
    in Concrete $ Nested.rfromListPrimLinear (k :$: shrDrop (rshape t)) l
  _ | Dict <- eltDictRep (knownSTK @x) -> case k of
    0 -> Concrete
         $ Nested.rreshape (0 :$: shrDrop (rshape t)) Nested.remptyArray
    _ -> Concrete $ Nested.rfromListOuterN k $ NonEmpty.fromList
         $ map (\i -> unConcrete $ t `trindex` f (Concrete i))
               [0 .. fromIntegral (k - 1)]
             -- this must be slightly faster than just
             -- trbuild1 k (\ix -> t `trindex` f ix)

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

tbuild1R
  :: forall r n. (Nested.KnownElt r, KnownNat n)
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
{-# INLINE tbuild1R #-}
tbuild1R k f =
  Nested.runNest
  $ Nested.rgenerate (k :$: ZSR) $ \(i :.: ZIR) -> f (fromIntegral i)

tbuildR
  :: forall m n x. (KnownNat m, KnownNat n, Nested.KnownElt x)
  => IShR (m + n) -> (IxR m Int64 -> Nested.Ranked n x)
  -> Nested.Ranked (m + n) x
{-# INLINE tbuildR #-}
tbuildR sh f =
  Nested.runNest
  $ Nested.rgenerate (shrTake @m sh) $ \i -> f (fmap fromIntegral i)

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r) -> Nested.Ranked n r1
  -> Nested.Ranked n r
{-# INLINE tmap0NR #-}
tmap0NR f = Ranked.liftRanked1
              (Mixed.mliftPrim (Nested.runScalar . f . Nested.rscalar))
  -- too slow: tbuildNR (Nested.rshape v) (\ix -> f $ v `tindexNR` ix)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2 -> Nested.Ranked n r
{-# INLINE tzipWith0NR #-}
tzipWith0NR f =
  Ranked.liftRanked2
    (Mixed.mliftPrim2
       (\x y -> Nested.runScalar $ f (Nested.rscalar x) (Nested.rscalar y)))


-- * Shaped internal definitions

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
{-# INLINE liftVS #-}
liftVS f = Shaped.liftShaped1 (Mixed.mliftNumElt1 (`liftVEltwise1` f))

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r proxy.
            ( KnownSTK r, KnownShS sh, KnownShS (Drop n sh)
            , KnownShS (Take n sh) )
         => proxy n -> Concrete (TKS2 sh r)
         -> [(IxSOf Concrete (Take n sh), Concrete (TKS2 (Drop n sh) r))]
         -> Concrete (TKS2 sh r)
{-# INLINE updateNS #-}
updateNS _ arr upd = case knownSTK @r of
  STKScalar ->
    let values = stoVector arr
        sh = knownShS @sh
        f !t (ix, u) =
          let v = stoVector u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unConcrete
                  $ toLinearIdxS @(Take n sh) @(Drop n sh) sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in Concrete $ Nested.sfromVector knownShS (foldl' f values upd)
  _ -> case shsProduct (knownShS @(Take n sh)) of
    SNat ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = snest (knownShS @(Take n sh)) arr
          shNested = sshape arrNested
          f i v = case lookup (fromLinearIdxS @(Take n sh)
                                 shNested (fromIntegral i)) upd of
            Just u -> snest (knownShS @'[]) u
            Nothing -> v
      in sunNest @_ @(Take n sh) $ tfromListLinearS
         $ imap f $ tsunravelToList $ sflatten arrNested

tfromListLinearS
  :: forall sh x. (KnownShS sh, KnownSTK x)
  => [Concrete (TKS2 '[] x)] -> Concrete (TKS2 sh x)
{-# INLINE tfromListLinearS #-}
tfromListLinearS l | Dict <- eltDictRep (knownSTK @x) = Concrete $
  case NonEmpty.nonEmpty $ fmapUnConcrete l of
    Nothing -> case testEquality (shsProduct (knownShS @sh)) (SNat @0) of
      Just Refl -> Nested.sreshape (knownShS @sh)
                   $ Nested.semptyArray (knownShS @sh)
      Nothing -> error "xfromListLinear: empty list, but not shape"
    Just nl -> Nested.sfromListLinear knownShS
               $ NonEmpty.map Nested.sunScalar nl

tindexNS
  :: Nested.Elt x
  => Nested.Shaped (sh1 ++ sh2) x -> IxS sh1 Int64 -> Nested.Shaped sh2 x
{-# INLINE tindexNS #-}  -- the function is just a wrapper
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
tindexZS :: forall shm shn x. (KnownShS shm, KnownShS shn, KnownSTK x)
         => Concrete (TKS2 (shm ++ shn) x) -> IxSOf Concrete shm
         -> Concrete (TKS2 shn x)
{-# INLINE tindexZS #-}  -- the function is just a wrapper
tindexZS v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
     if ixInBounds (toList ix) (toList $ Nested.sshape uv)
         then Concrete $ tindexNS uv ix
         else case tftk knownSTK v of
           FTKS _sh x -> tdefTarget (FTKS knownShS x)

tindex0S :: (KnownShS sh1, GoodScalar r)
         => Concrete (TKS sh1 r) -> IxSOf Concrete sh1 -> Concrete (TKScalar r)
{-# INLINE tindex0S #-}  -- the function is just a wrapper
tindex0S v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete $ if ixInBounds (toList ix) (toList $ Nested.sshape uv)
                then Nested.sindex uv (fmap fromIntegral ix)
                else def
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

tscatterZS :: (KnownShS shm, KnownShS shn, KnownShS shp, TKAllNum x, KnownSTK x)
           => Concrete (TKS2 (shm ++ shn) x)
           -> (IxSOf Concrete shm -> IxSOf Concrete shp)
           -> Concrete (TKS2 (shp ++ shn) x)
  -- Performance depends a lot on the number and size of tensors.
  -- If tensors are not tiny, memory taken by underlying vectors matters most
  -- and this implementation is probaly optimal in this respect
  -- (the only new vectors are created by V.concat, but this is done on demand).
  -- TODO: optimize updateNS and make it consume and forget arguments
  -- one by one to make the above true
  --
  -- Note how ix being in bounds is checked. The semantics of the operation
  -- permits index out of bounds and then no tensors is added at such an index.
{-# INLINE tscatterZS #-}  -- this function takes a function as an argument
tscatterZS @shm @shn @shp t f =
  let shpshn = knownShS @shp `shsAppend` knownShS @shn
  in withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
     case tftk knownSTK t of
       FTKS _ x@(FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
         -- Optimized.
         gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn)
                                        :~: shp) $
         gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn)
                                        :~: shn) $
         let zero = tdefTarget @Concrete (FTKS shpshn x)
             shm = knownShS @shm
             s = shsSize shm
             g :: IxS shm Int64
               -> M.Map (IxSOf Concrete shp) (VS.Vector r)
               -> M.Map (IxSOf Concrete shp) (VS.Vector r)
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBounds (fmapUnConcrete $ toList ix2)
                                (shsToList shpshn)
                  then M.insertWith (V.zipWith (+)) ix2
                         (Nested.stoVector
                          $ tindexNS @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g M.empty [ fromLinearIdxS shm i
                                   | i <- [0 .. fromIntegral s - 1] ]
         in withKnownShS shpshn $
            updateNS (Proxy @(Rank shp)) zero
            $ map (second $ Concrete . Nested.sfromVector (knownShS @shn))
            $ M.assocs ivs
       FTKS _ x | Dict <- eltDictRep (ftkToSTK x) ->
         gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn)
                                     :~: shp) $
         gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn)
                                     :~: shn) $
         let zero = tdefTarget @Concrete (FTKS shpshn x)
             shm = knownShS @shm
             s = shsSize shm
             g ix =
               let ix2 = f $ fmapConcrete ix
               in if ixInBounds (fmapUnConcrete $ toList ix2)
                                (shsToList shpshn)
                  then M.insertWith (taddTarget knownSTK) ix2
                         (Concrete
                          $ tindexNS @_ @shm @shn (unConcrete t) ix)
                  else id
             ivs = foldr g M.empty [ fromLinearIdxS shm i
                                   | i <- [0 .. fromIntegral s - 1] ]
         in withKnownShS shpshn $
            updateNS (Proxy @(Rank shp)) zero
            $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S
  :: forall n2 shn shp x.
     (KnownNat n2, KnownShS shn, KnownShS shp, TKAllNum x, KnownSTK x)
  => Concrete (TKS2 (n2 ': shn) x)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS2 (shp ++ shn) x)
{-# INLINE tscatterZ1S #-}   -- this function takes a function as an argument
tscatterZ1S t f = case tftk knownSTK t of
  FTKS _ x ->
    gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
    gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
    let shpshn = knownShS @shp `shsAppend` knownShS @shn
        zero = tdefTarget (FTKS shpshn x)
        lt = tsunravelToList t
        g i ti = let ix2 = f $ fromIntegral i
                 in if ixInBounds (fmapUnConcrete $ toList ix2)
                                  (shsToList shpshn)
                    then withKnownShS shpshn $
                         updateNS (Proxy @(Rank shp)) zero [(ix2, ti)]
                    else zero
        lu = imap g lt
    in foldr (taddTarget (STKS shpshn (knownSTK @x))) zero lu

tgatherZS :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x)
          => Concrete (TKS2 (shp ++ shn) x)
          -> (IxSOf Concrete shm -> IxSOf Concrete shp)
          -> Concrete (TKS2 (shm ++ shn) x)
{-# INLINE tgatherZS #-}  -- this function takes a function as an argument
tgatherZS @shm @shn @shp @r t f =
  gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
  case (knownShS @shn, knownSTK @r) of
    (ZSS, STKScalar) | Refl <- lemAppNil @shm
                     , Refl <- lemAppNil @shp ->  -- an optimized common case
      let shm = knownShS @shm
          s = shsSize shm
          l = [ unConcrete $
                t `tsindex0` f (fmapConcrete $ fromLinearIdxS shm i)
              | i <- [0 .. fromIntegral s - 1] ]
      in Concrete $ Nested.sfromListPrimLinear shm l
    _ ->
      withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
      case shsRank (knownShS @shm) of
        SNat -> -- needed only for GHC 9.10
          tsbuild @_ @(Rank shm) SNat (\ix -> t `tsindex` f ix)

tgatherZ1S
  :: (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x)
  => Concrete (TKS2 (shp ++ shn) x)
  -> (IntOf Concrete -> IxSOf Concrete shp)
  -> Concrete (TKS2 (n2 ': shn) x)
{-# INLINE tgatherZ1S #-}   -- this function takes a function as an argument
tgatherZ1S @n2 @shn @shp @x t f = case (knownShS @shn, knownSTK @x) of
  (ZSS, STKScalar) | Refl <- lemAppNil @shp ->  -- an optimized common case
    let l = [ unConcrete $ t `tsindex0` (f (Concrete i))
            | i <- [0 .. valueOf @n2 - 1] ]
    in Concrete $ Nested.sfromListPrimLinear knownShS l
  _ | Dict <- eltDictRep (knownSTK @x) -> case SNat @n2 of
    SNat' @0 -> Concrete $ Nested.semptyArray knownShS
    _ ->
      Concrete $ Nested.sfromListOuter SNat $ NonEmpty.fromList
      $ map (\i -> unConcrete $ t `tsindex` f (Concrete i))
            [0 .. valueOf @n2 - 1]
        -- this must be slightly faster than just
        -- tsbuild1 (\ix -> t `tsindex` f ix)

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

tbuild1S
  :: forall k sh x. (KnownNat k, KnownShS sh, Nested.KnownElt x)
  => (Int64 -> Nested.Shaped sh x) -> Nested.Shaped (k ': sh) x
{-# INLINE tbuild1S #-}
tbuild1S f =
  Nested.sunNest
  $ Nested.sgenerate (SNat @k :$$ ZSS) $ \(i :.$ ZIS) -> f (fromIntegral i)

tbuildS
  :: forall m sh x.
     (KnownShS (Take m sh), KnownShS (Drop m sh), Nested.KnownElt x)
  => (IxS (Take m sh) Int64 -> Nested.Shaped (Drop m sh) x)
  -> Nested.Shaped sh x
{-# INLINE tbuildS #-}
tbuildS f =
  gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh) $
  Nested.sunNest
  $ Nested.sgenerate (knownShS @(Take m sh)) $ \i -> f (fmap fromIntegral i)

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r) -> Nested.Shaped sh r1
  -> Nested.Shaped sh r
{-# INLINE tmap0NS #-}
tmap0NS f =
  Shaped.liftShaped1
    (Mixed.mliftPrim (Nested.sunScalar . f . Nested.sscalar))
      -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
{-# INLINE tzipWith0NS #-}
tzipWith0NS f =
  Shaped.liftShaped2
    (Mixed.mliftPrim2
       (\x y -> Nested.sunScalar $ f (Nested.sscalar x) (Nested.sscalar y)))


-- * Mixed internal definitions

liftVX
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Mixed sh r1 -> Nested.Mixed sh r
{-# INLINE liftVX #-}
liftVX f = Mixed.mliftNumElt1 (`liftVEltwise1` f)

updateNX :: forall n sh r proxy.
            (KnownSTK r, KnownShX (Drop n sh), KnownShX (Take n sh))
         => proxy n -> Concrete (TKX2 sh r)
         -> [(IxXOf Concrete (Take n sh), Concrete (TKX2 (Drop n sh) r))]
         -> Concrete (TKX2 sh r)
{-# INLINE updateNX #-}
updateNX _ arr upd = case knownSTK @r of
  STKScalar ->
    let values = xtoVector arr
        sh = xshape arr
        f !t (ix, u) =
          let v = xtoVector u
              i = gcastWith (unsafeCoerceRefl
                             :: sh :~: Take n sh ++ Drop n sh)
                  $ fromIntegral $ unConcrete
                  $ toLinearIdxX @(Take n sh) @(Drop n sh) sh ix
          in V.concat [V.take i t, v, V.drop (i + V.length v) t]
    in Concrete $ Nested.mfromVector (xshape arr) (foldl' f values upd)
  _ | Dict <- eltDictRep (knownSTK @r) ->
      gcastWith (unsafeCoerceRefl :: sh :~: Take n sh ++ Drop n sh) $
      let arrNested = xnest (knownShX @(Take n sh)) arr
          shNested = xshape arrNested
          f i v = case lookup (fromLinearIdxX @(Take n sh)
                                 shNested (fromIntegral i)) upd of
            Just u -> xnest ZKX u
            Nothing -> v
      in withSNat (shxSize shNested) $ \snat ->
           xunNest @_ @(Take n sh) $ tfromListLinearX shNested
           $ imap f $ txunravelToList
           $ Concrete $ Nested.mcast (Nested.SKnown snat :!% ZKX)
           $ unConcrete $ xflatten arrNested

tfromListLinearX
  :: forall x sh. KnownSTK x
  => IShX sh -> [Concrete (TKX2 '[] x)] -> Concrete (TKX2 sh x)
{-# INLINE tfromListLinearX #-}
tfromListLinearX sh l | Dict <- eltDictRep (knownSTK @x) = Concrete $
  case NonEmpty.nonEmpty $ fmapUnConcrete l of
    Nothing -> if shxSize sh == 0
               then Nested.mreshape sh $ Nested.memptyArray sh
               else error "xfromListLinear: empty list, but not shape"
    Just nl -> Nested.mfromListLinear sh $ NonEmpty.map Nested.munScalar nl

tindexNX
  :: Nested.Elt r
  => Nested.Mixed (sh1 ++ sh2) r -> IxX sh1 Int64 -> Nested.Mixed sh2 r
{-# INLINE tindexNX #-}  -- the function is just a wrapper
tindexNX v ix = Nested.mindexPartial v (fmap fromIntegral ix)

tindexZX :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
         => Concrete (TKX2 (sh1 ++ sh2) x) -> IxXOf Concrete sh1
         -> Concrete (TKX2 sh2 x)
{-# INLINE tindexZX #-}  -- the function is just a wrapper
tindexZX @sh1 @sh2 @x v ixConcrete | Dict <- eltDictRep (knownSTK @x) =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
     if ixInBounds (toList ix) (toList $ Nested.mshape uv)
     then Concrete $ tindexNX uv ix
     else case tftk knownSTK v of
       FTKX sh x -> tdefTarget (FTKX (shxDropSSX (knownShX @sh1) sh) x)

tindex0X :: (KnownShX sh1, GoodScalar r)
         => Concrete (TKX sh1 r) -> IxXOf Concrete sh1 -> Concrete (TKScalar r)
{-# INLINE tindex0X #-}  -- the function is just a wrapper
tindex0X v ixConcrete =
  let uv = unConcrete v
      ix = fmapUnConcrete ixConcrete
  in Concrete $ if ixInBounds (toList ix) (toList $ Nested.mshape uv)
                then Nested.mindex uv (fmap fromIntegral ix)
                else def

tscatterZX :: ( KnownShX shm, KnownShX shn, KnownShX shp
              , TKAllNum x, KnownSTK x )
           => IShX (shp ++ shn) -> Concrete (TKX2 (shm ++ shn) x)
           -> (IxXOf Concrete shm -> IxXOf Concrete shp)
           -> Concrete (TKX2 (shp ++ shn) x)
{-# INLINE tscatterZX #-}  -- this function takes a function as an argument
tscatterZX @shm @shn @shp sh t f =
  withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
  gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
  case tftk knownSTK t of
    FTKX _ x@(FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
      -- Optimized.
      let zero = tdefTarget (FTKX sh x)
          shm = shxTakeSSX (Proxy @shn) (knownShX @shm) (xshape t)
          shDropP = shxDropSSX (knownShX @shm) (xshape t)
          s = shxSize shm
          g :: IxX shm Int64
            -> M.Map (IxXOf Concrete shp) (VS.Vector r)
            -> M.Map (IxXOf Concrete shp) (VS.Vector r)
          g ix =
            let ix2 = f $ fmapConcrete ix
            in if ixInBounds (fmapUnConcrete $ toList ix2) (shxToList sh)
               then M.insertWith (V.zipWith (+)) ix2
                      (Nested.mtoVector
                       $ tindexNX @_ @shm @shn (unConcrete t) ix)
               else id
          ivs = foldr g M.empty [ fromLinearIdxX shm i
                                | i <- [0 .. fromIntegral s - 1] ]
      in updateNX (Proxy @(Rank shp)) zero
         $ map (second $ Concrete . Nested.mfromVector shDropP)
         $ M.assocs ivs
    FTKX _ x | Dict <- eltDictRep (ftkToSTK x) ->
      let zero = tdefTarget (FTKX sh x)
          shm = shxTakeSSX (Proxy @shn) (knownShX @shm) (xshape t)
          s = shxSize shm
          g ix =
            let ix2 = f $ fmapConcrete ix
            in if ixInBounds (fmapUnConcrete $ toList ix2) (shxToList sh)
               then M.insertWith (taddTarget knownSTK) ix2
                      (Concrete
                       $ tindexNX @_ @shm @shn (unConcrete t) ix)
               else id
          ivs = foldr g M.empty [ fromLinearIdxX shm i
                                | i <- [0 .. fromIntegral s - 1] ]
      in updateNX (Proxy @(Rank shp)) zero
         $ M.assocs ivs

tscatterZ1X :: ( KnownNat n2, KnownShX shn, KnownShX shp
               , TKAllNum x, KnownSTK x )
            => IShX (shp ++ shn) -> Concrete (TKX2 (Just n2 ': shn) x)
            -> (IntOf Concrete -> IxXOf Concrete shp)
            -> Concrete (TKX2 (shp ++ shn) x)
{-# INLINE tscatterZ1X #-}   -- this function takes a function as an argument
tscatterZ1X @_ @shn @shp sh t f =
  case tftk knownSTK t of
    FTKX _ x ->
      withKnownShX (ssxFromShX sh) $
      gcastWith (unsafeCoerceRefl :: Take (Rank shp) (shp ++ shn) :~: shp) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank shp) (shp ++ shn) :~: shn) $
      let zero = tdefTarget (FTKX sh x)
          lt = txunravelToList t
          g i ti = let ix2 = f $ fromIntegral i
                   in if ixInBounds (fmapUnConcrete $ toList ix2)
                                    (shxToList sh)
                      then updateNX (Proxy @(Rank shp)) zero [(ix2, ti)]
                      else zero
          lu = imap g lt
      in foldr (taddTarget knownSTK) zero lu

tgatherZX :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
          => IShX (shm ++ shn)
          -> Concrete (TKX2 (shp ++ shn) x)
          -> (IxXOf Concrete shm -> IxXOf Concrete shp)
          -> Concrete (TKX2 (shm ++ shn) x)
{-# INLINE tgatherZX #-}  -- this function takes a function as an argument
tgatherZX @shm @shn @shp @r sh t f =
  gcastWith (unsafeCoerceRefl :: Take (Rank shm) (shm ++ shn) :~: shm) $
  gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
  case (knownShX @shn, knownSTK @r) of
    (ZKX, STKScalar) | Refl <- lemAppNil @shm
                     , Refl <- lemAppNil @shp ->  -- an optimized common case
      let shm = sh
          s = shxSize shm
          l = [ unConcrete $
                t `txindex0` f (fmapConcrete $ fromLinearIdxX shm i)
              | i <- [0 .. fromIntegral s - 1] ]
      in Concrete $ Nested.mfromListPrimLinear shm l
    _ ->
      withKnownShX (ssxFromShX sh) $
      case ssxRank (knownShX @shm) of
        SNat -> -- needed only for GHC 9.10
          txbuild @_ @(Rank shm) SNat sh (\ix -> t `txindex` f ix)

tgatherZ1X :: forall n2 shn shp x.
              (KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x)
           => SNat n2 -> Concrete (TKX2 (shp ++ shn) x)
           -> (IntOf Concrete -> IxXOf Concrete shp)
           -> Concrete (TKX2 (Just n2 ': shn) x)
{-# INLINE tgatherZ1X #-}   -- this function takes a function as an argument
tgatherZ1X n2@SNat t f = case (knownShX @shn, knownSTK @x) of
  (ZKX, STKScalar) | Refl <- lemAppNil @shp ->  -- an optimized common case
    let l = [ unConcrete $ t `txindex0` (f (Concrete i))
            | i <- [0 .. valueOf @n2 - 1] ]
    in Concrete
       $ Nested.mfromListPrimLinear
           (SKnown SNat :$% shxDropSSX (knownShX @shp) (xshape t)) l
  _ | Dict <- eltDictRep (knownSTK @x) -> case n2 of
    SNat' @0 ->
      Concrete $ Nested.memptyArray (shxDropSSX (knownShX @shp) $ xshape t)
    _ ->
      Concrete
      $ Nested.mfromListOuterSN n2 $ NonEmpty.fromList
      $ map (\i -> unConcrete $ t `txindex` f (Concrete i))
            [0 .. valueOf @n2 - 1]
        -- this must be slightly faster than just
        -- txbuild1 @_ @n2 (\ix -> t `txindex` f ix)

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

tbuild1X
  :: forall k sh r. (KnownNat k, KnownShX sh, Nested.KnownElt r)
  => (Int64 -> Nested.Mixed sh r) -> Nested.Mixed (Just k ': sh) r
{-# INLINE tbuild1X #-}
tbuild1X f =
  Nested.munNest
  $ Nested.mgenerate (Nested.SKnown (SNat @k) :$% ZSX) $ \(i :.% ZIX) ->
      f (fromIntegral i)
tbuildX
  :: forall m sh x.
     (KnownShX (Take m sh), KnownShX (Drop m sh), Nested.KnownElt x)
  => IShX sh -> (IxX (Take m sh) Int64 -> Nested.Mixed (Drop m sh) x)
  -> Nested.Mixed sh x
{-# INLINE tbuildX #-}
tbuildX sh f =
  gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh) $
  Nested.munNest
  $ Nested.mgenerate
      (shxTakeSSX (Proxy @(Drop m sh)) (knownShX @(Take m sh)) sh) $ \i ->
        f (fmap fromIntegral i)
