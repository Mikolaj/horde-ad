{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, here we do not abstract over
-- the typing of tensors and so we give separate instances
-- for ranked tensors and shaped tensors.
module HordeAd.Core.OpsADVal
  ( crevOnADInputs, crevOnHVector, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)
import Data.Maybe (fromMaybe)

import Data.Array.Nested
  ( StaticShX(..)
  , ShR (..)
  , ShX (..)
  , ShS (..)
  , KnownShS (..)
  , KnownShX (..)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (withKnownShS)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (withKnownShX, ssxFromShape, fromSMayNat')

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Unwind
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Non-symbolic reverse and forward derivative computation

-- The user-written function f can do anything, so the inputs
-- argument has to be duplicable.
crevOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullTensorKind x -> ADVal target x
  -> (target (ADTensorKind x), target z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f xftk inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D v delta) = f inputs in
  let zftk = ftkDelta delta
      dt = fromMaybe (constantTarget 1 $ adFTK zftk) mdt
      !gradient = gradientFromDelta xftk zftk dt delta
  in (gradient, v)

crevOnHVector
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullTensorKind x -> target x
  -> (target (ADTensorKind x), target z)
{-# INLINE crevOnHVector #-}
crevOnHVector edt f xftk parameters =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in crevOnADInputs edt f xftk inputs

cfwdOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullTensorKind x -> ADVal target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs xftk inputs f ds =
  let !(D v delta) = f inputs in
  let !derivative = derivativeFromDelta @x delta (adFTK xftk) ds
  in (derivative, v)

cfwdOnHVector
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullTensorKind x -> target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
{-# INLINE cfwdOnHVector #-}
cfwdOnHVector xftk parameters f ds =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in cfwdOnADInputs xftk inputs f ds


-- * Instances

fromPrimalFTK :: FullTensorKind z -> f z -> ADVal f z
fromPrimalFTK ftk a = dDnotShared a (DeltaZero ftk)

-- This instance can be sped up by defining and simplifying all default
-- methods (or only tfromVector?), but it probably benefits only product
-- tensor kinds, which are probably not a bottleneck in realistic examples.
instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => LetTensor (ADVal target) where
  ttlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')
  toShare = id
  tunshare = id
  tD _stk t d = dD t d

instance (ADReadyNoLet target, ShareTensor target)
         => ShareTensor (ADVal target) where
  tshare = id
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unDeltaPair u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => BaseTensor (ADVal target) where
  tconstantTarget = constantTarget
  taddTarget = addTarget

  -- Ranked ops
  rshape (D u _) = rshape u
  rsum (D u u') = withSNat (rwidth u) $ \snat ->
    dD (rsum u) (DeltaSum snat knownSTK u')
  rsum0 (D u u') = dD (rsum0 u) (DeltaSum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (dAdd (DeltaDot0R v u') (DeltaDot0R u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
  rmatvecmul m v = rsum (rtr (rreplicate (rwidth m) v * m))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR ->
      rsum (rtranspose [2,1,0] (rreplicate width2 m1)
            * rtranspose [1,0] (rreplicate (rwidth m1) m2))
  rreplicate k (D u u') = withSNat k $ \snat ->
    dD (rreplicate k u) (DeltaReplicate snat knownSTK u')
  -- TODO: speed up by using tindex0R and dDeltaIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dDeltaIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex (D u u') i =
    let ix = tprimalPart <$> i
    in dD (rindex u ix) (DeltaIndexR SNat u' ix)
  rscatter sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (rscatter sh u g) (DeltaScatterR SNat SNat SNat sh u' g)
  rgather sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (rgather sh u g) (DeltaGatherR SNat SNat SNat sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  trconcrete a =
    let v = trconcrete a
    in fromPrimalFTK (FTKR (Nested.rshape a) FTKScalar) v
  rfloor (D u _) =
    let v = rfloor u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  rcast (D u u') = dD (rcast u) (DeltaCastR u')
  rminIndex (D u _) =
    let v = rminIndex u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  riota n = fromPrimalFTK (FTKR (n :$: ZSR) FTKScalar) $ riota n
  rappend (D u u') (D v v') = dD (rappend u v) (DeltaAppendR u' v')
  rslice i n (D u u') = dD (rslice i n u) (DeltaSliceR i n u')
  rreverse (D u u') = dD (rreverse u) (DeltaReverseR u')
  rtranspose perm (D u u') = dD (rtranspose perm u) (DeltaTransposeR perm u')
  rreshape sh (D u u') = dD (rreshape sh u) (DeltaReshapeR sh u')
  rbuild1 @r @n k f = case NonEmpty.nonEmpty [0 .. fromIntegral k - 1] of
    Nothing -> case sameNat (Proxy @n) (Proxy @0) of
      Just Refl | Dict <- eltDictRep (knownSTK @r) ->
        let arr = Nested.remptyArray
        in tconcrete (tftkG knownSTK arr) (RepN arr)
      Nothing -> error "rbuild1: shape ambiguity"
    Just l -> rfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Shaped ops
  sshape (D u _) = sshape u
  ssum (D u u') = dD (ssum u) (DeltaSum SNat knownSTK u')
  ssum0 (D u u') = dD (ssum0 u) (DeltaSum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (dAdd (DeltaDot0S v u') (DeltaDot0S u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
  smatvecmul m v = ssum (str (sreplicate v * m))
  smatmul2 m1 m2 =
    ssum (stranspose @_ @'[2, 1, 0] (sreplicate m1)
          * stranspose @_ @'[1, 0] (sreplicate m2))
  sindex (D u u') i =
    let ix = tprimalPart <$> i
    in dD (sindex u ix) (DeltaIndexS knownShS u' ix)
  sscatter @r @shm @shn @shp (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (sscatter @_ @r @shm @shn @shp u g)
          (DeltaScatterS @shm @shn @shp knownShS knownShS knownShS u' g)
  sgather @r @shm @shn @shp (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (sgather @_ @r @shm @shn @shp u g)
          (DeltaGatherS @shm @shn @shp knownShS knownShS knownShS u' g)
  tsconcrete a =
    let v = tsconcrete a
    in fromPrimalFTK (FTKS (Nested.sshape a) FTKScalar) v
  sfloor (D u _) =
    let v = sfloor u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  scast (D u u') = dD (scast u) (DeltaCastS u')
  sminIndex (D u _) =
    let v = sminIndex u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  smaxIndex (D u _) =
    let v = smaxIndex u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  siota = fromPrimalFTK (FTKS (SNat :$$ ZSS) FTKScalar) siota
  sappend (D u u') (D v v') = dD (sappend u v) (DeltaAppendS u' v')
  sslice i n k (D u u') = dD (sslice i n k u) (DeltaSliceS i n k u')
  sreverse (D u u') = dD (sreverse u) (DeltaReverseS u')
  sbuild1 @k @sh @r f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
    Nothing | Dict <- eltDictRep (knownSTK @r) ->
      let arr = Nested.semptyArray @(RepORArray r) (knownShS @sh)
      in gcastWith (unsafeCoerceRefl :: k :~: 0) $
         tconcrete (tftkG knownSTK arr) (RepN arr)
    Just l -> sfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Mixed ops
  xshape (D u _) = xshape u
  xsum (D u u') = dD (xsum u) (DeltaSum SNat knownSTK u')
  xsum0 (D u u') = dD (xsum0 u) (DeltaSum0X u')
  xdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (xdot0 u v) (dAdd (DeltaDot0X v u') (DeltaDot0X u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
  xmatvecmul mm mn m v =
    withKnownShX (ssxFromShape $ mn :$% ZSX) $
    withKnownShX (ssxFromShape $ mm :$% mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @m) ->
    withSNat (fromSMayNat' mn) $ \(SNat @n) ->
      xmcast (ssxFromShape (mm :$% ZSX))
      $ xsum (xtr (xreplicate @_ @m
                     (xmcast (ssxFromShape (Nested.SKnown (SNat @n)
                                            :$% ZSX)) v)
                   * xmcast (ssxFromShape (Nested.SKnown (SNat @m)
                                           :$% Nested.SKnown (SNat @n)
                                           :$% ZSX)) m))
  xmatmul2 m1 m2 =
    xsum (xtranspose @_ @'[2, 1, 0] (xreplicate m1)
          * xtranspose @_ @'[1, 0] (xreplicate m2))
  xreplicate (D u u') = dD (xreplicate u) (DeltaReplicate SNat knownSTK u')
  xindex (D u u') i =
    let ix = tprimalPart <$> i
    in dD (xindex u ix) (DeltaIndexX knownShX u' ix)
  xscatter @r @shm @shn @shp sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (xscatter @_ @r @shm @shn @shp sh u g)
          (DeltaScatterX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  xgather @r @shm @shn @shp sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (xgather @_ @r @shm @shn @shp sh u g)
          (DeltaGatherX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  txconcrete a =
    let v = txconcrete a
    in fromPrimalFTK (FTKX (Nested.mshape a) FTKScalar) v
  xfloor (D u _) =
    let v = xfloor u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  xfromIntegral (D u _) =
    let v = xfromIntegral u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  xcast (D u u') = dD (xcast u) (DeltaCastX u')
  xminIndex (D u _) =
    let v = xminIndex u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  xmaxIndex (D u _) =
    let v = xmaxIndex u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  xiota = fromPrimalFTK (FTKX (Nested.SKnown SNat :$% ZSX) FTKScalar) xiota
  xappend (D u u') (D v v') = dD (xappend u v) (DeltaAppendX u' v')
  xslice i n k (D u u') = dD (xslice i n k u) (DeltaSliceX i n k u')
  xreverse (D u u') = dD (xreverse u) (DeltaReverseX u')
  xtranspose @perm (D u u') =
    dD (xtranspose @_ @perm u) (DeltaTransposeX @_ @_ @_ @target (Permutation.makePerm @perm) u')
  xreshape sh (D u u') = dD (xreshape sh u) (DeltaReshapeX sh u')
  xbuild1 @k @sh @r f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
    Nothing -> case testEquality (knownShX @sh) ZKX of
      Just Refl | Dict <- eltDictRep (knownSTK @r) ->
        let arr = Nested.memptyArray @(RepORArray r) ZSX
        in gcastWith (unsafeCoerceRefl :: k :~: 0) $
           tconcrete (tftkG knownSTK arr) (RepN arr)
      Nothing -> error "xbuild1: shape ambiguity"
    Just l -> xfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Scalar ops
  tkconcrete a =
    let v = tkconcrete a
    in fromPrimalFTK FTKScalar v
  kfloor (D u _) =
    let v = kfloor u
    in fromPrimalFTK FTKScalar v
  kfromIntegral (D u _) =
    let v = kfromIntegral u
    in fromPrimalFTK FTKScalar v
  kcast (D u u') = dD (kcast u) (DeltaCastK u')

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk (D _ u') = ftkDelta u'
  tconcrete ftk t | Dict <- lemKnownSTK (ftkToSTK ftk) =
    fromPrimalFTK ftk $ tconcrete ftk t
  tpair (D u u') (D v v') = dDnotShared (tpair u v) (DeltaPair u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unDeltaPairUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unDeltaPairUnshared u')
  tsreplicate sh (D u u') =
    dD (tsreplicate sh u) (DeltaReplicate SNat (STKS sh knownSTK) u')
  stranspose @perm = tstranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  tstranspose perm (D u u') =
    dD (tstranspose perm u) (DeltaTransposeS @_ @_ @_ @target perm u')
  tsreshape sh (D u u') = dD (tsreshape sh u) (DeltaReshapeS sh u')
  tmapAccumRDer @accShs @bShs @eShs _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (ftkToSTK accShs)
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eShs) =
    let !(D acc0 acc0') = acc0D in
    let !(D esNotShared es') = esD in
    let es = tshare esNotShared
        codomainShs = FTKProduct accShs bShs
        g :: forall f. ADReady f
          => f (TKProduct accShs eShs)
          -> f (TKProduct accShs (TKProduct accShs bShs))
        g !acc_e =
          tlet acc_e $ \ !acc_e1 ->
          tlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs eShs))
                           (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs (TKProduct accShs bShs)))
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in tlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs
                                         (TKProduct accShs bShs)))
                           (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs eShs))
        rg !args =
          tlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in tlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in tlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in tlet (unHFun rf (tpair dx_dbRes acc_e)) $ \ !daccRes_deRes ->
                  let added = addTarget (adSTK $ ftkToSTK accShs)
                                        (tproject1 daccRes_deRes)
                                        (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = tmapAccumRDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumR k bShs eShs q es df rf acc0' es'
    in dD (tpair accFin bs) dual
  tmapAccumLDer @accShs @bShs @eShs _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (ftkToSTK accShs)
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eShs) =
    let !(D acc0 acc0') = acc0D in
    let !(D esNotShared es') = esD in
    let es = tshare esNotShared
        codomainShs = FTKProduct accShs bShs
        g :: forall f. ADReady f
          => f (TKProduct accShs eShs)
          -> f (TKProduct accShs (TKProduct accShs bShs))
        g !acc_e =
          tlet acc_e $ \ !acc_e1 ->
          tlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs eShs))
                           (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs (TKProduct accShs bShs)))
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in tlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accShs
                                         (TKProduct accShs bShs)))
                           (TKProduct accShs eShs))
           -> f (ADTensorKind (TKProduct accShs eShs))
        rg !args =
          tlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in tlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in tlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in tlet (unHFun rf (tpair dx_dbRes acc_e)) $ \ !daccRes_deRes ->
                  let added = addTarget (adSTK $ ftkToSTK accShs)
                                        (tproject1 daccRes_deRes)
                                        (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = tmapAccumLDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumL k bShs eShs q es df rf acc0' es'
    in dD (tpair accFin bs) dual
  tApply (HFun f) = f
  tlambda _ = id
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v =
    let uv = tfromVector (SNat @2) stk (V.fromList [u, v])
    in tindexBuild (SNat @2) stk uv (ifF b 0 1)
  tprimalPart (D u _) = u
  tdualPart _stk (D _ u') = u'
  tfromPrimal stk t = fromPrimalFTK (tftk stk t) t
  tfromDual t = dDnotShared (constantTarget 0 (ftkDelta t)) t
  tScale stk k = withKnownSTK stk $ dScale k
  trev @x xftk h =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = tlet a $ \ !aShared ->
          tunshare $ fst $ crevOnHVector
                             Nothing
                             (unHFun h @(ADVal (ShareOf f)))
                             xftk
                             (toShare aShared)
    in HFun rf
  trevDt @x @z xftk h =
    let rf :: forall f. ADReady f
           => f (TKProduct (ADTensorKind z) x)
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new db and a.
        rf !db_a = tlet db_a $ \ !db_aShared ->
          tunshare $ fst $ crevOnHVector
                             (Just $ toShare $ tproject1 db_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             xftk
                             (toShare $ tproject2 db_aShared)
    in HFun rf
  tfwd @x @z xftk h =
    let df :: forall f. ADReady f
           => f (TKProduct (ADTensorKind x) x)
           -> f (ADTensorKind z)
        -- This computes the derivative of g again for each new da and a.
        df !da_a = tlet da_a $ \ !da_aShared ->
          tunshare $ fst $ cfwdOnHVector
                             xftk
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df

  tfromVector snat stk lu =
    dD (tfromVector snat stk $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector snat stk $ V.map (\(D _ u') -> u') lu)

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => ConvertTensor (ADVal target) where
  rzip (D u u') = dD (rzip u) (DeltaZipR u')
  runzip (D u u') = dD (runzip u) (DeltaUnzipR u')
  szip (D u u') = dD (szip u) (DeltaZipS u')
  sunzip (D u u') = dD (sunzip u) (DeltaUnzipS u')
  xzip (D u u') = dD (xzip u) (DeltaZipX u')
  xunzip (D u u') = dD (xunzip u) (DeltaUnzipX u')

  -- This avoids product eta-expansions for AST instance primal,
  -- though contangent expands anyway.
  tfromS ystk zstk (D u u') =
    dDnotShared (tfromS ystk zstk u) (dFromS zstk u')
  rfromX a@(D _ u') = case ftkDelta u' of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a@(D _ u') =
   case ftkDelta u' of
    FTKR shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  sfromK (D t d) = dDnotShared (sfromK t) (DeltaSFromK d)
  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR knownShS u')
  sfromX (D u u') = dDnotShared (sfromX u) (dSFromX knownShS u')

  xnestR sh1 (D u u') = dD (xnestR sh1 u) (DeltaXNestR sh1 SNat u')
  xnestS sh1 (D u u') = dD (xnestS sh1 u) (DeltaXNestS sh1 knownShS u')
  xnest sh1 (D u u') = dD (xnest sh1 u) (DeltaXNest sh1 knownShX u')
  xunNestR (D u u') = dD (xunNestR u) (DeltaXUnNestR u')
  xunNestS (D u u') = dD (xunNestS u) (DeltaXUnNestS u')
  xunNest (D u u') = dD (xunNest u) (DeltaXUnNest u')
