{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. All definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms or anything else (e.g., nested 'ADVal').
module HordeAd.Core.OpsADVal
  ( crevOnADInputs, crevOnParams, cfwdOnParams
  ) where

import Prelude hiding (foldl')

import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)

import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Non-symbolic (or at least non-sharing) reverse and forward derivative computation

-- The user-written function f can do anything, so the inputs
-- argument has to be duplicable.
crevOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> ADVal target x
  -> (target (ADTensorKind x), target z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f xftk inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D v delta) = f inputs in
  let zftk = ftkDelta delta
      dt = fromMaybe (treplTarget 1 $ adFTK zftk) mdt
      !gradient = gradientFromDelta xftk zftk dt delta
  in (gradient, v)

crevOnParams
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> target x
  -> (target (ADTensorKind x), target z)
{-# INLINE crevOnParams #-}
crevOnParams edt f xftk parameters =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in crevOnADInputs edt f xftk inputs

cfwdOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK x -> ADVal target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs xftk inputs f ds =
  let !(D v delta) = f inputs in
  let !derivative = derivativeFromDelta @x delta (adFTK xftk) ds
  in (derivative, v)

cfwdOnParams
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK x -> target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
{-# INLINE cfwdOnParams #-}
cfwdOnParams xftk parameters f ds =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in cfwdOnADInputs xftk inputs f ds


-- * Instances

fromPrimalFTK :: FullShapeTK z -> f z -> ADVal f z
fromPrimalFTK ftk a = dDnotShared a (DeltaZero ftk)

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => LetTensor (ADVal target) where
  ttlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')  -- u' was already shared
  ttletPrimal u f =
    let !var2 = tshare u
    in f var2
  toShare = id
  tunshare = id
  tD _stk = dD

instance (ADReadyNoLet target, ShareTensor target)
         => ShareTensor (ADVal target) where
  tshare (D u u') = dDnotShared (tshare u) u'  -- u' was already shared
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unDeltaPair u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)

-- Note that this instance doesn't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the best pipeline, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Concrete instantiation is used in other pipelines and tests.
instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => BaseTensor (ADVal target) where
  -- Ranked ops
  rshape (D u _) = rshape u
  trsum (D u u') = withSNat (rwidth u) $ \snat ->
    dD (trsum u) (DeltaSum snat knownSTK u')
  trsum0 (D u u') = dD (trsum0 u) (DeltaSum0R u')
  trdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (trdot0 u v) (dAdd (DeltaDot0R v u') (DeltaDot0R u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
  trmatvecmul m v = trsum (rtr (trreplicate (rwidth m) v * m))
  trmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR ->
      trsum (trtranspose [2,1,0] (trreplicate width2 m1)
             * trtranspose [1,0] (trreplicate (rwidth m1) m2))
  trreplicate k (D u u') = withSNat k $ \snat ->
    dD (trreplicate k u) (DeltaReplicate snat knownSTK u')
  trindex (D u u') i =
    let !ix = tshare . tprimalPart <$> i
    in dD (trindex u ix) (DeltaIndexR SNat u' ix)
  trscatter sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (trscatter sh u g) (DeltaScatterR SNat SNat SNat sh u' g)
  trgather sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (trgather sh u g) (DeltaGatherR SNat SNat SNat sh u' g)
      -- Note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on.
      -- Note also how g is duplicated and this leads to loss of sharing
      -- of indexes in AST instances.
  trconcrete a =
    let v = trconcrete a
    in fromPrimalFTK (FTKR (Nested.rshape a) FTKScalar) v
  trfloor (D u _) =
    let v = trfloor u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  trfromIntegral (D u _) =
    let v = trfromIntegral u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  trcast (D u u') = dD (trcast u) (DeltaCastR u')
  trminIndex (D u _) =
    let v = trminIndex u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  trmaxIndex (D u _) =
    let v = trmaxIndex u
    in fromPrimalFTK (FTKR (rshape v) FTKScalar) v
  triota n = fromPrimalFTK (FTKR (n :$: ZSR) FTKScalar) $ triota n
  trappend (D u u') (D v v') = dD (trappend u v) (DeltaAppendR u' v')
  trslice i n (D u u') = dD (trslice i n u) (DeltaSliceR i n u')
  trreverse (D u u') = dD (trreverse u) (DeltaReverseR u')
  trtranspose perm (D u u') = dD (trtranspose perm u) (DeltaTransposeR perm u')
  trreshape sh (D u u') = dD (trreshape sh u) (DeltaReshapeR sh u')
  trbuild1 @n @x k f =
    let l = [0 .. fromIntegral k - 1]
    in if null l
       then case sameNat (Proxy @n) (Proxy @0) of
         Just Refl | Dict <- eltDictRep (knownSTK @x) ->
           let arr = Nested.remptyArray
           in tconcrete (tftkG knownSTK arr) (Concrete arr)
         Nothing -> error "rbuild1: shape ambiguity"
       else trfromVector $ V.fromList $ map (f . fromInteger) l
              -- hope this fuses

  -- Shaped ops
  sshape (D u _) = sshape u
  tssum (D u u') = dD (tssum u) (DeltaSum SNat knownSTK u')
  tssum0 (D u u') = dD (tssum0 u) (DeltaSum0S u')
  tsdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (tsdot0 u v) (dAdd (DeltaDot0S v u') (DeltaDot0S u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
  tsmatvecmul m v = tssum (str (tsreplicate SNat knownShS v * m))
  tsmatmul2 m1 m2 =
    tssum (tstranspose (Permutation.makePerm @'[2, 1, 0])
                       (tsreplicate SNat knownShS m1)
           * tstranspose (Permutation.makePerm @'[1, 0])
                         (tsreplicate SNat knownShS m2))
  tsindex (D u u') i =
    let !ix = tshare . tprimalPart <$> i
    in dD (tsindex u ix) (DeltaIndexS knownShS u' ix)
  tsscatter @shm @shn @shp (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (tsscatter @_ @shm @shn @shp u g)
          (DeltaScatterS @shm @shn @shp knownShS knownShS knownShS u' g)
  tsgather @shm @shn @shp (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (tsgather @_ @shm @shn @shp u g)
          (DeltaGatherS @shm @shn @shp knownShS knownShS knownShS u' g)
  tsconcrete a =
    let v = tsconcrete a
    in fromPrimalFTK (FTKS (Nested.sshape a) FTKScalar) v
  tsfloor (D u _) =
    let v = tsfloor u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  tsfromIntegral (D u _) =
    let v = tsfromIntegral u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  tscast (D u u') = dD (tscast u) (DeltaCastS u')
  tsminIndex (D u _) =
    let v = tsminIndex u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  tsmaxIndex (D u _) =
    let v = tsmaxIndex u
    in fromPrimalFTK (FTKS (sshape v) FTKScalar) v
  tsiota = fromPrimalFTK (FTKS (SNat :$$ ZSS) FTKScalar) tsiota
  tsappend (D u u') (D v v') = dD (tsappend u v) (DeltaAppendS u' v')
  tsslice i n k (D u u') = dD (tsslice i n k u) (DeltaSliceS i n k u')
  tsreverse (D u u') = dD (tsreverse u) (DeltaReverseS u')
  tsbuild1 @k @sh @r f | Dict <- eltDictRep (knownSTK @r) =
    let l = [0 .. valueOf @k - 1]
    in if null l
       then let arr = Nested.semptyArray @(RepConcrete r) (knownShS @sh)
            in gcastWith (unsafeCoerceRefl :: k :~: 0) $
               tconcrete (tftkG knownSTK arr) (Concrete arr)
       else tsfromVector $ V.fromList $ map (f . fromInteger) l
              -- hope this fuses

  -- Mixed ops
  xshape (D u _) = xshape u
  txsum (D u u') = dD (txsum u) (DeltaSum SNat knownSTK u')
  txsum0 (D u u') = dD (txsum0 u) (DeltaSum0X u')
  txdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (txdot0 u v) (dAdd (DeltaDot0X v u') (DeltaDot0X u v'))
  -- These two are manually vectorized to avoid delta blowup when run
  -- via primitive pipelines.
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
  txmatmul2 m1 m2 =
    txsum (txtranspose (Permutation.makePerm @'[2, 1, 0])
                       (txreplicate SNat knownShX m1)
           * txtranspose (Permutation.makePerm @'[1, 0])
                         (txreplicate SNat knownShX m2))
  txreplicate snat sh (D u u') =
    dD (txreplicate snat sh u) (DeltaReplicate snat (STKX sh knownSTK) u')
  txindex (D u u') i =
    let !ix = tshare . tprimalPart <$> i
    in dD (txindex u ix) (DeltaIndexX knownShX u' ix)
  txscatter @shm @shn @shp sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (txscatter @_ @shm @shn @shp sh u g)
          (DeltaScatterX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  txgather @shm @shn @shp sh (D u u') f =
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (txgather @_ @shm @shn @shp sh u g)
          (DeltaGatherX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  txconcrete a =
    let v = txconcrete a
    in fromPrimalFTK (FTKX (Nested.mshape a) FTKScalar) v
  txfloor (D u _) =
    let v = txfloor u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  txfromIntegral (D u _) =
    let v = txfromIntegral u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  txcast (D u u') = dD (txcast u) (DeltaCastX u')
  txminIndex (D u _) =
    let v = txminIndex u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  txmaxIndex (D u _) =
    let v = txmaxIndex u
    in fromPrimalFTK (FTKX (xshape v) FTKScalar) v
  txiota = fromPrimalFTK (FTKX (Nested.SKnown SNat :$% ZSX) FTKScalar) txiota
  txappend (D u u') (D v v') = dD (txappend u v) (DeltaAppendX u' v')
  txslice i n k (D u u') = dD (txslice i n k u) (DeltaSliceX i n k u')
  txreverse (D u u') = dD (txreverse u) (DeltaReverseX u')
  txtranspose perm (D u u') =
    dD (txtranspose perm u) (DeltaTransposeX @_ @_ @_ @target perm u')
  txreshape sh (D u u') = dD (txreshape sh u) (DeltaReshapeX sh u')
  txbuild1 @k @sh @r f =
    let l = [0 .. valueOf @k - 1]
    in if null l
       then case testEquality (knownShX @sh) ZKX of
         Just Refl | Dict <- eltDictRep (knownSTK @r) ->
           let arr = Nested.memptyArray @(RepConcrete r) ZSX
           in gcastWith (unsafeCoerceRefl :: k :~: 0) $
              tconcrete (tftkG knownSTK arr) (Concrete arr)
         Nothing -> error "xbuild1: shape ambiguity"
       else txfromVector $ V.fromList $ map (f . fromInteger) l
              -- hope this fuses

  -- Scalar ops
  tkconcrete a =
    let v = tkconcrete a
    in fromPrimalFTK FTKScalar v
  tkfloor (D u _) =
    let v = tkfloor u
    in fromPrimalFTK FTKScalar v
  tkfromIntegral (D u _) =
    let v = tkfromIntegral u
    in fromPrimalFTK FTKScalar v
  tkcast (D u u') = dD (tkcast u) (DeltaCastK u')

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk (D _ u') = ftkDelta u'
  tconcrete ftk t | Dict <- lemKnownSTK (ftkToSTK ftk) =
    fromPrimalFTK ftk $ tconcrete ftk t
  tpair (D u u') (D v v') = dDnotShared (tpair u v) (DeltaPair u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unDeltaPairUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unDeltaPairUnshared u')
  tsreplicate snat sh (D u u') =
    dD (tsreplicate snat sh u) (DeltaReplicate snat (STKS sh knownSTK) u')
  tstranspose perm (D u u') =
    dD (tstranspose perm u) (DeltaTransposeS @_ @_ @_ @target perm u')
  tsreshape sh (D u u') = dD (tsreshape sh u) (DeltaReshapeS sh u')
  tmapAccumRDer @accy @by @ey _ !k accftk bftk eftk f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (ftkToSTK accftk)
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eftk) =
    let !(D acc0 acc0') = acc0D in
    let !(D esNotShared es') = esD in
    let !es = tshare esNotShared
        codomainShs = FTKProduct accftk bftk
        g :: forall f. ADReady f
          => f (TKProduct accy ey)
          -> f (TKProduct accy (TKProduct accy by))
        g !acc_e =
          ttlet acc_e $ \ !acc_e1 ->
          ttlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accy ey))
                           (TKProduct accy ey))
           -> f (ADTensorKind (TKProduct accy (TKProduct accy by)))
        dg !dacc_de_acc_e =
          ttlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in ttlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accy
                                         (TKProduct accy by)))
                           (TKProduct accy ey))
           -> f (ADTensorKind (TKProduct accy ey))
        rg !args =
          ttlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in ttlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in ttlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in ttlet (unHFun rf (tpair dx_dbRes acc_e))
                   $ \ !daccRes_deRes ->
                  let added = taddTarget (adSTK $ ftkToSTK accftk)
                                         (tproject1 daccRes_deRes)
                                         (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = tmapAccumRDer (Proxy @target)
                          k accftk codomainShs eftk
                          (tlambda @target (FTKProduct accftk eftk)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accftk eftk))
                                         (FTKProduct accftk eftk))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accftk codomainShs))
                                         (FTKProduct accftk eftk))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumR k bftk eftk q es df rf acc0' es'
    in dD (tpair accFin bs) dual
  tmapAccumLDer @accy @by @ey _ !k accftk bftk eftk f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (ftkToSTK accftk)
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eftk) =
    let !(D acc0 acc0') = acc0D in
    let !(D esNotShared es') = esD in
    let !es = tshare esNotShared
        codomainShs = FTKProduct accftk bftk
        g :: forall f. ADReady f
          => f (TKProduct accy ey)
          -> f (TKProduct accy (TKProduct accy by))
        g !acc_e =
          ttlet acc_e $ \ !acc_e1 ->
          ttlet (unHFun f acc_e) $ \ !accRes_bRes ->
            tpair (tproject1 accRes_bRes)
                  (tpair (tproject1 acc_e1) (tproject2 accRes_bRes))
        dg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accy ey))
                           (TKProduct accy ey))
           -> f (ADTensorKind (TKProduct accy (TKProduct accy by)))
        dg !dacc_de_acc_e =
          ttlet dacc_de_acc_e $ \ !dacc_de_acc_e1 ->
            let (!dacc_de, !_acc_e) =
                  (tproject1 dacc_de_acc_e1, tproject2 dacc_de_acc_e1)
                !dacc1 = tproject1 dacc_de
            in ttlet (unHFun df dacc_de_acc_e) $ \ !accRes_bRes ->
                 tpair (tproject1 accRes_bRes)
                       (tpair dacc1 (tproject2 accRes_bRes))
        rg :: forall f. ADReady f
           => f (TKProduct (ADTensorKind (TKProduct accy
                                         (TKProduct accy by)))
                           (TKProduct accy ey))
           -> f (ADTensorKind (TKProduct accy ey))
        rg !args =
          ttlet args $ \ args1 ->
            let (!dx_db, !acc_e) = (tproject1 args1, tproject2 args1)
            in ttlet dx_db $ \ !dx_db1 ->
              let (!dx, !db) = (tproject1 dx_db1, tproject2 dx_db1)
              in ttlet db $ \ !db1 ->
                let dx_dbRes = tpair dx (tproject2 db1)
                in ttlet (unHFun rf (tpair dx_dbRes acc_e))
                   $ \ !daccRes_deRes ->
                  let added = taddTarget (adSTK $ ftkToSTK accftk)
                                         (tproject1 daccRes_deRes)
                                         (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = tmapAccumLDer (Proxy @target)
                          k accftk codomainShs eftk
                          (tlambda @target (FTKProduct accftk eftk)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accftk eftk))
                                         (FTKProduct accftk eftk))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (adFTK (FTKProduct accftk codomainShs))
                                         (FTKProduct accftk eftk))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumL k bftk eftk q es df rf acc0' es'
    in dD (tpair accFin bs) dual
  tApply (HFun f) = f
  tlambda _ = id
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v =
    let uv = tfromVector (SNat @2) stk (V.fromList [u, v])
    in tindexBuild (SNat @2) stk uv (tcond knownSTK b 0 1)
  tprimalPart (D u _) = u
  tdualPart _stk (D _ u') = u'
  tfromPrimal stk t = fromPrimalFTK (tftk stk t) t
  tfromDual t = dDnotShared (tdefTarget (ftkDelta t)) t
  tScale _stk = dScale
  tgrad @x xftk h =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = ttlet a $ \ !aShared ->
          tunshare $ fst $ crevOnParams
                             Nothing
                             (unHFun h @(ADVal (ShareOf f)))
                             xftk
                             (toShare aShared)
    in HFun rf
  tvjp @x @z xftk h =
    let rf :: forall f. ADReady f
           => f (TKProduct (ADTensorKind z) x)
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new db and a.
        rf !db_a = ttlet db_a $ \ !db_aShared ->
          tunshare $ fst $ crevOnParams
                             (Just $ toShare $ tproject1 db_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             xftk
                             (toShare $ tproject2 db_aShared)
    in HFun rf
  tjvp @x @z xftk h =
    let df :: forall f. ADReady f
           => f (TKProduct (ADTensorKind x) x)
           -> f (ADTensorKind z)
        -- This computes the derivative of g again for each new da and a.
        df !da_a = ttlet da_a $ \ !da_aShared ->
          tunshare $ fst $ cfwdOnParams
                             xftk
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df

  tfromVector snat stk lu =
    dD (tfromVector snat stk $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector snat stk $ V.map (\(D _ u') -> u') lu)

  treplTarget r ftk = dDnotShared (treplTarget r ftk) (DeltaZero ftk)
  tdefTarget ftk = dDnotShared (tdefTarget ftk) (DeltaZero ftk)
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => ConvertTensor (ADVal target) where
  rzip (D u u') = dD (rzip u) (DeltaZipR u')
  runzip (D u u') = dD (runzip u) (DeltaUnzipR u')
  szip (D u u') = dD (szip u) (DeltaZipS u')
  sunzip (D u u') = dD (sunzip u) (DeltaUnzipS u')
  xzip (D u u') = dD (xzip u) (DeltaZipX u')
  xunzip (D u u') = dD (xunzip u) (DeltaUnzipX u')

  -- This avoid product eta-expansions for AST instance primal,
  -- though the contangent expands anyway.
  tfromS zstk (D u u') =
    dDnotShared (tfromS zstk u) (dFromS zstk u')
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

  tpairConv = tpair
  tunpairConv = tunpair
