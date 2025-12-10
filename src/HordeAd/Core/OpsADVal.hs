{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. All definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms or anything else (e.g., nested 'ADVal').
module HordeAd.Core.OpsADVal
  ( crevOnADInputs, crevOnParams, crevOnParamsDt, cfwdOnParams
  ) where

import Prelude hiding (foldl')

import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)

import Data.Array.Nested (Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.UnwindNum

-- * Non-symbolic (or at least non-sharing) reverse and forward derivative computation

-- The user-written function f can do anything, so the inputs
-- argument has to be duplicable.
crevOnADInputs
  :: forall x z target.
     (TKAllNum (ADTensorKind z), ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> ADVal target x
  -> (target z, target (ADTensorKind x))
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f xftk inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D v delta) = f inputs in
  let zftk = ftkDelta delta
      dt = fromMaybe (treplTarget 1 $ adFTK zftk) mdt
      !gradient = gradientFromDelta xftk zftk dt delta
  in (v, gradient)

crevOnParams
  :: forall x z target.
     (TKAllNum (ADTensorKind z), ADReadyNoLet target, ShareTensor target)
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> target x
  -> (target z, target (ADTensorKind x))
{-# INLINE crevOnParams #-}
crevOnParams edt f xftk parameters =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in crevOnADInputs edt f xftk inputs

-- These two functions are as above, but the dt must be provided and so,
-- due to technical reasons, the type is less constrained.
-- The user-written function f can do anything, so the inputs
-- argument has to be duplicable.
crevOnADInputsDt
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => target (ADTensorKind z)
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> ADVal target x
  -> (target z, target (ADTensorKind x))
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE crevOnADInputsDt #-}
crevOnADInputsDt dt f xftk inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D v delta) = f inputs in
  let zftk = ftkDelta delta
      !gradient = gradientFromDelta xftk zftk dt delta
  in (v, gradient)

crevOnParamsDt
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => target (ADTensorKind z)
  -> (ADVal target x -> ADVal target z)
  -> FullShapeTK x -> target x
  -> (target z, target (ADTensorKind x))
{-# INLINE crevOnParamsDt #-}
crevOnParamsDt dt f xftk parameters =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in crevOnADInputsDt dt f xftk inputs

cfwdOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK x -> ADVal target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target z, target (ADTensorKind z))
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs xftk inputs f ds =
  let !(D v delta) = f inputs in
  let !derivative = derivativeFromDelta @x delta (adFTK xftk) ds
  in (v, derivative)

cfwdOnParams
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => FullShapeTK x -> target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target z, target (ADTensorKind z))
{-# INLINE cfwdOnParams #-}
cfwdOnParams xftk parameters f ds =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in cfwdOnADInputs xftk inputs f ds


-- * Instances

fromPrimalFTK :: FullShapeTK z -> f z -> ADVal f z
fromPrimalFTK ftk a = dDnotShared a (DeltaZero ftk)

-- TODO: inline all ops that take functions here, in OpsAst and OpsConcrete
-- and benchmark to see if that's a good idea
instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PlainOf target))
         => LetTensor (ADVal target) where
  ttlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')  -- u' was already shared
  ttletPrimal u f =
    let !var2 = tshare u
    in f var2
  ttletPlain u f =
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
         , ShareTensor (PrimalOf target), ShareTensor (PlainOf target) )
         => BaseTensor (ADVal target) where
  rshape (D u _) = rshape u
  sshape (D u _) = sshape u
  xshape (D u _) = xshape u
  tftk _stk (D _ u') = ftkDelta u'
  tpair (D u u') (D v v') = dDnotShared (tpair u v) (DeltaPair u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unDeltaPairUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unDeltaPairUnshared u')
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v =
    let uv = tfromList (SNat @2) stk [u, v]
    in tindexBuild (SNat @2) stk uv (tcond knownSTK b 0 1)
  tkconcrete a =
    let v = tkconcrete a
    in fromPrimalFTK FTKScalar v
  trconcrete a =
    let v = trconcrete a
    in fromPrimalFTK (FTKR (Nested.rshape a) FTKScalar) v
  tsconcrete a =
    let v = tsconcrete a
    in fromPrimalFTK (FTKS (Nested.sshape a) FTKScalar) v
  txconcrete a =
    let v = txconcrete a
    in fromPrimalFTK (FTKX (Nested.mshape a) FTKScalar) v
  tconcrete ftk t | Dict <- lemKnownSTK (ftkToSTK ftk) =
    fromPrimalFTK ftk $ tconcrete ftk t
  tfromVector snat stk lu =
    dD (tfromVector snat stk $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector snat stk $ V.map (\(D _ u') -> u') lu)
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
  tsreplicate snat sh (D u u') =
    dD (tsreplicate snat sh u) (DeltaReplicate snat (STKS sh knownSTK) u')
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
  trindex (D u u') i =
    let !ix = tshare <$> i
    in dD (trindex u ix) (DeltaIndexR SNat u' ix)
  trindex0 (D u u') i =
    let !ix = tshare <$> i
        c = convCmp ConvX0 ConvRX
    in dD (trindex0 u ix) (DeltaConvert c (DeltaIndexR (SNat @0) u' ix))
  trscatter sh (D u u') f =
    dD (trscatter sh u f) (DeltaScatterR SNat SNat SNat sh u' f)
  trgather sh (D u u') f =
    dD (trgather sh u f) (DeltaGatherR SNat SNat SNat sh u' f)
      -- Note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on.
      -- Note also how f is duplicated and this leads to loss of sharing
      -- of indexes in AST instances.
  tsindex (D u u') i =
    let !ix = tshare <$> i
    in dD (tsindex u ix) (DeltaIndexS knownShS u' ix)
  tsindex0 @sh (D u u') i | Refl <- lemAppNil @sh =
    let !ix = tshare <$> i
        c = convCmp ConvX0 ConvSX
    in dD (tsindex0 u ix) (DeltaConvert c (DeltaIndexS ZSS u' ix))
  tsscatter @shm @shn @shp (D u u') f =
    dD (tsscatter @_ @shm @shn @shp u f)
       (DeltaScatterS @shm @shn @shp knownShS knownShS knownShS u' f)
  tsgather @shm @shn @shp (D u u') f =
    dD (tsgather @_ @shm @shn @shp u f)
       (DeltaGatherS @shm @shn @shp knownShS knownShS knownShS u' f)
  txindex (D u u') i =
    let !ix = tshare <$> i
    in dD (txindex u ix) (DeltaIndexX knownShX u' ix)
  txindex0 @sh (D u u') i | Refl <- lemAppNil @sh =
    let !ix = tshare <$> i
        c = ConvX0
    in dD (txindex0 u ix) (DeltaConvert c (DeltaIndexX ZKX u' ix))
  txscatter @shm @shn @shp sh (D u u') f =
    dD (txscatter @_ @shm @shn @shp sh u f)
       (DeltaScatterX @shm @shn @shp knownShX knownShX knownShX sh u' f)
  txgather @shm @shn @shp sh (D u u') f =
    dD (txgather @_ @shm @shn @shp sh u f)
       (DeltaGatherX @shm @shn @shp knownShX knownShX knownShX sh u' f)
  tkfloor (D u _) =
    let v = tkfloor u
    in fromPrimalFTK FTKScalar v
  tkfromIntegral (D u _) =
    let v = tkfromIntegral u
    in fromPrimalFTK FTKScalar v
  tkcast (D u u') = dD (tkcast u) (DeltaCastK u')
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
  trappend (D u u') (D v v') = dD (trappend u v) (DeltaAppendR u' v')
  trslice i n (D u u') = dD (trslice i n u) (DeltaSliceR i n u')
  trreverse (D u u') = dD (trreverse u) (DeltaReverseR u')
  trtranspose perm (D u u') = dD (trtranspose perm u) (DeltaTransposeR perm u')
  trreshape sh (D u u') = dD (trreshape sh u) (DeltaReshapeR sh u')
  tsappend (D u u') (D v v') = dD (tsappend u v) (DeltaAppendS u' v')
  tsslice i n k (D u u') = dD (tsslice i n k u) (DeltaSliceS i n k u')
  tsreverse (D u u') = dD (tsreverse u) (DeltaReverseS u')
  tstranspose perm (D u u') =
    dD (tstranspose perm u) (DeltaTransposeS @_ @_ @_ @target perm u')
  tsreshape sh (D u u') = dD (tsreshape sh u) (DeltaReshapeS sh u')
  txappend (D u u') (D v v') = dD (txappend u v) (DeltaAppendX u' v')
  txslice i n k (D u u') = dD (txslice i n k u) (DeltaSliceX i n k u')
  txreverse (D u u') = dD (txreverse u) (DeltaReverseX u')
  txtranspose perm (D u u') =
    dD (txtranspose perm u) (DeltaTransposeX @_ @_ @_ @target perm u')
  txreshape sh (D u u') = dD (txreshape sh u) (DeltaReshapeX sh u')
  tkbuild1 @k f =
    case SNat @k of
      SNat' @0 ->
        let arr = Nested.semptyArray ZSS
        in tconcrete (FTKS (SNat @0 :$$ ZSS) FTKScalar) (Concrete arr)
      _ ->
        let l = [0 .. valueOf @k - 1]
        in tfromVector SNat STKScalar
           $ V.fromListN (valueOf @k) $ map (f . fromInteger) l
             -- hope this fuses
  trbuild1 @n @x k f =
    if k == 0
    then case sameNat (Proxy @n) (Proxy @0) of
      Just Refl | Dict <- eltDictRep (knownSTK @x) ->
        let arr = Nested.remptyArray
        in tconcrete (tftkG knownSTK arr) (Concrete arr)
      Nothing -> error "rbuild1: shape ambiguity"
    else let l = [0 .. fromIntegral k - 1]
         in trfromVector $ V.fromListN k $ map (f . fromInteger) l
              -- hope this fuses
  tsbuild1 @k @sh @r f | Dict <- eltDictRep (knownSTK @r) =
    case SNat @k of
      SNat' @0 ->
        let arr = Nested.semptyArray @_ @(RepConcrete r) (knownShS @sh)
        in tconcrete (tftkG knownSTK arr) (Concrete arr)
      _ ->
        let l = [0 .. valueOf @k - 1]
        in tsfromVector $ V.fromListN (valueOf @k) $ map (f . fromInteger) l
             -- hope this fuses
  txbuild1 @k @sh @r f =
    case SNat @k of
      SNat' @0 -> case testEquality (knownShX @sh) ZKX of
        Just Refl | Dict <- eltDictRep (knownSTK @r) ->
          let arr = Nested.memptyArray @_ @(RepConcrete r) ZSX
          in tconcrete (tftkG knownSTK arr) (Concrete arr)
        _ -> error "xbuild1: shape ambiguity"
      _ ->
        let l = [0 .. valueOf @k - 1]
        in txfromVector $ V.fromListN (valueOf @k) $ map (f . fromInteger) l
             -- hope this fuses
  tmapAccumRDer @accy @by @ey _ !k accftk bftk eftk f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (ftkToSTK accftk)
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eftk)
   , Dict0 <- lemTKAllNumAD (ftkToSTK accftk) =
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
   , Dict <- lemKnownSTKOfBuild k (ftkToSTK eftk)
   , Dict0 <- lemTKAllNumAD (ftkToSTK accftk) =
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
  tapply (HFun f) = f
  tlambda _ = id
  tgrad @x @r xftk h | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = ttlet a $ \ !aShared ->
          tunshare $ snd $ crevOnParams
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
          tunshare $ snd $ crevOnParamsDt
                             (toShare $ tproject1 db_aShared)
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
          tunshare $ snd $ cfwdOnParams
                             xftk
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df
  tprimalPart (D u _) = u
  tdualPart _stk (D _ u') = u'
  tplainPart (D u _) = tplainPart u
  tfromPrimal stk t = fromPrimalFTK (tftk stk t) t
  tfromDual t = dDnotShared (tdefTarget (ftkDelta t)) t
  tfromPlain stk t = fromPrimalFTK (tftk stk t) (tfromPlain stk t)
  tScale _stk = dScale
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target

instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target), ShareTensor (PlainOf target) )
         => ConvertTensor (ADVal target) where
  tconvert c astk (D u u') =
    dDnotShared (tconvert c astk u)
                (DeltaConvert c u')

  rfromX a@(D _ u') = case ftkDelta u' of
    FTKX sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a@(D _ u') = case ftkDelta u' of
    FTKR shr _ ->
      withShsFromShR shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR knownShS u')
  sfromX (D u u') = dDnotShared (sfromX u) (dSFromX knownShS u')
  xfromS (D u u') = dDnotShared (xfromS u) (dXFromS knownShX u')

  rzip @_ @_ @n (D u u')
   | Refl <- lemRankReplicate (Proxy @n) = case ftkDelta u' of
    ftk@(FTKProduct (FTKR _sh y) (FTKR _ z)) ->
      let c = convCmp
                (ConvXR (ftkToSTK (FTKProduct y z)))
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvRX ConvRX))
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')
  runzip @_ @_ @n (D u u')
   | Refl <- lemRankReplicate (Proxy @n) = case ftkDelta u' of
    ftk@(FTKR _sh (FTKProduct y z)) ->
      let c = convCmp
                (ConvT2 (ConvXR (ftkToSTK y)) (ConvXR (ftkToSTK z)))
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvRX)
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')
  szip (D u u') = case ftkDelta u' of
    ftk@(FTKProduct (FTKS _sh y) (FTKS _ z)) ->
      let c = convCmp
                ConvXS
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvSX ConvSX))
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')
  sunzip (D u u') = case ftkDelta u' of
    ftk@(FTKS _sh (FTKProduct y z)) ->
      let c = convCmp
                (ConvT2 ConvXS ConvXS)
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvSX)
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')
  xzip (D u u') = case ftkDelta u' of
    ftk@(FTKProduct (FTKX _sh y) (FTKX _ z)) ->
      let c = ConvZip (ftkToSTK y) (ftkToSTK z)
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')
  xunzip (D u u') = case ftkDelta u' of
    ftk@(FTKX _sh (FTKProduct y z)) ->
      let c = ConvUnzip (ftkToSTK y) (ftkToSTK z)
      in dD (tconvert c (ftkToSTK ftk) u)
            (DeltaConvert c u')

  xnestR @sh1 @m @x sh1 (D u u')
    | Refl <- lemRankReplicate (Proxy @m) =
      let c :: TKConversion (TKX2 (sh1 ++ Replicate m Nothing) x)
                            (TKX2 sh1 (TKR2 m x))
          c = convCmp
                (ConvXX (ConvXR (knownSTK @x)))
                (ConvNest @_ @_ @(Replicate m Nothing)
                          (STKX sh1 (knownSTK @x)))
      in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
            (DeltaConvert c u')
  xnestS @_ @_ @x sh1 (D u u') =
    let c = convCmp (ConvXX ConvXS)
                    (ConvNest (STKX sh1 (knownSTK @x)))
    in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
          (DeltaConvert c u')
  xnest @_ @_ @x sh1 (D u u') =
    let c = ConvNest (STKX sh1 (knownSTK @x))
    in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
          (DeltaConvert c u')
  xunNestR (D u u') =
    let c = convCmp ConvUnnest
                    (ConvXX ConvRX)
    in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
          (DeltaConvert c u')
  xunNestS (D u u') =
    let c = convCmp ConvUnnest
                   (ConvXX ConvSX)
    in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
          (DeltaConvert c u')
  xunNest (D u u') =
    let c = ConvUnnest
    in dD (tconvert c (ftkToSTK $ ftkDelta u') u)
          (DeltaConvert c u')

  tpairConv = tpair
  tunpairConv = tunpair
