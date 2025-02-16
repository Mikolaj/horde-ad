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

import Control.Exception.Assert.Sugar
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)

import Data.Array.Mixed.Shape (ssxAppend, withKnownShX, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  ( IxR (..)
  , IxS (..)
  , IxX (..)
  , StaticShX(..)
  , ShX (..)
  , ShS (..)
  , KnownShS (..)
  , KnownShX (..)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shsInit, shCvtSX, withKnownShS, shsAppend)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Mixed.Permutation qualified as Permutation

import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Unwind
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Either (STensorKind z) (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullTensorKind x -> ADVal target x
  -> (target (ADTensorKind x), target z)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f xftk inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(D v delta) = f inputs in
  let oneAtF zstk = constantTarget 1 $ adFTK $ tftk zstk v
      dt = either oneAtF id mdt
      !gradient = gradientFromDelta xftk dt delta
  in (gradient, v)

crevOnHVector
  :: forall x z target. (ADReadyNoLet target, ShareTensor target)
  => Either (STensorKind z) (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> FullTensorKind x -> target x
  -> (target (ADTensorKind x), target z)
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
{-# INLINE cfwdOnADInputs #-}
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
cfwdOnHVector xftk parameters f ds =
  let deltaInputs = generateDeltaInputs xftk
      inputs = dDnotShared parameters deltaInputs
  in cfwdOnADInputs xftk inputs f ds


-- * Instances

-- This instance can be sped up by defining and simplifying all default
-- methods (or only tfromVector?), but it probably benefits only product
-- tensor kinds, which are probably not a bottleneck in realistic examples.
instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => LetTensor (ADVal target) where
  tlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')
  toShare = id
  tunshare = id
  -- This avoids product eta-expansions for AST instance primal,
  -- though contangent expands anyway.
  tfromS ystk zstk (D u u') =
    dDnotShared (tfromSShare ystk zstk u) (dFromS zstk u')
  tD stk t d | Dict <- lemKnownSTK stk = dD t d

instance (ADReadyNoLet target, ShareTensor target)
         => ShareTensor (ADVal target) where
  tshare = id
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unDeltaPair u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)
  tfromSShare ystk zstk (D u u') =
    dDnotShared (tfromSShare ystk zstk u) (dFromS zstk u')

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
  rfromVector lu = withSNat (V.length lu) $ \snat ->
    dD (rfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector snat knownSTK $ V.map (\(D _ u') -> u') lu)
  runravelToList (D u u') =
    let lu = runravelToList u
        f i ui = dD ui (DeltaIndexR SNat u' (fromIntegral i :.: ZIR))
    in imap f lu
  rsum (D u u') = withSNat (rlength u) $ \snat ->
    dD (rsum u) (DeltaSum snat knownSTK u')
  rsum0 (D u u') = dD (rsum0 u) (DeltaSum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (dAdd (DeltaDot0R v u') (DeltaDot0R u v'))
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
  rconcrete a =
    let v = rconcrete a
    in fromPrimalADVal v
  rfloor (D u _) =
    let v = rfloor u
    in fromPrimalADVal v
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in fromPrimalADVal v
  rcast (D u u') = dD (rcast u) (DeltaCastR u')
  rminIndex (D u _) =
    let v = rminIndex u
    in fromPrimalADVal v
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in fromPrimalADVal v
  riota = fromPrimalADVal . riota
  rappend (D u u') (D v v') =
    dD (rappend u v) (DeltaAppendR u' v')
  rslice i n (D u u') = dD (rslice i n u) (DeltaSliceR i n u')
  rreverse (D u u') = dD (rreverse u) (DeltaReverseR u')
  rtranspose perm (D u u') = dD (rtranspose perm u) (DeltaTransposeR perm u')
  rreshape @_ @n @m sh t@(D u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (DeltaReshapeR sh u')
  rzip (D u u') = dD (rzip u) (DeltaZipR u')
  runzip (D u u') = dD (runzip u) (DeltaUnzipR u')
  rbuild1 @r @n k f = case NonEmpty.nonEmpty [0 .. fromIntegral k - 1] of
    Nothing -> case sameNat (Proxy @n) (Proxy @0) of
      Just Refl | Dict <- eltDictRep (knownSTK @r) ->
        rconcrete Nested.remptyArray
      Nothing -> error "rbuild1: shape ambiguity"
    Just l -> rfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Shaped ops
  sfromVector @_ @k lu = assert (length lu == valueOf @k) $
    dD (sfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector (SNat @k) knownSTK $ V.map (\(D _ u') -> u') lu)
  sunravelToList (D u u') =
    let lu = sunravelToList u
        f i ui = dD ui (DeltaIndexS knownShS u' (fromIntegral i :.$ ZIS))
    in imap f lu
  ssum (D u u') = dD (ssum u) (DeltaSum SNat knownSTK u')
  ssum0 (D u u') = dD (ssum0 u) (DeltaSum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (dAdd (DeltaDot0S v u') (DeltaDot0S u v'))
  sreplicate (D u u') = dD (sreplicate u) (DeltaReplicate SNat knownSTK u')
  sindex (D u u') i =
    let ix = tprimalPart <$> i
    in dD (sindex u ix) (DeltaIndexS knownShS u' ix)
  sscatter @r @shm @shn @shp (D u u') f =
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (sscatter @_ @r @shm @shn @shp u g)
          (DeltaScatterS @shm @shn @shp knownShS knownShS knownShS u' g)
  sgather @r @shm @shn @shp (D u u') f =
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (sgather @_ @r @shm @shn @shp u g)
          (DeltaGatherS @shm @shn @shp knownShS knownShS knownShS u' g)
  sconcrete a =
    let v = sconcrete a
    in fromPrimalADVal v
  sfloor (D u _) =
    let v = sfloor u
    in fromPrimalADVal v
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in fromPrimalADVal v
  scast (D u u') = dD (scast u) (DeltaCastS u')
  sminIndex @_ @_ @sh @n (D u _) =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    let v = sminIndex u
    in fromPrimalADVal v
  smaxIndex @_ @_ @sh @n (D u _) =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    let v = smaxIndex u
    in fromPrimalADVal v
  siota = fromPrimalADVal siota
  sappend (D u u') (D v v') =
    dD (sappend u v) (DeltaAppendS u' v')
  sslice @_ @i i_proxy n_proxy (D u u') =
    dD (sslice i_proxy n_proxy u) (DeltaSliceS @i SNat SNat SNat u')
  sreverse (D u u') = dD (sreverse u) (DeltaReverseS u')

  sreshape @_ @sh @sh2 t@(D u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (DeltaReshapeS knownShS u')
  szip (D u u') = dD (szip u) (DeltaZipS u')
  sunzip (D u u') = dD (sunzip u) (DeltaUnzipS u')
  sbuild1 @k @_ @r f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
    Nothing | Dict <- eltDictRep (knownSTK @r) ->
      gcastWith (unsafeCoerceRefl :: k :~: 0) $
      sconcrete $ Nested.semptyArray knownShS
    Just l -> sfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Mixed ops
  xshape (D u _) = xshape u
  xfromVector @_ @k lu = assert (length lu == valueOf @k) $  -- TODO: Move these assertions to the base instances, that is concrete and AST
    dD (xfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector (SNat @k) knownSTK $ V.map (\(D _ u') -> u') lu)
  xunravelToList (D u u') =
    let lu = xunravelToList u
        f i ui = dD ui (DeltaIndexX knownShX u' (fromIntegral i :.% ZIX))
    in imap f lu
  xsum (D u u') = dD (xsum u) (DeltaSum SNat knownSTK u')
  xsum0 (D u u') = dD (xsum0 u) (DeltaSum0X u')
  xdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (xdot0 u v) (dAdd (DeltaDot0X v u') (DeltaDot0X u v'))
  xreplicate (D u u') = dD (xreplicate u) (DeltaReplicate SNat knownSTK u')
  xindex (D u u') i =
    let ix = tprimalPart <$> i
    in dD (xindex u ix) (DeltaIndexX knownShX u' ix)
  xscatter @r @shm @shn @shp sh (D u u') f =
    withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
    withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (xscatter @_ @r @shm @shn @shp sh u g)
          (DeltaScatterX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  xgather @r @shm @shn @shp sh (D u u') f =
    withKnownShX (ssxFromShape sh) $
    withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
    let g x = tprimalPart <$> f (tfromPrimal STKScalar <$> x)
    in dD (xgather @_ @r @shm @shn @shp sh u g)
          (DeltaGatherX @shm @shn @shp knownShX knownShX knownShX sh u' g)
  xconcrete a =
    let v = xconcrete a
    in fromPrimalADVal v
  xfloor (D u _) =
    let v = xfloor u
    in fromPrimalADVal v
  xfromIntegral (D u _) =
    let v = xfromIntegral u
    in fromPrimalADVal v
  xcast (D u u') = dD (xcast u) (DeltaCastX u')
  xminIndex (D u _) =
    let v = xminIndex u
    in fromPrimalADVal v
  xmaxIndex (D u _) =
    let v = xmaxIndex u
    in fromPrimalADVal v
  xiota = fromPrimalADVal xiota
  xappend (D u u') (D v v') =
    dD (xappend u v) (DeltaAppendX u' v')
  xslice @_ @i i_proxy n_proxy (D u u') =
    dD (xslice i_proxy n_proxy u) (DeltaSliceX @i SNat SNat SNat u')
  xreverse (D u u') = withKnownShX (ssxFromShape $ xshape u) $
                      dD (xreverse u) (DeltaReverseX u')
  xtranspose @perm @_ @sh (D u u') =
    withKnownShX (ssxPermutePrefix (Permutation.makePerm @perm) (knownShX @sh)) $
    dD (xtranspose @_ @perm u) (DeltaTransposeX @_ @_ @_ @target (Permutation.makePerm @perm) u')
  xreshape @_ @sh sh t@(D u u') =
   case testEquality (knownShX @sh) (ssxFromShape sh) of
    Just Refl | sh == xshape u -> t
    _ -> dD (xreshape sh u) (DeltaReshapeX sh u')
  xzip (D u u') = dD (xzip u) (DeltaZipX u')
  xunzip (D u u') = dD (xunzip u) (DeltaUnzipX u')
  xbuild1 @k @sh @r f = case NonEmpty.nonEmpty [0 .. valueOf @k - 1] of
    Nothing -> case testEquality (knownShX @sh) ZKX of
      Just Refl | Dict <- eltDictRep (knownSTK @r) ->
        gcastWith (unsafeCoerceRefl :: k :~: 0) $
        xconcrete $ Nested.memptyArray ZSX
      Nothing -> error "xbuild1: shape ambiguity"
    Just l -> xfromList $ NonEmpty.map (f . fromInteger) l  -- hope this fuses

  -- Scalar ops
  kconcrete a =
    let v = kconcrete a
    in fromPrimalADVal v
  kfloor (D u _) =
    let v = kfloor u
    in fromPrimalADVal v
  kfromIntegral (D u _) =
    let v = kfromIntegral u
    in fromPrimalADVal v
  kcast (D u u') = dD (kcast u) (DeltaCastK u')

  -- Conversions
  sfromK (D t d) = dDnotShared (sfromK t) (DeltaSFromK d)
  sfromR (D u u') = dDnotShared (sfromR u) (dSFromR knownShS u')
  sfromX (D u u') = dDnotShared (sfromX u) (dSFromX knownShS u')

  -- Nesting/unnesting
  xnestR @_ @m sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    dD (xnestR sh1 u) (DeltaXNestR knownShX SNat u')
  xnestS @_ @sh2 sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    dD (xnestS sh1 u) (DeltaXNestS knownShX knownShS u')
  xnest @_ @sh2 sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` knownShX @sh2) $
    dD (xnest sh1 u) (DeltaXNest knownShX knownShX u')
  xunNestR @sh1 @m (D u u') =
    withKnownShX (knownShX @sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    dD (xunNestR u) (DeltaXUnNestR u')
  xunNestS @sh1 @sh2 (D u u') =
    withKnownShX (knownShX @sh1
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    dD (xunNestS u) (DeltaXUnNestS u')
  xunNest @sh1 @sh2 (D u u') =
    withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
    dD (xunNest u) (DeltaXUnNest u')

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk (D u _) = tftk stk u
  tconcrete ftk t | Dict <- lemKnownSTK (ftkToSTK ftk) =
    fromPrimalADVal $ tconcrete ftk t
  tpair (D u u') (D v v') = dDnotShared (tpair u v) (DeltaPair u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unDeltaPairUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unDeltaPairUnshared u')
  stranspose @perm = ttranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  ttranspose perm (D u u') =
    dD (ttranspose perm u) (DeltaTransposeS @_ @_ @_ @target perm u')
  tmapAccumRDer @accShs @bShs @eShs
                _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs) =
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
                  let added = addTarget knownSTK (tproject1 daccRes_deRes)
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
  tmapAccumLDer @accShs @bShs @eShs
                _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemKnownSTKOfBuild k (knownSTK @accShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @bShs)
   , Dict <- lemKnownSTKOfBuild k (knownSTK @eShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @accShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @bShs)
   , Dict <- lemKnownSTKOfAD (knownSTK @eShs) =
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
                  let added = addTarget knownSTK (tproject1 daccRes_deRes)
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
  tApply _ (HFun f) = f
  tlambda _ = id
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v =
    let uv = tfromVectorShare (SNat @2) stk (V.fromList [u, v])
    in tindexBuildShare (SNat @2) stk uv (ifF b 0 1)
  tprimalPart (D u _) = u
  tdualPart _stk (D _ u') = u'
  tfromPrimal stk t | Dict <- lemKnownSTK stk = fromPrimalADVal t
  tfromDual t = dDnotShared (constantTarget 0 (ftkDelta t)) t
  tScale stk k = withKnownSTK stk $ dScale k
  trev @x xftk h zstk =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = tlet a $ \ !aShared ->
          tunshare $ fst $ crevOnHVector
                             (Left zstk)
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
                             (Right $ toShare $ tproject1 db_aShared)
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
