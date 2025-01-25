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
  ( unADValRep
  , crevOnADInputs, crevOnHVector, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.List.Index (imap)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape (ssxAppend, withKnownShX, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  ( IxR (..)
  , IxS (..)
  , IxX (..)
  , StaticShX(..)
  , ShX (..)
  , KnownShS (..)
  , KnownShX (..)
  , Rank
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shCvtSX, withKnownShS, shsAppend)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.CarriersADVal
import HordeAd.Core.Delta
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: forall x z target.
     ( TensorKind x, TensorKind z, ADReadyNoLet target
     , ShareTensor target, ShareTensor (PrimalOf target) )
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> ADVal target x
  -> (target (ADTensorKind x), target z)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(!v, !delta) = unADValRep (stensorKind @z) $ f inputs in
  let parameters0 = tftk (stensorKind @x) inputs
      !gradient = gradientFromDelta parameters0 v mdt delta
  in (gradient, v)

crevOnHVector
  :: forall x z target.
     ( TensorKind x, TensorKind z, ADReadyNoLet target
     , ShareTensor target, ShareTensor (PrimalOf target) )
  => Maybe (target (ADTensorKind z))
  -> (ADVal target x -> ADVal target z)
  -> target x
  -> (target (ADTensorKind x), target z)
crevOnHVector mdt f parameters =
  let deltaInputs = generateDeltaInputs
                    $ tftk (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs

cfwdOnADInputs
  :: forall x z target.
     (TensorKind x, TensorKind z, ADReadyNoLet target, ShareTensor target)
  => ADVal target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(!v, !delta) = unADValRep (stensorKind @z) $ f inputs in
  let !derivative = derivativeFromDelta @x delta ds
  in (derivative, v)

cfwdOnHVector
  :: forall x z target.
     (TensorKind x, TensorKind z, ADReadyNoLet target, ShareTensor target)
  => target x
  -> (ADVal target x -> ADVal target z)
  -> target (ADTensorKind x)
  -> (target (ADTensorKind z), target z)
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs
                    $ tftk (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds


-- * Misc instances

-- This instance can be sped up by defining and simplifying all default
-- methods (or only tfromVector?), but it probably benefits only product
-- tensor kinds, which are probably not a bottleneck in realistic examples.
instance ( ADReadyNoLet target, ShareTensor target
         , ShareTensor (PrimalOf target) )
         => LetTensor (ADVal target) where
  tlet :: forall x z. TensorKind x
       => ADVal target x
       -> (ADVal target x -> ADVal target z)
       -> ADVal target z
  tlet (D u u') f =
    let !var2 = tshare u
    in f (dDnotShared var2 u')
  toShare = id
  tunshare = id
  -- This avoids product eta-expansions for AST instance primal,
  -- though contangent expands anyway.
  tfromS (D u u') = dDnotShared (tfromSShare u) (dFromS u')
   where
    -- Avoid building huge Delta terms, not only evaluating them.
    dFromS :: forall y z. (TensorKind y, TensorKind z)
           => Delta target y -> Delta target z
    dFromS (DeltaSFromR @sh @x d)
      | Just Refl <- sameTensorKind @z @(TKR2 (Rank sh) x) = d
    dFromS (DeltaSFromX @_ @sh' @x d)
      | Just Refl <- sameTensorKind @z @(TKX2 sh' x) = d
    dFromS d = DeltaFromS d

instance (ADReadyNoLet target, ShareTensor target)
         => ShareTensor (ADVal target) where
  tshare = id
  tunpair (D u u') = let (u1, u2) = tunpair u
                         (d1, d2) = unDeltaPair u'
                     in (dDnotShared u1 d1, dDnotShared u2 d2)


-- * Base tensor instance

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance (ADReadyNoLet target, ShareTensor target, ShareTensor (PrimalOf target))
         => BaseTensor (ADVal target) where
  rshape (D u _) = rshape u
  rminIndex (D u _) =
    let v = rminIndex u
    in fromPrimalADVal v
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in fromPrimalADVal v
  rfloor (D u _) =
    let v = rfloor u
    in fromPrimalADVal v

  riota = fromPrimalADVal . riota
  -- TODO: speed up by using tindex0R and dDeltaIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dDeltaIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex (D u u') i =
    let ix = tprimalPart (STKScalar typeRep) <$> i
    in dD (rindex u ix) (DeltaIndexR u' ix)
  rsum (D u u') = withSNat (rlength u) $ \snat ->
    dD (rsum u) (DeltaSum snat stensorKind u')
  rsum0 (D u u') = dD (rsum0 u) (DeltaSum0R u')
  rdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (DeltaAdd (DeltaDot0R v u') (DeltaDot0R u v'))
  rscatter sh (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (rscatter sh u g) (DeltaScatterR sh u' g)

  rfromVector lu = withSNat (V.length lu) $ \snat ->
    -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
    dD (rfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector snat stensorKind $ V.map (\(D _ u') -> u') lu)
  runravelToList (D u u') =
    let lu = runravelToList u
        f i ui = dD ui (DeltaIndexR u' (fromIntegral i :.: ZIR))
    in imap f lu
  rreplicate k (D u u') = withSNat k $ \snat ->
    dD (rreplicate k u) (DeltaReplicate snat stensorKind u')
  rappend (D u u') (D v v') =
    dD (rappend u v) (DeltaAppendR u' v')
  rslice i n (D u u') = dD (rslice i n u) (DeltaSliceR i n u')
  rreverse (D u u') = dD (rreverse u) (DeltaReverseR u')
  rtranspose perm (D u u') = dD (rtranspose perm u) (DeltaTransposeR perm u')
  rreshape @_ @n @m sh t@(D u u') = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (DeltaReshapeR sh u')
  rbuild1 @r @n 0 _ = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> case stensorKind @r of
      STKScalar{} -> rconcrete Nested.remptyArray
      _ -> error "rbuild1: empty nested array"
    Nothing -> error "rbuild1: shape ambiguity"
  rbuild1 k f = rfromList $ NonEmpty.map (f . fromIntegral)
                          $ 0 :| [1 .. k - 1]
    -- element-wise (POPL) version
  rgather sh (D u u') f =
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (rgather sh u g) (DeltaGatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D u u') = dD (rcast u) (DeltaCastR u')
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in fromPrimalADVal v
  rzip (D u u') = dD (rzip u) (DeltaZipR u')
  runzip (D u u') = dD (runzip u) (DeltaUnzipR u')
  kfromR @r (D t d) =
    dDnotShared (kfromR t) (DeltaFromS @(TKS '[] r) $ DeltaSFromR d)
  rfromK (D t d) =
    dDnotShared (rfromK t) (DeltaFromS $ DeltaSFromK d)

  rfromPrimal t = fromPrimalADVal t
  rprimalPart (D u _) = u
  rdualPart (D _ u') = u'
  rD t d = dD t d
  rScale k = DeltaScale k

  sminIndex (D u _) =
    let v = sminIndex u
    in fromPrimalADVal v
  smaxIndex (D u _) =
    let v = smaxIndex u
    in fromPrimalADVal v
  sfloor (D u _) =
    let v = sfloor u
    in fromPrimalADVal v

  siota = fromPrimalADVal siota
  sindex (D u u') i =
    let ix = tprimalPart (STKScalar typeRep) <$> i
    in dD (sindex u ix) (DeltaIndexS u' ix)
  ssum (D u u') = dD (ssum u) (DeltaSum SNat stensorKind u')
  ssum0 (D u u') = dD (ssum0 u) (DeltaSum0S u')
  sdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (DeltaAdd (DeltaDot0S v u') (DeltaDot0S u v'))
  sscatter @r @shm @shn @shp (D u u') f =
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (sscatter @_ @r @shm @shn @shp u g) (DeltaScatterS @_ @r @shm @shn @shp u' g)

  sfromVector @_ @k lu = assert (length lu == valueOf @k) $
    dD (sfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector (SNat @k) stensorKind $ V.map (\(D _ u') -> u') lu)
  sunravelToList (D u u') =
    let lu = sunravelToList u
        f i ui = dD ui (DeltaIndexS u' (fromIntegral i :.$ ZIS))
    in imap f lu
  sreplicate (D u u') = dD (sreplicate u) (DeltaReplicate SNat stensorKind u')
  sappend (D u u') (D v v') =
    dD (sappend u v) (DeltaAppendS u' v')
  sslice @_ @i i_proxy n_proxy (D u u') =
    dD (sslice i_proxy n_proxy u) (DeltaSliceS @target @i u')
  sreverse (D u u') = dD (sreverse u) (DeltaReverseS u')

  stranspose @_ @_ @sh perm (D u u') | Dict <- Nested.Internal.Shape.shsKnownShS (Nested.Internal.Shape.shsPermutePrefix perm (knownShS @sh)) =
    dD (stranspose perm u) (DeltaTransposeS @_ @_ @_ @target perm u')
  sreshape @_ @sh @sh2 t@(D u u') = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (DeltaReshapeS u')
  sbuild1 @r @n @sh f = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> case stensorKind @r of
      STKScalar{} ->
        sconcrete $ Nested.semptyArray (knownShS @sh)
      _ -> error "sbuild1: empty nested array"
    Nothing -> sfromList $ NonEmpty.map (f . fromInteger)
                         $ 0 :| [1 .. valueOf @n - 1]
      -- element-wise (POPL) version
  sgather @r @shm @shn @shp (D u u') f =
    withKnownShS (knownShS @shm `shsAppend` knownShS @shn) $
    withKnownShS (knownShS @shp `shsAppend` knownShS @shn) $
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (sgather @_ @r @shm @shn @shp u g) (DeltaGatherS @_ @r @shm @shn @shp u' g)
  scast (D u u') = dD (scast u) (DeltaCastS u')
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in fromPrimalADVal v
  kfromS (D t d) = dDnotShared (kfromS t) (DeltaFromS d)
  sfromK (D t d) = dDnotShared (sfromK t) (DeltaSFromK d)
  szip (D u u') = dD (szip u) (DeltaZipS u')
  sunzip (D u u') = dD (sunzip u) (DeltaUnzipS u')

  sfromPrimal t = fromPrimalADVal t
  sprimalPart (D u _) = u
  sdualPart (D _ u') = u'
  sD t d = dD t d
  sScale k = DeltaScale k

  xminIndex (D u _) =
    let v = xminIndex u
    in fromPrimalADVal v
  xmaxIndex (D u _) =
    let v = xmaxIndex u
    in fromPrimalADVal v
  xfloor (D u _) =
    let v = xfloor u
    in fromPrimalADVal v

  xshape (D u _) = xshape u
  xiota = fromPrimalADVal xiota
  xindex (D u u') i =
    let ix = tprimalPart (STKScalar typeRep) <$> i
    in dD (xindex u ix) (DeltaIndexX u' ix)
  xsum (D u u') = dD (xsum u) (DeltaSum SNat stensorKind u')
  xsum0 (D u u') = dD (xsum0 u) (DeltaSum0X u')
  xdot0 (D ue u') (D ve v') =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (xdot0 u v) (DeltaAdd (DeltaDot0X v u') (DeltaDot0X u v'))
  xscatter @r @shm @shn @shp sh (D u u') f =
    withKnownShX (knownShX @shm `ssxAppend` knownShX @shn) $
    withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (xscatter @_ @r @shm @shn @shp sh u g)
          (DeltaScatterX @_ @r @shm @shn @shp sh u' g)

  xfromVector @_ @k lu = assert (length lu == valueOf @k) $  -- TODO: Move these assertions to the base instances, that is concrete and AST
    dD (xfromVector $ V.map (\(D u _) -> u) lu)
       (DeltaFromVector (SNat @k) stensorKind $ V.map (\(D _ u') -> u') lu)
  xunravelToList (D u u') =
    let lu = xunravelToList u
        f i ui = dD ui (DeltaIndexX u' (fromIntegral i :.% ZIX))
    in imap f lu
  xreplicate (D u u') = dD (xreplicate u) (DeltaReplicate SNat stensorKind u')
  xappend (D u u') (D v v') =
    dD (xappend u v) (DeltaAppendX u' v')
  xslice @_ @i i_proxy n_proxy (D u u') =
    dD (xslice i_proxy n_proxy u) (DeltaSliceX @target @i u')
  xreverse (D u u') = withKnownShX (ssxFromShape $ xshape u) $
                      dD (xreverse u) (DeltaReverseX u')

  xtranspose @_ @_ @sh perm (D u u') =
    withKnownShX (ssxPermutePrefix perm (knownShX @sh)) $
    dD (xtranspose perm u) (DeltaTransposeX @_ @_ @_ @target perm u')
  xreshape @_ @sh sh t@(D u u') =
   case testEquality (knownShX @sh) (ssxFromShape sh) of
    Just Refl | sh == xshape u -> t
    _ -> dD (xreshape sh u) (DeltaReshapeX sh u')
  xbuild1 @r @n @sh f = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> case stensorKind @r of
      STKScalar{} -> case knownShX @sh of
        ZKX -> xconcrete $ Nested.memptyArray ZSX
        _ -> error "xbuild1: empty nested array"
      _ -> error "xbuild1: shape ambiguity"
    Nothing -> xfromList $ NonEmpty.map (f . fromInteger)
                         $ 0 :| [1 .. valueOf @n - 1]
      -- element-wise (POPL) version
  xgather @r @shm @shn @shp sh (D u u') f =
    withKnownShX (ssxFromShape sh) $
    withKnownShX (knownShX @shp `ssxAppend` knownShX @shn) $
    let g x = tprimalPart (STKScalar typeRep)
              <$> f (tfromPrimal (STKScalar typeRep) <$> x)
    in dD (xgather @_ @r @shm @shn @shp sh u g) (DeltaGatherX @_ @r @shm @shn @shp sh u' g)
  xcast (D u u') = dD (xcast u) (DeltaCastX u')
  xfromIntegral (D u _) =
    let v = xfromIntegral u
    in fromPrimalADVal v
  xzip (D u u') = dD (xzip u) (DeltaZipX u')
  xunzip (D u u') = dD (xunzip u) (DeltaUnzipX u')
  kfromX @r (D t d) =
    dDnotShared (kfromX t) (DeltaFromS @(TKS '[] r) $ DeltaSFromX d)
  xfromK (D t d) =
    dDnotShared (xfromK t) (DeltaFromS $ DeltaSFromK d)
  xfromPrimal t = fromPrimalADVal t
  xprimalPart (D u _) = u
  xdualPart (D _ u') = u'
  xD t d = dD t d
  xScale k = DeltaScale k

  kfloor (D u _) =
    let v = kfloor u
    in fromPrimalADVal v
  kcast (D u u') = dD (kcast u) (DeltaCast u')
  kfromIntegral (D u _) =
    let v = kfromIntegral u
    in fromPrimalADVal v

  sfromR @sh @x (D u u') = dDnotShared (sfromR u) (dSFromR u')
   where
    dSFromR (DeltaFromS @y d) =
      case sameTensorKind @y @(TKS2 sh x) of
        Just Refl -> d
        _ -> error "sfromR: different shapes in DeltaSFromR(DeltaFromS)"
    dSFromR d = DeltaSFromR d
  sfromX @sh @_ @x (D u u') = dDnotShared (sfromX u) (dSFromX u')
   where
    dSFromX (DeltaFromS @y d) =
      case sameTensorKind @y @(TKS2 sh x) of
        Just Refl -> d
        _ -> error "sfromR: different shapes in DeltaSFromX(DeltaFromS)"
    dSFromX d = DeltaSFromX d

  xnestR @_ @m sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxReplicate (SNat @m)) $
    dD (xnestR sh1 u) (DeltaXNestR u')
  xnestS @_ @sh2 sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    dD (xnestS sh1 u) (DeltaXNestS u')
  xnest @_ @sh2 sh1 (D u u') =
    withKnownShX sh1 $
    withKnownShX (sh1 `ssxAppend` knownShX @sh2) $
    dD (xnest sh1 u) (DeltaXNest u')

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

  tpair (D u u') (D v v') = dDnotShared (tpair u v) (DeltaPair u' v')
  tproject1 (D u u') = dDnotShared (tproject1 u) (fst $ unDeltaPairUnshared u')
  tproject2 (D u u') = dDnotShared (tproject2 u) (snd $ unDeltaPairUnshared u')
  tftk stk (D u _) = tftk stk u
  -- Bangs are for the proper order of sharing stamps.
  tcond !stk !b !u !v =
    let uv = tfromVector (SNat @2) stk (V.fromList [u, v])
    in tindexBuildShare (SNat @2) stk uv (ifF b 0 1)
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk = fromPrimalADVal t
  tprimalPart _stk (D u _) = u
  tdualPart _stk (D _ u') = u'
  tD stk t d | Dict <- lemTensorKindOfSTK stk = dD t d
  tconcrete ftk t | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    fromPrimalADVal $ tconcrete ftk t
  tlambda _ = id
  tApply (HFun f) = f
  drev @x _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let rf :: forall f. ADReady f
           => f x
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new a.
        rf !a = tlet a $ \ !aShared ->
          tunshare $ fst $ crevOnHVector
                             Nothing
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare aShared)
    in HFun rf
  drevDt @x @z _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x)
                      , Dict <- lemTensorKindOfAD (stensorKind @z) =
    let rf :: forall f. ADReady f
           => f (TKProduct (ADTensorKind z) x)
           -> f (ADTensorKind x)
        -- This computes the derivative of g again for each new db and a.
        rf !db_a = tlet db_a $ \ !db_aShared ->
          tunshare $ fst $ crevOnHVector
                             (Just $ toShare $ tproject1 db_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject2 db_aShared)
    in HFun rf
  dfwd @x @z _ftk h | Dict <- lemTensorKindOfAD (stensorKind @x)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) =
    let df :: forall f. ADReady f
           => f (TKProduct (ADTensorKind x) x)
           -> f (ADTensorKind z)
        -- This computes the derivative of g again for each new da and a.
        df !da_a = tlet da_a $ \ !da_aShared ->
          tunshare $ fst $ cfwdOnHVector
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df
  dmapAccumRDer @accShs @bShs @eShs
                _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs) =
    let (acc0, acc0') = unADValRep stensorKind acc0D
        (esNotShared, es') = unADValRep stensorKind esD
        es = tshare esNotShared
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
                  let added = addTarget stensorKind (tproject1 daccRes_deRes)
                                                    (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumRDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumR k accShs bShs eShs
                              q es
                              df rf acc0' es'
    in dD (tpair accFin bs) dual
  dmapAccumLDer @accShs @bShs @eShs
                _ !k accShs bShs eShs f df rf acc0D esD
   | Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @bShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs) =
    let (acc0, acc0') = unADValRep stensorKind acc0D
        (esNotShared, es') = unADValRep stensorKind esD
        es = tshare esNotShared
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
                  let added = addTarget stensorKind (tproject1 daccRes_deRes)
                                                    (tproject1 db1)
                  in tpair added (tproject2 daccRes_deRes)
        p = dmapAccumLDer (Proxy @target)
                          k accShs codomainShs eShs
                          (tlambda @target (FTKProduct accShs eShs)
                           $ HFun g)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs eShs))
                                         (FTKProduct accShs eShs))
                           $ HFun dg)
                          (tlambda @target
                             (FTKProduct (aDFTK (FTKProduct accShs codomainShs))
                                         (FTKProduct accShs eShs))
                           $ HFun rg)
                          acc0 es
        (accFin, qbs) = tunpair p
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        (q, bs) = tunpair qbs
        dual = DeltaMapAccumL k accShs bShs eShs
                              q es
                              df rf acc0' es'
    in dD (tpair accFin bs) dual

unADValRep
  :: forall y target.
     STensorKindType y
  -> ADVal target y
  -> (target y, Delta target y)
unADValRep _stk (D p d) = (p, d)
