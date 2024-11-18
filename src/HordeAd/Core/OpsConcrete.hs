{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.OpsConcrete
  () where

import Prelude hiding (foldl')

import Data.Function ((&))
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)
import System.Random

import Data.Array.Nested (KnownShS (..), Rank)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Delta
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX

instance EqF RepN where
  (==.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u ==. RepN v = case stensorKind @y of
    STKScalar _ -> unRepScalar u == unRepScalar v
    STKR SNat STKScalar{} -> u == v
    STKS sh STKScalar{} -> withKnownShS sh $ u == v
    STKX sh STKScalar{} -> withKnownShX sh $ u == v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      RepN (fst u) ==. RepN (fst v) && RepN (snd u) ==. RepN (snd v)
    STKUntyped -> error "TODO"
    _ -> error "TODO"

instance OrdF RepN where
  (<.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u <. RepN v = case stensorKind @y of
    STKScalar _ -> unRepScalar u < unRepScalar v
    STKR SNat STKScalar{} -> u < v
    STKS sh STKScalar{} -> withKnownShS sh $ u < v
    STKX sh STKScalar{} -> withKnownShX sh $ u < v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      RepN (fst u) <. RepN (fst v) && RepN (snd u) <. RepN (snd v)
        -- lexicographic ordering  -- TODO: is this standard and the same as for <=. ? as for || ?
    STKUntyped -> error "TODO"
    _ -> error "TODO"

instance IfF RepN where
  ifF b v w = if b then v else w

instance LetTensor RepN where
  tlet = (&)
  toShare = id
  tunshare = id

instance ShareTensor RepN where
  tshare = id
  tunpair (RepN (t1, t2)) = (RepN t1, RepN t2)
  tunvector = unRepN
  taddShare stk t1 t2 = fromRepD $ addRepD (toRepDShare stk t1)
                                           (toRepDShare stk t2)

instance BaseTensor RepN where
  rmkRepScalar = RepN . RepScalar . unRepN
  runRepScalar = RepN . unRepScalar . unRepN

  rshape = tshapeR . unRepN
  rminIndex = RepN . tminIndexR . unRepN
  rmaxIndex = RepN . tmaxIndexR . unRepN
  rfloor = RepN . tfloorR . unRepN
  rindex v ix = RepN $ tindexZR (unRepN v) (fromIndexOfR $ fmap unRepN $ ix)
  rindex0 v ix = RepN . tscalarR $ tindex0R (unRepN v) (fromIndexOfR $ fmap unRepN $ ix)
  rsum = RepN . tsumR . unRepN
  rsum0 = RepN . tscalarR . tsum0R . unRepN
  rdot0 u v = RepN $ tscalarR $ tdot0R (unRepN u) (unRepN v)
  rmatmul2 m1 m2 = RepN $ tmatmul2R (unRepN m1) (unRepN m2)
  rscatter sh t f = RepN $ tscatterZR sh (unRepN t)
                                         (fromIndexOfR . fmap unRepN . f . fmap RepN . toIndexOfR)
  rscatter1 sh t f = RepN $ tscatterZ1R sh (unRepN t)
                                           (fromIndexOfR . fmap unRepN . f . RepN . tscalarS)
  rfromList = RepN . tfromListR . NonEmpty.map (unRepN)
  rfromList0N sh = RepN . tfromList0NR sh . map (tunScalarR . unRepN)
  rfromVector = RepN . tfromVectorR . V.map (unRepN)
  rfromVector0N sh = RepN . tfromVector0NR sh . V.map (tunScalarR . unRepN)
  runravelToList = map RepN . tunravelToListR . unRepN
  rreplicate k = RepN . treplicateR k . unRepN
  rreplicate0N sh = RepN . treplicate0NR sh . tunScalarR . unRepN
  rappend u v = RepN $ tappendR (unRepN u) (unRepN v)
  rslice i n = RepN . tsliceR i n . unRepN
  rreverse = RepN . treverseR . unRepN
  rtranspose perm = RepN . ttransposeR perm . unRepN
  rreshape sh = RepN . treshapeR sh . unRepN
  rbuild1 k f = RepN $ tbuild1R k (unRepN . f . RepN . tscalarS)
  rmap0N f t = RepN $ tmap0NR (unRepN . f . RepN) (unRepN t)
  rzipWith0N f t u =
    RepN $ tzipWith0NR (\v w -> unRepN $ f (RepN v) (RepN w))
                        (unRepN t) (unRepN u)
  rgather sh t f = RepN $ tgatherZR sh (unRepN t)
                                       (fromIndexOfR . fmap unRepN . f . fmap RepN . toIndexOfR)
  rgather1 k t f = RepN $ tgatherZ1R k (unRepN t)
                                       (fromIndexOfR . fmap unRepN . f . RepN . tscalarS)
  rcast = RepN . tcastR . unRepN
  rfromIntegral = RepN . tfromIntegralR . unRepN
  rconcrete = RepN
  rfromS = RepN . Nested.stoRanked . unRepN

  rscaleByScalar s v =
    RepN $ tscaleByScalarR (tunScalarR $ unRepN s) (unRepN v)
  rdot1In u v = RepN $ tdot1InR (unRepN u) (unRepN v)

  rfromPrimal = id
  rprimalPart = id
  rdualPart _ = DummyDualTarget
  rD u _ = u
  rScale _ _ = DummyDualTarget

  xshape = Nested.mshape . unRepN
  xindex = error "TODO"
  xfromVector = error "TODO"
  xreplicate _ = error "TODO"
  xconcrete = RepN
  xfromPrimal = id
  xprimalPart = id
  xdualPart _ = DummyDualTarget
  xD u _ = u

  sminIndex = RepN . tminIndexS . unRepN
  smaxIndex = RepN . tmaxIndexS . unRepN
  sfloor = RepN . tfloorS . unRepN
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => RepN (TKS '[n] r)  -- from 0 to n - 1
  siota = let n = valueOf @n :: Int
          in RepN $ Nested.sfromList1 SNat
             $ NonEmpty.map fromIntegral $ NonEmpty.fromList [0 .. n - 1]
  sindex v ix = RepN $ tindexZS (unRepN v) (fromIndexOfS $ fmap unRepN $ ix)
  sindex0 v ix = RepN . tscalarS $ tindex0S (unRepN v) (fromIndexOfS $ fmap unRepN $ ix)
  ssum = RepN . tsumS . unRepN
  ssum0 = RepN . tscalarS . tsum0S . unRepN
  sdot0 u v = RepN $ tscalarS $ tdot0S (unRepN u) (unRepN v)
  smatmul2 m1 m2 = RepN $ tmatmul2S (unRepN m1) (unRepN m2)
  sscatter t f = RepN $ tscatterZS (unRepN t)
                                   (fromIndexOfS . fmap unRepN . f . fmap RepN . toIndexOfS)
  sscatter1 t f = RepN $ tscatterZ1S (unRepN t)
                                      (fromIndexOfS . fmap unRepN . f . RepN . tscalarS)
  sfromList = RepN . tfromListS . NonEmpty.map (unRepN)
  sfromList0N = RepN . tfromList0NS . map (tunScalarS . unRepN)
  sfromVector = RepN . tfromVectorS . V.map (unRepN)
  sfromVector0N = RepN . tfromVector0NS . V.map (tunScalarS . unRepN)
  sunravelToList = map RepN . tunravelToListS . unRepN
  sreplicate = RepN . treplicateS . unRepN
  sreplicate0N = RepN . treplicate0NS . tunScalarS . unRepN
  sappend u v = RepN $ tappendS (unRepN u) (unRepN v)
  sslice (_ :: Proxy i) _ = RepN . tsliceS @i . unRepN
  sreverse = RepN . treverseS . unRepN
  stranspose perm = RepN . ttransposeS perm . unRepN
  sreshape = RepN . treshapeS . unRepN
  sbuild1 f = RepN $ tbuild1S (unRepN . f . RepN . tscalarS)
  smap0N f t = RepN $ tmap0NS (unRepN . f . RepN) (unRepN t)
  szipWith0N f t u =
    RepN $ tzipWith0NS (\v w -> unRepN $ f (RepN v) (RepN w))
                        (unRepN t) (unRepN u)
  sgather t f = RepN $ tgatherZS (unRepN t)
                                  (fromIndexOfS . fmap unRepN . f . fmap RepN . toIndexOfS)
  sgather1 t f = RepN $ tgatherZ1S (unRepN t)
                                  (fromIndexOfS . fmap unRepN . f . RepN . tscalarS)
  scast = RepN . tcastS . unRepN
  sfromIntegral = RepN . tfromIntegralS . unRepN
  sconcrete = RepN
  sfromR = RepN . flip Nested.rcastToShaped knownShS . unRepN

  sscaleByScalar s v =
    RepN $ tscaleByScalarS (tunScalarS $ unRepN s) (unRepN v)
  sdot1In proxy u v = RepN $ tdot1InS proxy (unRepN u) (unRepN v)

  sfromPrimal = id
  sprimalPart = id
  sdualPart _ = DummyDualTarget
  sD u _ = u
  sScale _ _ = DummyDualTarget

  tpair u v = RepN (unRepN u, unRepN v)
  tproject1 = RepN . fst . unRepN
  tproject2 = RepN . snd . unRepN
  dshape = voidFromHVector . unRepN
  tshapeFull stk t = case stk of
    STKScalar _ -> FTKScalar
    STKR SNat STKScalar{} -> FTKR $ tshapeR $ unRepN t
    STKS sh STKScalar{} -> FTKS sh
    STKX sh STKScalar{} -> withKnownShX sh $ FTKX $ Nested.mshape $ unRepN t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> FTKUntyped $ voidFromHVector $ tunvector t
    _ -> error "TODO"
  tcond _ b u v = if b then u else v
  tfromPrimal _ t = t
  tprimalPart _ = id
  tdualPart _stk _t = DummyDualTarget
  tD _stk t _d = t
  dmkHVector = RepN
  tlambda _ f x = unRepN $ unHFun f $ RepN x
  tApply f x = RepN $ f $ unRepN x
  dunHVector = unRepN
  dbuild1 k f =
    dmkHVector $ ravelHVector $ map (tunvector . f . fromIntegral) [0 .. sNatValue k - 1]
  -- The code for drevDt and dfwd in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drev :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFunOf RepN x (ADTensorKind x)
  drev _ftk h =
    let rf :: RepORArray x -> RepORArray (ADTensorKind x)
        rf !a = unRepN $ fst $ crevOnHVector Nothing (unHFun h) (RepN a)
    in rf
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> HFunOf RepN (TKProduct (ADTensorKind z) x) (ADTensorKind x)
  drevDt _ftk h =
    let rf :: RepORArray (TKProduct (ADTensorKind z) x) -> RepORArray (ADTensorKind x)
        rf !db_a = unRepN $ fst
                   $ crevOnHVector (Just $ RepN $ fst db_a) (unHFun h) (RepN $ snd db_a)
    in rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFunOf RepN (TKProduct (ADTensorKind x) x) (ADTensorKind z)
  dfwd _shs h =
    let df :: RepORArray (TKProduct (ADTensorKind x) x)
          -> RepORArray (ADTensorKind z)
        df !da_a = unRepN $ fst
                   $ cfwdOnHVector (RepN $ snd da_a) (unHFun h) (RepN $ fst da_a)
    in df
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rscan f x0 as =
    rfromList $ NonEmpty.fromList $ scanl' f x0 (runravelToList as)
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sscan f x0 as =
    sfromList $ NonEmpty.fromList $ scanl' f x0 (sunravelToList as)
  -- The eta-expansion below is needed for typing.
  dmapAccumR _ k accShs bShs eShs f acc0 es =
    oRdmapAccumR k accShs bShs eShs f acc0 es
  dmapAccumRDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumR k accShs bShs eShs (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es
  dmapAccumL _ k accShs bShs eShs f acc0 es =
    oRdmapAccumL k accShs bShs eShs f acc0 es
  dmapAccumLDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumL k accShs bShs eShs (\ !(RepN a) !(RepN b) -> RepN $ f (a, b)) acc0 es

instance Eq (RepORArray y) => Eq (RepN y) where
  RepN u == RepN v = u == v

instance Ord (RepORArray y) => Ord (RepN y) where
  RepN u <= RepN v = u <= v

instance Num (RepORArray y) => Num (RepN y) where
  RepN t + RepN u = RepN $ t + u
  RepN t - RepN u = RepN $ t - u
  RepN t * RepN u = RepN $ t * u
  negate (RepN t) = RepN $ negate t
  abs (RepN t) = RepN $ abs t
  signum (RepN t) = RepN $ signum t
  fromInteger = RepN . fromInteger

instance IntegralF (RepORArray y) => IntegralF (RepN y) where
  quotF (RepN t) (RepN u) = RepN $ quotF t u
  remF (RepN t) (RepN u) = RepN $ remF t u

instance Fractional (RepORArray y) => Fractional (RepN y) where
  RepN u / RepN v = RepN $ u / v
  recip (RepN t) = RepN $ recip t
  fromRational = RepN . fromRational

instance Floating (RepORArray y) => Floating (RepN y) where
  pi = RepN pi
  exp (RepN t) = RepN $ exp t
  log (RepN t) = RepN $ log t
  sqrt (RepN t) = RepN $ sqrt t
  (**) (RepN t) (RepN u) = RepN $ (**) t u
  logBase (RepN t) (RepN u) = RepN $ logBase t u
  sin (RepN t) = RepN $ sin t
  cos (RepN t) = RepN $ cos t
  tan (RepN t) = RepN $ tan t
  asin (RepN t) = RepN $ asin t
  acos (RepN t) = RepN $ acos t
  atan (RepN t) = RepN $ atan t
  sinh (RepN t) = RepN $ sinh t
  cosh (RepN t) = RepN $ cosh t
  tanh (RepN t) = RepN $ tanh t
  asinh (RepN t) = RepN $ asinh t
  acosh (RepN t) = RepN $ acosh t
  atanh (RepN t) = RepN $ atanh t

instance RealFloatF (RepORArray y) => RealFloatF (RepN y) where
  atan2F (RepN t) (RepN u) = RepN $ atan2F t u

ravel :: forall k y. TensorKind y
      => SNat k -> [RepN y]
      -> RepN (BuildTensorKind k y)
ravel k@SNat t = case stensorKind @y of
  STKScalar _ -> rfromList $ NonEmpty.fromList $ runRepScalar <$> t
  STKR SNat STKScalar{} -> rfromList $ NonEmpty.fromList t
  STKS sh STKScalar{} -> withKnownShS sh $ sfromList $ NonEmpty.fromList t
  STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfS stk1
    , Dict <- lemTensorKindOfS stk2
    , Dict <- lemTensorKindOfBuild k (stensorKind @y1)
    , Dict <- lemTensorKindOfBuild k (stensorKind @y2) ->
      let (lt1, lt2) = unzip $ map (\u -> (tproject1 u, tproject2 u)) t
      in tpair (ravel k lt1) (ravel k lt2)
  STKUntyped -> dmkHVector $ ravelHVector $ tunvector <$> t
  _ -> error "TODO"

unravel :: forall k y. TensorKind y
        => SNat k -> RepN (BuildTensorKind k y)
        -> [RepN y]
unravel k@SNat t = case stensorKind @y of
  STKScalar _ -> error "unravel: impossible"
  STKR SNat STKScalar{} -> runravelToList t
  STKS sh STKScalar{} -> withKnownShS sh $ sunravelToList t
  STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfS stk1
    , Dict <- lemTensorKindOfS stk2
    , Dict <- lemTensorKindOfBuild k (stensorKind @y1)
    , Dict <- lemTensorKindOfBuild k (stensorKind @y2) ->
      let lt1 = unravel k $ tproject1 t
          lt2 = unravel k $ tproject2 t
      in zipWith tpair lt1 lt2
  STKUntyped ->
    if V.null $ tunvector t
    then replicate (sNatValue k) $ dmkHVector V.empty
    else dmkHVector <$> unravelHVector (tunvector t)
  _ -> error "TODO"

oRdmapAccumR
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> TensorKindFull accShs
  -> TensorKindFull bShs
  -> TensorKindFull eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumR k _ bShs _ f acc0 es
 | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (repConstant 0 bShs))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumR g acc0 (unravel k es)
    in tpair xout (ravel k lout)
      -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> TensorKindFull accShs
  -> TensorKindFull bShs
  -> TensorKindFull eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumL k _ bShs _ f acc0 es
 | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (repConstant 0 bShs))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumL g acc0 (unravel k es)
    in tpair xout (ravel k lout)

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector RepN (RepN (TKR n r)) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector RepN (RepN (TKR n Double)) #-}
  type X (RepN (TKR n r)) = TKR n r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR n r)) =
    case sameTensorKind @(TKR n r) @(ADTensorKind (TKR n r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero $ rshape aInit, Nothing)

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector RepN (AsHVector (RepN (TKR n r))) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector RepN (AsHVector (RepN (TKR n Double))) #-}
  type X (AsHVector (RepN (TKR n r))) = TKUntyped
  toHVectorOf = RepN . V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance ForgetShape (RepN (TKR n r)) where
  type NoShape (RepN (TKR n r)) = RepN (TKR n r)
  forgetShape = id

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector RepN (RepN (TKS sh r)) where
  type X (RepN (TKS sh r)) = TKS sh r
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS sh r)) =
    case sameTensorKind @(TKS sh r) @(ADTensorKind (TKS sh r)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector RepN (AsHVector (RepN (TKS sh r))) where
  type X (AsHVector (RepN (TKS sh r))) = TKUntyped
  toHVectorOf = RepN . V.singleton . DynamicShaped . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicS (srepl 0) dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance GoodScalar r
         => ForgetShape (RepN (TKS sh r)) where
  type NoShape (RepN (TKS sh r)) = RepN (TKR (Rank sh) r)  -- key case
  forgetShape = RepN . Nested.stoRanked . unRepN

instance (KnownShS sh, GoodScalar r, Fractional r, Random r)
         => RandomHVector (RepN (TKS sh r)) where
  randomVals :: forall g. RandomGen g => Double -> g -> (RepN (TKS sh r), g)
  randomVals range g =
    let createRandomVector :: Int -> g -> Nested.Shaped sh r
        createRandomVector n seed =
          unRepN (srepl (2 * realToFrac range))
          * (Nested.sfromVector knownShS (V.fromListN n (randoms seed))
             - unRepN (srepl 0.5))
        (g1, g2) = split g
        arr = createRandomVector (sizeP (Proxy @sh)) g1
    in (RepN arr, g2)
{-
instance AdaptableHVector RepN (HVector RepN) where
  type X (HVector RepN) = TKUntyped
  toHVectorOf = RepN
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length aInit) $ unRepN params
    in Just (portion, Just $ RepN rest)
-}
-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: TensorKindFull TKUntyped
  -> RepN TKUntyped
  -> Maybe (RepN TKUntyped)
  -> Delta RepN TKUntyped
  -> RepN TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState RepN -> EvalState RepN #-}

instance ADReady target
         => DualNumberValue (DynamicTensor (ADVal target)) where
  type DValue (DynamicTensor (ADVal target)) = DynamicTensor RepN
  fromDValue = \case
    DynamicRanked t -> DynamicRanked $ fromPrimalADVal $ rconcrete $ unRepN t
    DynamicShaped t -> DynamicShaped $ fromPrimalADVal $ sconcrete $ unRepN t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
