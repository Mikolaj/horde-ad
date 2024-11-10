{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.TensorConcrete
  () where

import Prelude hiding (foldl')

import Data.Array.Internal (valueOf)
import Data.Function ((&))
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)
import System.Random

import Data.Array.Nested (Rank)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX
import HordeAd.Internal.OrthotopeOrphanInstances
  (FlipR (..), FlipS (..), FlipX (..), IntegralF (..), RealFloatF (..))

type instance BoolOf RepN = Bool

instance EqF RepN where
  (==.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u ==. RepN v = case stensorKind @y of
    STKScalar _ -> unRepScalar u == unRepScalar v
    STKR STKScalar{} SNat -> u == v
    STKS STKScalar{} sh -> withKnownShS sh $ u == v
    STKX STKScalar{} sh -> withKnownShX sh $ u == v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      RepN (fst u) ==. RepN (fst v) && RepN (snd u) ==. RepN (snd v)
    STKUntyped -> error "TODO"
    _ -> error "TODO"

instance OrdF RepN where
  (<.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u <. RepN v = case stensorKind @y of
    STKScalar _ -> unRepScalar u < unRepScalar v
    STKR STKScalar{} SNat -> u < v
    STKS STKScalar{} sh -> withKnownShS sh $ u < v
    STKX STKScalar{} sh -> withKnownShX sh $ u < v
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      RepN (fst u) <. RepN (fst v) && RepN (snd u) <. RepN (snd v)
        -- lexicographic ordering  -- TODO: is this standard and the same as for <=. ? as for || ?
    STKUntyped -> error "TODO"
    _ -> error "TODO"

instance IfF RepN where
  ifF b v w = if b then v else w

type instance HFunOf RepN x z = RepORArray x -> RepORArray z

type instance PrimalOf RepN = RepN

type instance DualOf RepN = DummyDualTarget

type instance ShareOf RepN = RepN

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

  rshape = tshapeR . runFlipR . unRepN
  rminIndex = RepN . FlipR . tminIndexR . runFlipR . unRepN
  rmaxIndex = RepN . FlipR . tmaxIndexR . runFlipR . unRepN
  rfloor = RepN . FlipR . tfloorR . runFlipR . unRepN
  rindex v ix = RepN $ FlipR $ tindexZR (runFlipR $ unRepN v) (fromIndexOfR $ fmap unRepN $ ix)
  rindex0 v ix = RepN . FlipR . tscalarR $ tindex0R (runFlipR $ unRepN v) (fromIndexOfR $ fmap unRepN $ ix)
  rsum = RepN . FlipR . tsumR . runFlipR . unRepN
  rsum0 = RepN . FlipR . tscalarR . tsum0R . runFlipR . unRepN
  rdot0 u v = RepN $ FlipR $ tscalarR $ tdot0R (runFlipR $ unRepN u) (runFlipR $ unRepN v)
  rmatmul2 m1 m2 = RepN $ FlipR $ tmatmul2R (runFlipR $ unRepN m1) (runFlipR $ unRepN m2)
  rscatter sh t f = RepN $ FlipR $ tscatterZR sh (runFlipR $ unRepN t)
                                         (fromIndexOfR . fmap unRepN . f . fmap RepN . toIndexOfR)
  rscatter1 sh t f = RepN $ FlipR $ tscatterZ1R sh (runFlipR $ unRepN t)
                                           (fromIndexOfR . fmap unRepN . f . RepN . FlipR . tscalarR)
  rfromList = RepN . FlipR . tfromListR . NonEmpty.map (runFlipR . unRepN)
  rfromList0N sh = RepN . FlipR . tfromList0NR sh . map (tunScalarR . runFlipR . unRepN)
  rfromVector = RepN . FlipR . tfromVectorR . V.map (runFlipR . unRepN)
  rfromVector0N sh = RepN . FlipR . tfromVector0NR sh . V.map (tunScalarR . runFlipR . unRepN)
  runravelToList = map (RepN . FlipR) . tunravelToListR . runFlipR . unRepN
  rreplicate k = RepN . FlipR . treplicateR k . runFlipR . unRepN
  rreplicate0N sh = RepN . FlipR . treplicate0NR sh . tunScalarR . runFlipR . unRepN
  rappend u v = RepN $ FlipR $ tappendR (runFlipR $ unRepN u) (runFlipR $ unRepN v)
  rslice i n = RepN . FlipR . tsliceR i n . runFlipR . unRepN
  rreverse = RepN . FlipR . treverseR . runFlipR . unRepN
  rtranspose perm = RepN . FlipR . ttransposeR perm . runFlipR . unRepN
  rreshape sh = RepN . FlipR . treshapeR sh . runFlipR . unRepN
  rbuild1 k f = RepN $ FlipR $ tbuild1R k (runFlipR . unRepN . f . RepN . FlipR . tscalarR)
  rmap0N f t = RepN $ FlipR $ tmap0NR (runFlipR . unRepN . f . RepN . FlipR) (runFlipR $ unRepN t)
  rzipWith0N f t u =
    RepN $ FlipR $ tzipWith0NR (\v w -> runFlipR $ unRepN $ f (RepN $ FlipR v) (RepN $ FlipR w))
                        (runFlipR $ unRepN t) (runFlipR $ unRepN u)
  rgather sh t f = RepN $ FlipR $ tgatherZR sh (runFlipR $ unRepN t)
                                       (fromIndexOfR . fmap unRepN . f . fmap RepN . toIndexOfR)
  rgather1 k t f = RepN $ FlipR $ tgatherZ1R k (runFlipR $ unRepN t)
                                       (fromIndexOfR . fmap unRepN . f . RepN . FlipR . tscalarR)
  rcast = RepN . FlipR . tcastR . runFlipR . unRepN
  rfromIntegral = RepN . FlipR . tfromIntegralR . runFlipR . unRepN
  rconst = RepN . FlipR
  rfromS = RepN . FlipR . Nested.stoRanked . runFlipS . unRepN

  rscaleByScalar s v =
    RepN $ FlipR $ tscaleByScalarR (tunScalarR $ runFlipR $ unRepN s) (runFlipR $ unRepN v)
  rdot1In u v = RepN $ FlipR $ tdot1InR (runFlipR $ unRepN u) (runFlipR $ unRepN v)

  rconstant = id
  rprimalPart = id
  rdualPart _ = DummyDualTarget
  rD u _ = u
  rScale _ _ = DummyDualTarget

  xshape = Nested.mshape . runFlipX . unRepN
  xindex = error "TODO"
  xfromVector = error "TODO"
  xreplicate _ = error "TODO"
  xconst = RepN . FlipX
  xconstant = id
  xprimalPart = id
  xdualPart _ = DummyDualTarget
  xD u _ = u

  sminIndex = RepN . FlipS . tminIndexS . runFlipS . unRepN
  smaxIndex = RepN . FlipS . tmaxIndexS . runFlipS . unRepN
  sfloor = RepN . FlipS . tfloorS . runFlipS . unRepN
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => RepN (TKS r '[n])  -- from 0 to n - 1
  siota = let n = valueOf @n :: Int
          in RepN $ FlipS $ Nested.sfromList1 SNat
             $ NonEmpty.map fromIntegral $ NonEmpty.fromList [0 .. n - 1]
  sindex v ix = RepN $ FlipS $ tindexZS (runFlipS $ unRepN v) (fromIndexOfS $ fmap unRepN $ ix)
  sindex0 v ix = RepN . FlipS . tscalarS $ tindex0S (runFlipS $ unRepN v) (fromIndexOfS $ fmap unRepN $ ix)
  ssum = RepN . FlipS . tsumS . runFlipS . unRepN
  ssum0 = RepN . FlipS . tscalarS . tsum0S . runFlipS . unRepN
  sdot0 u v = RepN $ FlipS $ tscalarS $ tdot0S (runFlipS $ unRepN u) (runFlipS $ unRepN v)
  smatmul2 m1 m2 = RepN $ FlipS $ tmatmul2S (runFlipS $ unRepN m1) (runFlipS $ unRepN m2)
  sscatter t f = RepN $ FlipS $ tscatterZS (runFlipS $ unRepN t)
                                   (fromIndexOfS . fmap unRepN . f . fmap RepN . toIndexOfS)
  sscatter1 t f = RepN $ FlipS $ tscatterZ1S (runFlipS $ unRepN t)
                                      (fromIndexOfS . fmap unRepN . f . RepN . FlipR . tscalarR)
  sfromList = RepN . FlipS . tfromListS . NonEmpty.map (runFlipS . unRepN)
  sfromList0N = RepN . FlipS . tfromList0NS . map (tunScalarS . runFlipS . unRepN)
  sfromVector = RepN . FlipS . tfromVectorS . V.map (runFlipS . unRepN)
  sfromVector0N = RepN . FlipS . tfromVector0NS . V.map (tunScalarS . runFlipS . unRepN)
  sunravelToList = map (RepN . FlipS) . tunravelToListS . runFlipS . unRepN
  sreplicate = RepN . FlipS . treplicateS . runFlipS . unRepN
  sreplicate0N = RepN . FlipS . treplicate0NS . tunScalarS . runFlipS . unRepN
  sappend u v = RepN $ FlipS $ tappendS (runFlipS $ unRepN u) (runFlipS $ unRepN v)
  sslice (_ :: Proxy i) _ = RepN . FlipS . tsliceS @i . runFlipS . unRepN
  sreverse = RepN . FlipS . treverseS . runFlipS . unRepN
  stranspose perm = RepN . FlipS . ttransposeS perm . runFlipS . unRepN
  sreshape = RepN . FlipS . treshapeS . runFlipS . unRepN
  sbuild1 f = RepN $ FlipS $ tbuild1S (runFlipS . unRepN . f . RepN . FlipR . tscalarR)
  smap0N f t = RepN $ FlipS $ tmap0NS (runFlipS . unRepN . f . RepN . FlipS) (runFlipS $ unRepN t)
  szipWith0N f t u =
    RepN $ FlipS $ tzipWith0NS (\v w -> runFlipS $ unRepN $ f (RepN $ FlipS v) (RepN $ FlipS w))
                        (runFlipS $ unRepN t) (runFlipS $ unRepN u)
  sgather t f = RepN $ FlipS $ tgatherZS (runFlipS $ unRepN t)
                                  (fromIndexOfS . fmap unRepN . f . fmap RepN . toIndexOfS)
  sgather1 t f = RepN $ FlipS $ tgatherZ1S (runFlipS $ unRepN t)
                                  (fromIndexOfS . fmap unRepN . f . RepN . FlipR . tscalarR)
  scast = RepN . FlipS . tcastS . runFlipS . unRepN
  sfromIntegral = RepN . FlipS . tfromIntegralS . runFlipS . unRepN
  sconst = RepN . FlipS
  sfromR = RepN . FlipS . flip Nested.rcastToShaped knownShS . runFlipR . unRepN

  sscaleByScalar s v =
    RepN $ FlipS $ tscaleByScalarS (tunScalarS $ runFlipS $ unRepN s) (runFlipS $ unRepN v)
  sdot1In proxy u v = RepN $ FlipS $ tdot1InS proxy (runFlipS $ unRepN u) (runFlipS $ unRepN v)

  sconstant = id
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
    STKR STKScalar{} SNat -> FTKR $ tshapeR $ runFlipR $ unRepN t
    STKS STKScalar{} sh -> FTKS sh
    STKX STKScalar{} sh -> withKnownShX sh $ FTKX $ Nested.mshape $ runFlipX $ unRepN t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      FTKProduct (tshapeFull stk1 (tproject1 t))
                 (tshapeFull stk2 (tproject2 t))
    STKUntyped -> FTKUntyped $ voidFromHVector $ tunvector t
    _ -> error "TODO"
  tcond _ b u v = if b then u else v
  tconstant _ t = t
  tprimalPart _ = id
  tdualPart _stk _t = DummyDualTarget
  tD _stk t _d = t
  dmkHVector = RepN
  dlambda _ f x = unRepN $ unHFun f $ RepN x
  dHApply f x = RepN $ f $ unRepN x
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
  STKR STKScalar{} SNat -> rfromList $ NonEmpty.fromList t
  STKS STKScalar{} sh -> withKnownShS sh $ sfromList $ NonEmpty.fromList t
  STKX STKScalar{} sh -> withKnownShX sh $ error "TODO"
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
  STKR STKScalar{} SNat -> runravelToList t
  STKS STKScalar{} sh -> withKnownShS sh $ sunravelToList t
  STKX STKScalar{} sh -> withKnownShX sh $ error "TODO"
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
         => AdaptableHVector RepN (RepN (TKR r n)) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector RepN (RepN (TKR Double n)) #-}
  type X (RepN (TKR r n)) = TKR r n
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    case sameTensorKind @(TKR r n) @(ADTensorKind (TKR r n)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (rzero $ rshape aInit, Nothing)

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector RepN (AsHVector (RepN (TKR r n))) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector RepN (AsHVector (RepN (TKR Double n))) #-}
  type X (AsHVector (RepN (TKR r n))) = TKUntyped
  toHVectorOf = RepN . V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance ForgetShape (RepN (TKR r n)) where
  type NoShape (RepN (TKR r n)) = RepN (TKR r n)
  forgetShape = id

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector RepN (RepN (TKS r sh)) where
  type X (RepN (TKS r sh)) = TKS r sh
  toHVectorOf = id
  fromHVector _aInit t = Just (t, Nothing)
  fromHVectorAD _aInit t | Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    case sameTensorKind @(TKS r sh) @(ADTensorKind (TKS r sh)) of
      Just Refl -> Just (t, Nothing)
      _ -> Just (srepl 0, Nothing)

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector RepN (AsHVector (RepN (TKS r sh))) where
  type X (AsHVector (RepN (TKS r sh))) = TKUntyped
  toHVectorOf = RepN . V.singleton . DynamicShaped . unAsHVector
  fromHVector _aInit params = case V.uncons $ tunvector params of
    Just (dynamic, rest) ->
      Just (AsHVector $ fromDynamicS (srepl 0) dynamic, Just $ dmkHVector rest)
    Nothing -> Nothing

instance GoodScalar r
         => ForgetShape (RepN (TKS r sh)) where
  type NoShape (RepN (TKS r sh)) = RepN (TKR r (Rank sh))  -- key case
  forgetShape = RepN . FlipR . Nested.stoRanked . runFlipS . unRepN

instance (KnownShS sh, GoodScalar r, Fractional r, Random r)
         => RandomHVector (RepN (TKS r sh)) where
  randomVals :: forall g. RandomGen g => Double -> g -> (RepN (TKS r sh), g)
  randomVals range g =
    let createRandomVector :: Int -> g -> OSArray r sh
        createRandomVector n seed =
          unRepN (srepl (2 * realToFrac range))
          * (FlipS (Nested.sfromVector knownShS (V.fromListN n (randoms seed)))
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
    DynamicRanked t -> DynamicRanked $ constantADVal $ rconst $ runFlipR $ unRepN t
    DynamicShaped t -> DynamicShaped $ constantADVal $ sconst $ runFlipS $ unRepN t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
