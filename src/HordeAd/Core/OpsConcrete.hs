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
import Data.Default
import Data.Foldable qualified as Foldable
import Data.Function ((&))
import Data.Int (Int64)
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.Index (imap)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Type.Ord (Compare)
import Data.Vector.Generic qualified as V
import Data.Vector.Storable qualified as VS
import GHC.Exts (IsList (..))
import GHC.IsList qualified as IsList
import GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+), type (<=))
import Numeric.LinearAlgebra (Numeric)
import Numeric.LinearAlgebra qualified as LA
import System.Random
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise1)
import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (StaticShX (..))
import Data.Array.Nested
  ( IShR
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , pattern (:$:)
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape (shrRank, shsAppend)
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.Adaptor
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.CarriersConcrete ()
import HordeAd.Core.Delta
import HordeAd.Core.HVectorOps
import HordeAd.Core.OpsADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

instance EqF RepN where
  (==.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u ==. RepN v = case stensorKind @y of
    STKScalar _ -> u == v
    STKR SNat STKScalar{} -> u == v
    STKS sh STKScalar{} -> withKnownShS sh $ u == v
    STKX sh STKScalar{} -> withKnownShX sh $ u == v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                                 , Dict <- lemTensorKindOfSTK stk2 ->
      RepN @y1 (fst u) ==. RepN  @y1(fst v)
      && RepN @y2 (snd u) ==. RepN @y2 (snd v)
    STKUntyped -> error "TODO"
    _ -> error "TODO"

instance OrdF RepN where
  (<.) :: forall y. TensorKind y => RepN y -> RepN y -> Bool
  RepN u <. RepN v = case stensorKind @y of
    STKScalar _ -> u < v
    STKR SNat STKScalar{} -> u < v
    STKS sh STKScalar{} -> withKnownShS sh $ u < v
    STKX sh STKScalar{} -> withKnownShX sh $ u < v
    STKProduct @y1 @y2 stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                                 , Dict <- lemTensorKindOfSTK stk2 ->
      RepN @y1 (fst u) <. RepN @y1 (fst v)
      && RepN @y2 (snd u) <. RepN @y2 (snd v)
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

instance BaseTensor RepN where
  rshape = tshapeR . unRepN
  rminIndex = RepN . tminIndexR . unRepN
  rmaxIndex = RepN . tmaxIndexR . unRepN
  rfloor = RepN . tfloorR . unRepN
  rindex v ix = tindexZR v (fmap unRepN $ ix)
--  rindex0 v ix = RepN . tscalarR $ tindex0R (unRepN v) (fmap unRepN $ ix)
-- TODO: re-add when there's a faster implementation
--  roneHot sh v ix = RepN $ toneHotR sh (unRepN v) (fmap unRepN $ ix)
  rsum = RepN . tsumR . unRepN
  rsum0 = RepN . tscalarR . tsum0R . unRepN
  rdot0 u v = RepN $ tscalarR $ tdot0R (unRepN u) (unRepN v)
  rmatmul2 m1 m2 = RepN $ tmatmul2R (unRepN m1) (unRepN m2)
  rscatter sh t f = RepN $ tscatterZR sh (unRepN t)
                                         (fmap unRepN . f . fmap RepN)
  rscatter1 sh t f = RepN $ tscatterZ1R sh (unRepN t)
                                           (fmap unRepN . f . RepN)
  rfromList = RepN . tfromListR . NonEmpty.map unRepN
  rfromList0N sh = RepN . tfromList0NR sh . map unRepN
  rfromVector = RepN . tfromVectorR . V.map unRepN
  rfromVector0N sh = RepN . tfromVector0NR sh . V.map unRepN
  runravelToList = map RepN . tunravelToListR . unRepN
  rreplicate k = RepN . treplicateR k . unRepN
  rreplicate0N sh = RepN . treplicate0NR sh . unRepN
  rappend u v = RepN $ tappendR (unRepN u) (unRepN v)
  rslice i n = RepN . tsliceR i n . unRepN
  rreverse = RepN . treverseR . unRepN
  rtranspose perm = RepN . ttransposeR perm . unRepN
  rreshape sh = RepN . treshapeR sh . unRepN
  rbuild1 k f = RepN $ tbuild1R k (unRepN . f . RepN)
  rmap0N :: forall r r1 n target.
            (target ~ RepN, TensorKind2 r, TensorKind2 r1, KnownNat n)
         => (target (TKR2 0 r1) -> target (TKR2 0 r)) -> target (TKR2 n r1)
         -> target (TKR2 n r)
  rmap0N f t = case (stensorKind @r1, stensorKind @r) of
    (STKScalar{}, STKScalar{}) -> RepN $ tmap0NR (unRepN . f . RepN) (unRepN t)
    _ ->  -- TODO: how to call the default implementation?
      rbuild (rshape t) (f . rindex0 t)
  rzipWith0N :: forall r1 r2 r n target.
                (target ~ RepN, TensorKind2 r1, TensorKind2 r2, TensorKind2 r, KnownNat n)
             => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r))
             -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r)
  rzipWith0N f t u = case (stensorKind @r1, stensorKind @r2, stensorKind @r) of
    (STKScalar{}, STKScalar{}, STKScalar{}) ->
      RepN $ tzipWith0NR (\v w -> unRepN $ f (RepN v) (RepN w))
                         (unRepN t) (unRepN u)
    _ ->  -- TODO: how to call the default implementation?
      rbuild (rshape u) (\ix -> f (rindex0 t ix) (rindex0 u ix))
  rgather sh t f = RepN $ tgatherZR sh (unRepN t)
                                       (fmap unRepN . f . fmap RepN)
  rgather1 k t f = RepN $ tgatherZ1R k (unRepN t)
                                       (fmap unRepN . f . RepN)
  rcast = RepN . tcastR . unRepN
  rfromIntegral = RepN . tfromIntegralR . unRepN
  rzip (RepN (a, b)) = RepN $ Nested.rzip a b
  runzip = RepN . Nested.runzip . unRepN
  rtoScalar = RepN . Nested.runScalar . unRepN
  rfromScalar = RepN . Nested.rscalar . unRepN

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
-- TODO: add when there's a faster implementation
--  xoneHot = ...
  xfromVector = error "TODO"
  xreplicate _ = error "TODO"
  xzip (RepN (a, b)) = RepN $ Nested.mzip a b
  xunzip = RepN . Nested.munzip . unRepN
  xtoScalar = RepN . Nested.munScalar . unRepN
  xfromScalar = RepN . Nested.mscalar . unRepN
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
  sindex v ix = tindexZS v (fmap unRepN $ ix)
--  sindex0 v ix = RepN . tscalarS $ tindex0S (unRepN v) (fmap unRepN $ ix)
-- TODO: re-add when there's a faster implementation
{-  soneHot  :: forall r sh1 sh2.
              ( TensorKind2 r, KnownShS sh2
              , KnownShS (sh1 ++ sh2) )
           => RepN (TKS2 sh2 r) -> IxSOf RepN sh1
           -> RepN (TKS2 (sh1 ++ sh2) r)
  soneHot v ix = case stensorKind @r of
    STKScalar{} -> RepN $ toneHotS (unRepN v) (fmap unRepN $ ix)
    _ -> error "TODO" -}
  ssum = RepN . tsumS . unRepN
  ssum0 = RepN . tscalarS . tsum0S . unRepN
  sdot0 u v = RepN $ tscalarS $ tdot0S (unRepN u) (unRepN v)
  smatmul2 m1 m2 = RepN $ tmatmul2S (unRepN m1) (unRepN m2)
  sscatter t f = RepN $ tscatterZS (unRepN t)
                                   (fmap unRepN . f . fmap RepN)
  sscatter1 t f = RepN $ tscatterZ1S (unRepN t)
                                      (fmap unRepN . f . RepN)
  sfromList = RepN . tfromListS . NonEmpty.map unRepN
  sfromList0N = RepN . tfromList0NS . map unRepN
  sfromVector = RepN . tfromVectorS . V.map unRepN
  sfromVector0N = RepN . tfromVector0NS . V.map unRepN
  sunravelToList = map RepN . tunravelToListS . unRepN
  sreplicate = RepN . treplicateS . unRepN
  sreplicate0N = RepN . treplicate0NS . unRepN
  sappend u v = RepN $ tappendS (unRepN u) (unRepN v)
  sslice (_ :: Proxy i) _ = RepN . tsliceS @i . unRepN
  sreverse = RepN . treverseS . unRepN
  stranspose perm = RepN . ttransposeS perm . unRepN
  sreshape = RepN . treshapeS . unRepN
  sbuild1 f = RepN $ tbuild1S (unRepN . f . RepN)
  smap0N :: forall r1 r sh target.
            (target ~ RepN, TensorKind2 r1, TensorKind2 r, KnownShS sh)
         => (target (TKS2 '[] r1) -> target (TKS2 '[] r)) -> target (TKS2 sh r1)
         -> target (TKS2 sh r)
  smap0N f v = case (stensorKind @r1, stensorKind @r) of
    (STKScalar{}, STKScalar{}) ->
      RepN $ tmap0NS (unRepN . f . RepN) (unRepN v)
    _ ->  -- TODO: how to call the default implementation?
      gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
      $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
      $ sbuild @target @r @(Rank sh) (f . sindex0 v)
  szipWith0N :: forall r1 r2 r sh target.
                ( target ~ RepN, TensorKind2 r1, TensorKind2 r2, TensorKind2 r
                , KnownShS sh )
             => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r))
             -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r)
  szipWith0N f t u = case (stensorKind @r1, stensorKind @r2, stensorKind @r) of
    (STKScalar{}, STKScalar{}, STKScalar{}) ->
      RepN $ tzipWith0NS (\v w -> unRepN $ f (RepN v) (RepN w))
                         (unRepN t) (unRepN u)
    _ ->  -- TODO: how to call the default implementation?
      gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
      $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
      $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 t ix) (sindex0 u ix))
  sgather t f = RepN $ tgatherZS (unRepN t)
                                 (fmap unRepN . f . fmap RepN)
  sgather1 t f = RepN $ tgatherZ1S (unRepN t)
                                   (fmap unRepN . f . RepN)
  scast = RepN . tcastS . unRepN
  sfromIntegral = RepN . tfromIntegralS . unRepN
  szip (RepN (a, b)) = RepN $ Nested.szip a b
  sunzip = RepN . Nested.sunzip . unRepN
  stoScalar = RepN . Nested.sunScalar . unRepN
  sfromScalar = RepN . Nested.sscalar . unRepN

  sscaleByScalar s v =
    RepN $ tscaleByScalarS (tunScalarS $ unRepN s) (unRepN v)
  sdot1In proxy u v = RepN $ tdot1InS proxy (unRepN u) (unRepN v)

  sfromPrimal = id
  sprimalPart = id
  sdualPart _ = DummyDualTarget
  sD u _ = u
  sScale _ _ = DummyDualTarget

  kfloor = RepN . floor . unRepN
  kcast = RepN . realToFrac . unRepN
  kfromIntegral = RepN . fromIntegral . unRepN

  rfromS = RepN . Nested.stoRanked . unRepN
  rfromX = RepN . Nested.mtoRanked . unRepN
  sfromR = RepN . flip Nested.rcastToShaped knownShS . unRepN
  sfromX = RepN . flip Nested.mcastToShaped knownShS . unRepN
  xfromR :: forall sh r. (KnownShX sh, TensorKind1 r)
         => RepN (TKR2 (Rank sh) r) -> RepN (TKX2 sh r)
  xfromR = RepN . Nested.rcastToMixed (knownShX @sh) . unRepN
  xfromS :: forall sh sh' r.
            (KnownShX sh', Rank sh ~ Rank sh', TensorKind1 r)
         => RepN (TKS2 sh r) -> RepN (TKX2 sh' r)
  xfromS = RepN . Nested.scastToMixed (knownShX @sh') . unRepN

  xnestR :: forall sh1 m x. TensorKind1 x
         => StaticShX sh1 -> RepN (TKX2 (sh1 ++ Replicate m Nothing) x)
         -> RepN (TKX2 sh1 (TKR2 m x))
  xnestR sh =
    RepN
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing)
                                                      (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Ranked m (RepORArray x)))
    . Nested.mnest sh
    . unRepN
  xnestS :: forall sh1 sh2 x. TensorKind1 x
         => StaticShX sh1 -> RepN (TKX2 (sh1 ++ MapJust sh2) x)
         -> RepN (TKX2 sh1 (TKS2 sh2 x))
  xnestS sh =
    RepN
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Mixed (MapJust sh2)
                                                      (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Shaped m (RepORArray x)))
    . Nested.mnest sh
    . unRepN
  xnest :: forall sh1 sh2 x. TensorKind1 x
        => StaticShX sh1 -> RepN (TKX2 (sh1 ++ sh2) x)
        -> RepN (TKX2 sh1 (TKX2 sh2 x))
  xnest sh = RepN . Nested.mnest sh . unRepN

  xunNestR :: forall sh1 m x.
              RepN (TKX2 sh1 (TKR2 m x))
           -> RepN (TKX2 (sh1 ++ Replicate m Nothing) x)
  xunNestR =
    RepN
    . Nested.munNest
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Ranked m (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Mixed (Replicate m Nothing)
                                                      (RepORArray x)))
    . unRepN
  xunNestS :: forall sh1 sh2 x.
              RepN (TKX2 sh1 (TKS2 sh2 x))
           -> RepN (TKX2 (sh1 ++ MapJust sh2) x)
  xunNestS =
    RepN
    . Nested.munNest
    . (unsafeCoerce :: Nested.Mixed sh1 (Nested.Shaped m (RepORArray x))
                    -> Nested.Mixed sh1 (Nested.Mixed (MapJust sh2)
                                                      (RepORArray x)))
    . unRepN
  xunNest = RepN . Nested.munNest . unRepN

  tpair u v = RepN (unRepN u, unRepN v)
  tproject1 = RepN . fst . unRepN
  tproject2 = RepN . snd . unRepN
  dshape = voidFromHVector . unRepN
  tftk stk (RepN t) = tftkG stk t
  tcond _ b u v = if b then u else v
  tfromPrimal _ t = t
  tprimalPart _ = id
  tdualPart _stk _t = DummyDualTarget
  tD _stk t _d = t
  tconcrete _ = id
  dmkHVector = RepN
  tlambda _ f x = unRepN $ unHFun f $ RepN x
  tApply f x = RepN $ f $ unRepN x
  dbuild1 k f =
    dmkHVector $ ravelHVector $ map (tunvector . f . fromIntegral) [0 .. sNatValue k - 1]
  -- The code for drevDt and dfwd in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drev :: forall x z. (TensorKind x, TensorKind z)
       => FullTensorKind x
       -> HFun x z
       -> HFunOf RepN x (ADTensorKind x)
  drev _ftk h =
    let rf :: RepORArray x -> RepORArray (ADTensorKind x)
        rf !a = unRepN $ fst $ crevOnHVector Nothing (unHFun h) (RepN a)
    in rf
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => FullTensorKind x
         -> HFun x z
         -> HFunOf RepN (TKProduct (ADTensorKind z) x) (ADTensorKind x)
  drevDt _ftk h =
    let rf :: RepORArray (TKProduct (ADTensorKind z) x) -> RepORArray (ADTensorKind x)
        rf !db_a = unRepN $ fst
                   $ crevOnHVector (Just $ RepN $ fst db_a) (unHFun h) (RepN $ snd db_a)
    in rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => FullTensorKind x
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
  STKScalar rep | Just Refl <- testEquality rep (typeRep @Z0) -> RepN Z0
  STKR SNat STKScalar{} -> rfromList $ NonEmpty.fromList t
  STKS sh STKScalar{} -> withKnownShS sh $ sfromList $ NonEmpty.fromList t
  STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @y1)
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @y2) ->
      let (lt1, lt2) = unzip $ map (\u -> (tproject1 u, tproject2 u)) t
      in tpair (ravel k lt1) (ravel k lt2)
  STKUntyped -> dmkHVector $ ravelHVector $ tunvector <$> t
  _ -> error "TODO"

unravel :: forall k y. TensorKind y
        => SNat k -> RepN (BuildTensorKind k y)
        -> [RepN y]
unravel k@SNat t = case stensorKind @y of
  STKScalar rep | Just Refl <- testEquality rep (typeRep @Z0) ->
    replicate (sNatValue k) (RepN Z0)
  STKR SNat STKScalar{} -> runravelToList t
  STKS sh STKScalar{} -> withKnownShS sh $ sunravelToList t
  STKX sh STKScalar{} -> withKnownShX sh $ error "TODO"
  STKProduct @y1 @y2 stk1 stk2
    | Dict <- lemTensorKindOfSTK stk1
    , Dict <- lemTensorKindOfSTK stk2
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @y1)
    , (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @y2) ->
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
     (TensorKind1 accShs, TensorKind1 bShs, TensorKind eShs)
  => SNat k
  -> FullTensorKind accShs
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumR k _ bShs _ f acc0 es
 | (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (constantTarget 0 bShs))
  _ ->
    let g a b = let res = f a b
                in (tproject1 res, tproject2 res)
        (xout, lout) = mapAccumR g acc0 (unravel k es)
    in tpair xout (ravel k lout)
      -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: forall k accShs bShs eShs.
     (TensorKind1 accShs, TensorKind1 bShs, TensorKind eShs)
  => SNat k
  -> FullTensorKind accShs
  -> FullTensorKind bShs
  -> FullTensorKind eShs
  -> (RepN accShs -> RepN eShs
      -> RepN (TKProduct accShs bShs))
  -> RepN accShs
  -> RepN (BuildTensorKind k eShs)
  -> RepN (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumL k _ bShs _ f acc0 es
 | (Dict, Dict) <- lemTensorKind1OfBuild k (stensorKind @bShs) = case sNatValue k of
  0 -> tpair acc0 (treplicate k (stensorKind @bShs) (constantTarget 0 bShs))
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
  :: FullTensorKind TKUntyped
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

-- TODO: check what the following did in tsum0R and if worth emulating
-- (also in sum1Inner and extremum and maybe tdot0R):
-- LA.sumElements $ OI.toUnorderedVectorT sh t


-- * Internal definitions

-- We often debug around here, so let's add Show and obfuscate it
-- to avoid warnings that it's unused. The addition silences warnings upstream.
type NumAndShow r = (Nested.KnownElt r, Nested.NumElt r, Num r, Show r, Default r)

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNR :: forall n m a. Nested.PrimElt a
         => Nested.Ranked (n + m) a -> [(IIxR64 n, Nested.Ranked m a)]
         -> Nested.Ranked (n + m) a
updateNR arr upd =
  let values = Nested.rtoVector arr
      sh = Nested.rshape arr
      f !t (ix, u) =
        let v = Nested.rtoVector u
            i = fromIntegral $ toLinearIdx @n @m fromIntegral sh ix
        in V.concat [V.take i t, v, V.drop (i + V.length v) t]
  in Nested.rfromVector sh (foldl' f values upd)

tshapeR
  :: Nested.Elt r
  => Nested.Ranked n r -> IShR n
tshapeR = Nested.rshape

tminIndexR
  :: forall n r r2. (Nested.PrimElt r, Nested.PrimElt r2, NumAndShow r, NumAndShow r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tminIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rminIndexPrim
  in Nested.rrerank (SNat @n) ZSR f

tmaxIndexR
  :: forall n r r2. (Nested.PrimElt r, Nested.PrimElt r2, NumAndShow r, NumAndShow r2, KnownNat n)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r2
tmaxIndexR =
  let f :: Nested.Ranked 1 r -> Nested.Ranked 0 r2
      f = Nested.rscalar . fromIntegral . Nested.Internal.Shape.ixrHead
          . Nested.rmaxIndexPrim
  in Nested.rrerank (SNat @n) ZSR f

tfloorR :: (Nested.PrimElt r, RealFrac r, Nested.PrimElt r2, Integral r2)
        => Nested.Ranked n r -> Nested.Ranked n r2
tfloorR = liftVR (V.map floor)

liftVR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r
liftVR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))

ixInBounds :: [Int64] -> [Int] -> Bool
ixInBounds ix sh =
  and $ zipWith (\i dim -> 0 <= i && i < fromIntegral dim) ix sh

tindexNR
  :: forall m n r. (KnownNat m, KnownNat n, Nested.Elt r, Show r)
  => Nested.Ranked (m + n) r -> IIxR64 m -> Nested.Ranked n r
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

tindexZR'
  :: forall m n r. (KnownNat m, KnownNat n, Nested.Elt r, Default r, Show r)
  => Nested.Ranked (m + n) r -> IIxR64 m -> Nested.Ranked n r
tindexZR' v ix =
  let sh = Nested.rshape v
  in if ixInBounds (toList ix) (toList sh)
     then tindexNR v ix
     else Nested.rreplicate (dropShape @m sh) (Nested.rscalar def)

tindexZR
  :: forall m n r. (KnownNat m, KnownNat n, TensorKind2 r)
  => RepN (TKR2 (m + n) r) -> IIxR64 m -> RepN (TKR2 n r)
tindexZR v ix = case tftk stensorKind v of
  FTKR sh x | SNat <- shrRank sh ->
   if ixInBounds (toList ix) (toList sh)
   then RepN $ tindexNR (unRepN v) ix
   else constantTarget 0 (FTKR (dropShape @m sh) x)

_tindex0R
  :: (KnownNat n, Nested.KnownElt r, Default r)
  => Nested.Ranked n r -> IIxR64 n -> r
_tindex0R v ix =
  let sh = Nested.rshape v
  in if ixInBounds (toList ix) (toList sh)
     then Nested.rindex v (fmap fromIntegral ix)
     else def
{- TODO: see above
tindex0R (RS.A (RG.A _ OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral $ indexToList ix)
                                        strides))
-}

_toneHotR
  :: forall m n r. (KnownNat n, Nested.KnownElt r,     Nested.PrimElt r, Nested.NumElt r, Num r, Show r, Default r)
  => IShR m -> Nested.Ranked n r -> IIxR64 m -> Nested.Ranked (m + n) r
_toneHotR sh v ix =
  tscatterZR @0 (Nested.Internal.Shape.shrAppend sh (Nested.rshape v))
             v (const ix)

-- | Sum the outermost dimension.
tsumR
  :: forall n r. (Nested.PrimElt r, NumAndShow r)
  => Nested.Ranked (1 + n) r -> Nested.Ranked n r
tsumR = Nested.rsumOuter1

-- | Sum all elements of a tensor.
tsum0R
  :: (Nested.PrimElt r, NumAndShow r)
  => Nested.Ranked n r -> r
tsum0R = Nested.rsumAllPrim

tdot0R
  :: (Nested.PrimElt r, NumAndShow r)
  => Nested.Ranked n r -> Nested.Ranked n r -> r
tdot0R = Nested.rdot
{-
tdot0R t u = OR.toVector t LA.<.> OR.toVector u
  -- TODO: if offset 0 and same strides, use toUnorderedVectorT
  -- TODO: if either has length 1 values, it may or may not be faster to do
  -- tsum0R (t * u)
-}

tdot1InR
  :: (Nested.PrimElt r, NumAndShow r)
  => Nested.Ranked (n + 1) r -> Nested.Ranked (n + 1) r -> Nested.Ranked n r
tdot1InR = Nested.rdot1Inner

tunravelToListR :: Nested.KnownElt r
                => Nested.Ranked (1 + n) r -> [Nested.Ranked n r]
tunravelToListR = Nested.rtoListOuter

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
              (KnownNat m, KnownNat n, Nested.PrimElt r, NumAndShow r)
           => IShR (p + n) -> Nested.Ranked (m + n) r
           -> (IIxR64 m -> IIxR64 p)
           -> Nested.Ranked (p + n) r
tscatterZR sh t f =
  let (shm, shDropP) = splitAt_Shape @m $ Nested.rshape t
      s = product $ shapeToList shm
      g ix =
        let ix2 = f ix
        in if ixInBounds (indexToList ix2) (shapeToList sh)
           then M.insertWith (V.zipWith (+)) ix2 (Nested.rtoVector $ t `tindexNR` ix)
           else id
      ivs = foldr g M.empty [ fromLinearIdx fromIntegral shm i
                            | i <- [0 .. fromIntegral s - 1] ]
  in updateNR (treplicate0NR sh (Nested.rscalar 0))
     $ map (second $ Nested.rfromVector shDropP)
     $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling Nested.rfromVector
-- or optimize tscatterNR and instantiate it instead
tscatterZ1R :: (Nested.PrimElt r, NumAndShow r)
            => IShR (p + n) -> Nested.Ranked (1 + n) r -> (Int64 -> IIxR64 p)
            -> Nested.Ranked (p + n) r
tscatterZ1R sh t f =
  sum $ imap (\i ti ->
                 let ix2 = f $ fromIntegral i
                 in if ixInBounds (indexToList ix2) (shapeToList sh)
                    then updateNR (treplicate0NR sh (Nested.rscalar 0)) [(ix2, ti)]
                    else treplicate0NR sh (Nested.rscalar def))
      $ tunravelToListR t

tfromListR
  :: forall n r. Nested.KnownElt r
  => NonEmpty (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tfromListR = Nested.rfromListOuter  -- TODO: make this strict

-- TODO: make this strict
tfromList0NR
  :: Nested.KnownElt r
  => IShR n -> [Nested.Ranked 0 r] -> Nested.Ranked n r
tfromList0NR sh l = case NonEmpty.nonEmpty l of
  Nothing -> Nested.rreshape sh Nested.remptyArray
  Just nl -> Nested.rfromListLinear sh $ NonEmpty.map Nested.runScalar nl

tfromVectorR
  :: forall n r. Nested.KnownElt r
  => Data.Vector.Vector (Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tfromVectorR = tfromListR . NonEmpty.fromList . V.toList

tfromVector0NR
  :: Nested.KnownElt r
  => IShR n -> Data.Vector.Vector (Nested.Ranked 0 r) -> Nested.Ranked n r
tfromVector0NR sh = tfromList0NR sh . V.toList

treplicateR
  :: forall n r. Nested.KnownElt r
  => Int -> Nested.Ranked n r -> Nested.Ranked (1 + n) r
treplicateR n = Nested.rreplicate (n :$: ZSR)

treplicate0NR
  :: Nested.KnownElt r
  => IShR n -> Nested.Ranked 0 r -> Nested.Ranked n r
treplicate0NR sh = Nested.rreplicate sh

tappendR
  :: Nested.KnownElt r
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
  -> Nested.Ranked (1 + n) r
tappendR = Nested.rappend

tsliceR
  :: Nested.KnownElt r
  => Int -> Int -> Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
tsliceR = Nested.rslice

treverseR
  :: Nested.KnownElt r
  => Nested.Ranked (1 + n) r -> Nested.Ranked (1 + n) r
treverseR = Nested.rrev1

ttransposeR
  :: Nested.KnownElt r
  => Permutation.PermR -> Nested.Ranked n r -> Nested.Ranked n r
ttransposeR = Nested.rtranspose

treshapeR
  :: Nested.KnownElt r
  => IShR m -> Nested.Ranked n r -> Nested.Ranked m r
treshapeR = Nested.rreshape

tbuild1R
  :: forall n r. Nested.KnownElt r
  => Int -> (Int64 -> Nested.Ranked n r) -> Nested.Ranked (1 + n) r
tbuild1R k f =
  Nested.rfromListOuter
  $ NonEmpty.map f
  $ NonEmpty.fromList [0 .. fromIntegral k - 1]  -- hope this fuses

tmap0NR
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r) -> Nested.Ranked n r1 -> Nested.Ranked n r
tmap0NR f =
  Nested.Internal.arithPromoteRanked
    (Nested.Internal.Mixed.mliftPrim (Nested.runScalar . f . Nested.rscalar ))
      -- too slow: tbuildNR (tshapeR v) (\ix -> f $ v `tindexNR` ix)

tzipWith0NR
  :: (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Ranked 0 r1 -> Nested.Ranked 0 r2 -> Nested.Ranked 0 r)
  -> Nested.Ranked n r1 -> Nested.Ranked n r2 -> Nested.Ranked n r
tzipWith0NR f =
  Nested.Internal.arithPromoteRanked2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.runScalar $ f (Nested.rscalar x) (Nested.rscalar y)))

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZR
--
-- Note how tindexZR is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZR :: forall m p n r.
             (Nested.PrimElt r, KnownNat m, KnownNat p, KnownNat n, NumAndShow r)
          => IShR (m + n) -> Nested.Ranked (p + n) r
          -> (IIxR64 m -> IIxR64 p)
          -> Nested.Ranked (m + n) r
tgatherZR sh t f =
  let shm = takeShape @m sh
      s = sizeShape shm
      l = [ Nested.rtoVector $ t `tindexZR'` f (fromLinearIdx fromIntegral shm i)
          | i <- [0 .. fromIntegral s - 1] ]
  in Nested.rfromVector sh $ V.concat l

tgatherZ1R :: forall p n r. (KnownNat p, KnownNat n, NumAndShow r)
           => Int -> Nested.Ranked (p + n) r -> (Int64 -> IIxR64 p)
           -> Nested.Ranked (1 + n) r
tgatherZ1R k t f =
  let l = NonEmpty.map (\i -> t `tindexZR'` f i)
                       (NonEmpty.fromList [0 .. fromIntegral k - 1])
  in Nested.rfromListOuter l

tcastR :: (Nested.PrimElt r1, Nested.PrimElt r2, Real r1, Fractional r2)
       => Nested.Ranked n r1 -> Nested.Ranked n r2
tcastR = liftVR (V.map realToFrac)

tfromIntegralR :: (Nested.PrimElt r1, Nested.PrimElt r2, NumAndShow r2, Integral r1)
               => Nested.Ranked n r1 -> Nested.Ranked n r2
tfromIntegralR = liftVR (V.map fromIntegral)

tscalarR
  :: Nested.Elt r
  => r -> Nested.Ranked 0 r
tscalarR = Nested.rscalar

tunScalarR
  :: Nested.Elt r
  => Nested.Ranked 0 r -> r
tunScalarR = Nested.runScalar

tscaleByScalarR :: (Nested.PrimElt r, Num r)
                => r -> Nested.Ranked n r -> Nested.Ranked n r
tscaleByScalarR s = liftVR (V.map (* s))

-- TODO: try to weave a similar magic as in tindex0R
-- TODO: for the non-singleton case see
-- https://github.com/Mikolaj/horde-ad/pull/81#discussion_r1096532164
updateNS :: forall n sh r. (Nested.PrimElt r, KnownShS sh, KnownShS (Drop n sh))
         => Nested.Shaped sh r
         -> [(IIxS64 (Take n sh), Nested.Shaped (Drop n sh) r)]
         -> Nested.Shaped sh r
updateNS arr upd =
  let values = Nested.stoVector arr
      sh = knownShS @sh
      f !t (ix, u) =
        let v = Nested.stoVector u
            i = gcastWith (unsafeCoerce Refl
                           :: sh :~: Take n sh ++ Drop n sh)
                $ fromIntegral
                $ ShapedList.toLinearIdx @(Take n sh) @(Drop n sh)
                                         fromIntegral sh ix
        in V.concat [V.take i t, v, V.drop (i + V.length v) t]
  in Nested.sfromVector knownShS (foldl' f values upd)

tminIndexS
  :: forall n sh r r2. ( Nested.PrimElt r, Nested.PrimElt r2, NumAndShow r, NumAndShow r2, KnownShS sh
                       , KnownShS (Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tminIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead . Nested.sminIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerce Refl
                         :: Init (n ': sh) ++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerce Refl
                         :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
              Nested.srerank @'[m] @'[] @(Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tminIndexS: impossible someNatVal error"
        Nothing -> error "tminIndexS: impossible someNatVal error"

tmaxIndexS
  :: forall n sh r r2. ( Nested.PrimElt r, Nested.PrimElt r2, NumAndShow r, NumAndShow r2, KnownShS sh
                       , KnownShS (Init (n ': sh)) )
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (Init (n ': sh)) r2
tmaxIndexS =
  let f :: Nested.Shaped '[m] r -> Nested.Shaped '[] r2
      f = Nested.sscalar . fromIntegral . Nested.Internal.Shape.ixsHead . Nested.smaxIndexPrim
  in case sameShape @sh @'[] of
    Just Refl -> f @n
    _ ->
      let sh = shapeT @sh
      in case someNatVal $ toInteger $ last sh of
        Just (SomeNat @m _proxy) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat _proxy) ->
              gcastWith (unsafeCoerce Refl
                         :: Init (n ': sh) ++ '[m] :~: n ': sh) $
              gcastWith (unsafeCoerce Refl
                         :: Init (n ': sh) :~: Init (n ': sh) ++ '[]) $
              Nested.srerank @'[m] @'[] @(Init (n ': sh)) knownShS knownShS (f @m)
            Nothing -> error "tmaxIndexS: impossible someNatVal error"
        Nothing -> error "tmaxIndexS: impossible someNatVal error"

tfloorS :: forall r r2 sh.
           (Nested.PrimElt r, RealFrac r, Nested.PrimElt r2, Integral r2)
        => Nested.Shaped sh r -> Nested.Shaped sh r2
tfloorS = liftVS (V.map floor)

liftVS
  :: (Nested.PrimElt r1, Nested.PrimElt r)
  => (VS.Vector r1 -> VS.Vector r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r
liftVS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftNumElt1
       (`Mixed.Internal.Arith.liftVEltwise1` f))

tindexNS
  :: forall sh1 sh2 r. Nested.Elt r
  => Nested.Shaped (sh1 ++ sh2) r -> IIxS64 sh1 -> Nested.Shaped sh2 r
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

-- Note that after vectorization, the index with type IIxS64 sh1
-- may not fit within the type-level shape, which we catch in the @ixInBounds@
-- and return 0, so it's fine. Similarly in gather and scatter.
tindexZS'
  :: forall sh1 sh2 r. (KnownShS sh2, Nested.Elt r, Default r)
  => Nested.Shaped (sh1 ++ sh2) r -> IIxS64 sh1 -> Nested.Shaped sh2 r
tindexZS' v ix | Refl <- lemAppNil @sh2 =
  let sh = Nested.Internal.Shape.shsToList $ Nested.sshape v
  in if ixInBounds (ShapedList.indexToList ix) sh
     then tindexNS v ix
     else Nested.sreplicate (knownShS @sh2) (Nested.sscalar def)

tindexZS
  :: forall sh1 sh2 r. (KnownShS sh1, KnownShS sh2, TensorKind1 r)
  => RepN (TKS2 (sh1 ++ sh2) r) -> IIxS64 sh1 -> RepN (TKS2 sh2 r)
tindexZS v ix | Refl <- lemAppNil @sh2 =
  withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
  case tftk stensorKind v of
    FTKS sh x ->
      if ixInBounds (toList ix) (toList sh)
      then RepN $ tindexNS (unRepN v) ix
      else constantTarget 0 (FTKS knownShS x)

_tindex0S
  :: (Nested.KnownElt r, Default r)
  => Nested.Shaped sh r -> IIxS64 sh -> r
_tindex0S v ix =
  let sh = Nested.Internal.Shape.shsToList $ Nested.sshape v
  in if ixInBounds (ShapedList.indexToList ix) sh
     then Nested.sindex v (fmap fromIntegral ix)
     else def
{- TODO: benchmark if this is faster enough for its complexity;
         probably not, becasue orthotope's index does no canonicalization either
tindex0S (SS.A (SG.A OI.T{..})) ix =
  values V.! (offset + sum (zipWith (*) (map fromIntegral
                                         $ ShapedList.indexToList ix)
                                        strides))
    -- to avoid linearizing @values@, we do everything in unsized way
-}

_toneHotS
  :: forall sh1 sh2 r. (Nested.KnownElt r,    Nested.PrimElt r, Nested.NumElt r, Num r, Show r, Default r, KnownShS sh2, KnownShS (sh1 ++ sh2))
  => Nested.Shaped sh2 r -> IIxS64 sh1 -> Nested.Shaped (sh1 ++ sh2) r
_toneHotS v ix =
  gcastWith (unsafeCoerce Refl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
  gcastWith (unsafeCoerce Refl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
  tscatterZS @_ @'[] @(Rank sh1) v (const ix)

-- | Sum the outermost dimension.
tsumS
  :: forall n sh r. (Nested.PrimElt r, NumAndShow r)
  => Nested.Shaped (n ': sh) r -> Nested.Shaped sh r
tsumS = Nested.ssumOuter1

-- | Sum all elements of a tensor.
tsum0S
  :: forall sh r. (Nested.PrimElt r, NumAndShow r)
  => Nested.Shaped sh r -> r
tsum0S = Nested.ssumAllPrim

tdot0S
  :: forall sh r. (Nested.PrimElt r, NumAndShow r)
  => Nested.Shaped sh r -> Nested.Shaped sh r -> r
tdot0S = Nested.sdot

tdot1InS
  :: (Nested.PrimElt r, NumAndShow r)
  => Proxy n -> Nested.Shaped (sh ++ '[n]) r -> Nested.Shaped (sh ++ '[n]) r
  -> Nested.Shaped sh r
tdot1InS = Nested.sdot1Inner

tunravelToListS :: forall r n sh. Nested.KnownElt r
                => Nested.Shaped (n ': sh) r -> [Nested.Shaped sh r]
tunravelToListS = Nested.stoListOuter

tmatmul2S
  :: forall m n p r. (Nested.PrimElt r, KnownNat m, KnownNat n, KnownNat p, Numeric r)
  => Nested.Shaped '[m, n] r -> Nested.Shaped '[n, p] r -> Nested.Shaped '[m, p] r
tmatmul2S t u =
  let t2 = Nested.stoVector t
      u2 = Nested.stoVector u
  in Nested.sfromVector knownShS $ LA.flatten
     $ LA.reshape (valueOf @n) t2 LA.<> LA.reshape (valueOf @p) u2

-- Performance depends a lot on the number and size of tensors.
-- If tensors are not tiny, memory taken by underlying vectors matters most
-- and this implementation is probbaly optimal in this respect
-- (the only new vectors are created by V.concat, but this is done on demand).
-- TODO: optimize updateNS and make it consume and forget arguments
-- one by one to make the above true
--
-- Note how ix being in bounds is checked. The semantics of the operation
-- permits index out of bounds and then no tensors is added at such an index.
tscatterZS :: forall r sh2 p sh.
              (Nested.PrimElt r, NumAndShow r, KnownShS sh2, KnownShS sh, KnownShS (Drop p sh))
           => Nested.Shaped (sh2 ++ Drop p sh) r
           -> (IIxS64 sh2 -> IIxS64 (Take p sh))
           -> Nested.Shaped sh r
tscatterZS t f =
  let sh2 = knownShS @sh2
      g ix =
        let ix2 = f ix
        in if ixInBounds (ShapedList.indexToList ix2) (shapeT @sh)
           then M.insertWith (V.zipWith (+)) ix2
                  (Nested.stoVector $ tindexNS @sh2 @(Drop p sh) t ix)
           else id
      ivs = foldr g M.empty [ ShapedList.fromLinearIdx fromIntegral sh2
                              $ fromIntegral i
                            | i <- [0 .. sizeT @sh2 - 1] ]
  in updateNS (Nested.sreplicateScal knownShS 0)
     $ map (second $ Nested.sfromVector knownShS)
     $ M.assocs ivs

-- TODO: update in place in ST or with a vector builder, but that requires
-- building the underlying value vector with crafty index computations
-- and then freezing it and calling OS.fromVector
-- or optimize tscatterNS and instantiate it instead
tscatterZ1S :: forall r n2 p sh.
               (Nested.PrimElt r, NumAndShow r, KnownShS sh, KnownShS (Drop p sh))
            => Nested.Shaped (n2 ': Drop p sh) r
            -> (Int64 -> IIxS64 (Take p sh))
            -> Nested.Shaped sh r
tscatterZ1S t f =
    sum $ imap (\i ti ->
                   let ix2 = f $ fromIntegral i
                   in if ixInBounds (ShapedList.indexToList ix2)
                                    (shapeT @sh)
                      then updateNS (Nested.sreplicateScal knownShS 0) [(ix2, ti)]
                      else Nested.sreplicateScal knownShS def)
        $ tunravelToListS t

tfromListS
  :: forall n sh r. (Nested.KnownElt r, KnownNat n)
  => NonEmpty (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromListS = Nested.sfromListOuter SNat  -- TODO: make this strict

tfromListX
  :: forall n sh r. -- (NumAndShow r, KnownNat n)
   NonEmpty (Nested.Mixed sh r) -> Nested.Mixed (Just n ': sh) r
tfromListX = error "TODO"

-- TODO: make this strict
tfromList0NS
  :: forall r sh. (Nested.KnownElt r, KnownShS sh, KnownNat (Nested.Product sh))
  => [Nested.Shaped '[] r] -> Nested.Shaped sh r
tfromList0NS l = case NonEmpty.nonEmpty l of
  Nothing -> case sameNat (Proxy @(Nested.Product sh)) (Proxy @0) of
    Just Refl -> Nested.sreshape (knownShS @sh)
                 $ Nested.semptyArray (knownShS @sh)
    Nothing -> error "tfromList0NS: empty list, but not shape"
  Just nl -> Nested.sfromListLinear knownShS $ NonEmpty.map Nested.sunScalar nl

tfromVectorS
  :: forall n sh r. (Nested.KnownElt r, KnownNat n)
  => Data.Vector.Vector (Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tfromVectorS = tfromListS . NonEmpty.fromList . V.toList

_tfromVectorX
  :: forall n sh r. -- (NumAndShow r, KnownNat n)
   Data.Vector.Vector (Nested.Mixed sh r) -> Nested.Mixed (Just n ': sh) r
_tfromVectorX = tfromListX . NonEmpty.fromList . V.toList

tfromVector0NS
  :: forall r sh. (Nested.KnownElt r, KnownShS sh, KnownNat (Nested.Product sh))
  => Data.Vector.Vector (Nested.Shaped '[] r) -> Nested.Shaped sh r
tfromVector0NS = tfromList0NS . V.toList

treplicateS
  :: forall n sh r. (Nested.KnownElt r, KnownNat n)
  => Nested.Shaped sh r -> Nested.Shaped (n ': sh) r
treplicateS = Nested.sreplicate (SNat @n :$$ ZSS)

treplicate0NS
  :: forall r sh. (Nested.KnownElt r, KnownShS sh)
  => Nested.Shaped '[] r -> Nested.Shaped sh r
treplicate0NS | Refl <- lemAppNil @sh = Nested.sreplicate (knownShS @sh)

tappendS
  :: forall r m n sh. Nested.KnownElt r
  => Nested.Shaped (m ': sh) r -> Nested.Shaped (n ': sh) r -> Nested.Shaped ((m + n) ': sh) r
tappendS = Nested.sappend

tsliceS
  :: forall i n k sh r. (Nested.KnownElt r, KnownNat i, KnownNat n)
  => Nested.Shaped (i + n + k ': sh) r -> Nested.Shaped (n ': sh) r
tsliceS = Nested.sslice (SNat @i) SNat

treverseS
  :: forall n sh r. Nested.KnownElt r
  => Nested.Shaped (n ': sh) r -> Nested.Shaped (n ': sh) r
treverseS = Nested.srev1

-- TODO: remove the conversion and overhaul the whole codebase
ttransposeS
  :: forall perm r sh.
     (Nested.KnownElt r, PermC perm, Rank perm <= Rank sh )
  => Permutation.Perm perm -> Nested.Shaped sh r
  -> Nested.Shaped (Permutation.PermutePrefix perm sh) r
ttransposeS perm =
  gcastWith (unsafeCoerce Refl :: Compare (Rank perm) (Rank sh) :~: LT) $
  gcastWith (unsafeCoerce Refl
             :: Permutation.PermutePrefix perm sh :~: Permutation.PermutePrefix perm sh) $
  Nested.stranspose perm

treshapeS
  :: forall r sh sh2.
     (Nested.KnownElt r, KnownShS sh2, Nested.Product sh ~ Nested.Product sh2)
  => Nested.Shaped sh r -> Nested.Shaped sh2 r
treshapeS = Nested.sreshape knownShS

tbuild1S
  :: forall n sh r. (KnownNat n, Nested.KnownElt r)
  => (Int64 -> Nested.Shaped sh r) -> Nested.Shaped (n ': sh) r
tbuild1S f =
  let k = valueOf @n
  in Nested.sfromListOuter SNat
     $ NonEmpty.map f
     $ NonEmpty.fromList [0 .. k - 1]  -- hope this fuses

tmap0NS
  :: forall r1 r sh. (Nested.PrimElt r1, Nested.PrimElt r)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r) -> Nested.Shaped sh r1 -> Nested.Shaped sh r
tmap0NS f =
  Nested.Internal.arithPromoteShaped
    (Nested.Internal.Mixed.mliftPrim (Nested.sunScalar . f . Nested.sscalar))
      -- too slow: tbuildNS (tshapeS v) (\ix -> f $ v `tindexNS` ix)

tzipWith0NS
  :: forall r1 r2 r sh. (Nested.PrimElt r, Nested.PrimElt r1, Nested.PrimElt r2)
  => (Nested.Shaped '[] r1 -> Nested.Shaped '[] r2 -> Nested.Shaped '[] r)
  -> Nested.Shaped sh r1 -> Nested.Shaped sh r2 -> Nested.Shaped sh r
tzipWith0NS f =
  Nested.Internal.arithPromoteShaped2
    (Nested.Internal.Mixed.mliftPrim2
       (\x y -> Nested.sunScalar $ f (Nested.sscalar x) (Nested.sscalar y)))

-- TODO: this can be slightly optimized by normalizing t first (?)
-- and then inlining toVector and tindexZS
--
-- Note how tindexZS is used. The semantics of the operation
-- permits index out of bounds and the result of such indexing is zero.
tgatherZS :: forall sh2 p sh r.
             ( Nested.PrimElt r, NumAndShow r, KnownShS sh2, KnownShS (Drop p sh)
             , KnownShS (sh2 ++ Drop p sh) )
          => Nested.Shaped sh r
          -> (IIxS64 sh2 -> IIxS64 (Take p sh))
          -> Nested.Shaped (sh2 ++ Drop p sh) r
tgatherZS t f =
  let sh2 = knownShS @sh2
      s = sizeT @sh2
      l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Take p sh ++ Drop p sh)
          $ [ Nested.stoVector
                (t `tindexZS'` f (ShapedList.fromLinearIdx fromIntegral sh2
                                 $ fromIntegral i)
                 :: Nested.Shaped (Drop p sh) r)
            | i <- [0 .. s - 1] ]
  in Nested.sfromVector knownShS $ V.concat l

tgatherZ1S :: forall n2 p sh r.
              (NumAndShow r, KnownNat n2, KnownShS (Drop p sh))
           => Nested.Shaped sh r -> (Int64 -> IIxS64 (Take p sh))
           -> Nested.Shaped (n2 ': Drop p sh) r
tgatherZ1S t f =
  let l = gcastWith (unsafeCoerce Refl
                     :: sh :~: Take p sh ++ Drop p sh)
          $ NonEmpty.map (\i -> t `tindexZS'` f i)
                         (NonEmpty.fromList [0 .. valueOf @n2 - 1])
  in Nested.sfromListOuter SNat l

tcastS :: forall r1 r2 sh.
          (Nested.PrimElt r1, Nested.PrimElt r2, Real r1, Fractional r2)
       => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tcastS = liftVS (V.map realToFrac)

tfromIntegralS :: forall r1 r2 sh .
                  (Nested.PrimElt r1, Nested.PrimElt r2, NumAndShow r2, Integral r1)
               => Nested.Shaped sh r1 -> Nested.Shaped sh r2
tfromIntegralS = liftVS (V.map fromIntegral)

tscalarS
  :: Nested.Elt r
  => r -> Nested.Shaped '[] r
tscalarS = Nested.sscalar

tunScalarS
  :: Nested.Elt r
  => Nested.Shaped '[] r -> r
tunScalarS = Nested.sunScalar

tscaleByScalarS :: forall r sh. (Nested.PrimElt r, Num r)
                => r -> Nested.Shaped sh r -> Nested.Shaped sh r
tscaleByScalarS s = liftVS (V.map (* s))
