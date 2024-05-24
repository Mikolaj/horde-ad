{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.TensorConcrete
  () where

import Prelude hiding (foldl')

import           Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Function ((&))
import           Data.List (foldl', mapAccumL, mapAccumR, scanl')
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed as X
import qualified Data.Array.Nested as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX
import HordeAd.Internal.OrthotopeOrphanInstances (FlipS (..))
import HordeAd.Util.ShapedList (shapedNat, unShapedNat)

type instance BoolOf (ORArray) = Bool

instance EqF (ORArray) where
  u ==. v = u == v
  u /=. v = u /= v

instance OrdF (ORArray) where
  u <. v = u < v
  u <=. v = u <= v
  u >. v = u > v
  u >=. v = u >= v

instance IfF (ORArray) where
  ifF b v w = if b then v else w

type instance RankedOf (ORArray) = ORArray

type instance ShapedOf (ORArray) = OSArray

type instance HVectorOf (ORArray) = HVector (ORArray)

type instance HFunOf (ORArray) =
  [HVector (ORArray)] -> HVectorOf (ORArray)

type instance PrimalOf (ORArray) = ORArray

type instance DualOf (ORArray) = DummyDual

instance RankedTensor (ORArray) where
  rshape = tshapeR . runFlip
  rminIndex = Flip . tminIndexR . runFlip
  rmaxIndex = Flip . tmaxIndexR . runFlip
  rfloor = Flip . tfloorR . runFlip
  rindex v ix = Flip $ tindexZR (runFlip v) (fromIndexOfR ix)
  rindex0 v ix = Flip . tscalarR $ tindex0R (runFlip v) (fromIndexOfR ix)
  rsum = Flip . tsumR . runFlip
  rsum0 = Flip . tscalarR . tsum0R . runFlip
  rdot0 u v = Flip $ tscalarR $ tdot0R (runFlip u) (runFlip v)
  rmatvecmul m v = Flip $ tmatvecmulR (runFlip m) (runFlip v)
  rmatmul2 m1 m2 = Flip $ tmatmul2R (runFlip m1) (runFlip m2)
  rscatter sh t f = Flip $ tscatterZR sh (runFlip t)
                                         (fromIndexOfR . f . toIndexOfR)
  rscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t)
                                           (fromIndexOfR . f . Flip . tscalarR)
  rfromList = Flip . tfromListR . NonEmpty.map runFlip
  rfromList0N sh = Flip . tfromList0NR sh . map (tunScalarR . runFlip)
  rfromVector = Flip . tfromVectorR . V.map runFlip
  rfromVector0N sh = Flip . tfromVector0NR sh . V.map (tunScalarR . runFlip)
  runravelToList = map Flip . tunravelToListR . runFlip
  rreplicate k = Flip . treplicateR k . runFlip
  rreplicate0N sh = Flip . treplicate0NR sh . tunScalarR . runFlip
  rappend u v = Flip $ tappendR (runFlip u) (runFlip v)
  rslice i n = Flip . tsliceR i n . runFlip
  rreverse = Flip . treverseR . runFlip
  rtranspose perm = Flip . ttransposeR perm . runFlip
  rreshape sh = Flip . treshapeR sh . runFlip
  rbuild1 k f = Flip $ tbuild1R k (runFlip . f . Flip . tscalarR)
  rmap0N f t = Flip $ tmap0NR (runFlip . f . Flip) (runFlip t)
  rzipWith0N f t u = Flip $ tzipWith0NR (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  rgather sh t f = Flip $ tgatherZR sh (runFlip t)
                                       (fromIndexOfR . f . toIndexOfR)
  rgather1 k t f = Flip $ tgatherZ1R k (runFlip t)
                                       (fromIndexOfR . f . Flip . tscalarR)
  rcast = Flip . tcastR . runFlip
  rfromIntegral = Flip . tfromIntegralR . runFlip
  rconst = Flip
  rletHVectorIn = (&)
  rletHFunIn = (&)
  rfromS :: forall r sh. (GoodScalar r, KnownShS sh)
         => OSArray r sh -> ORArray r (Sh.Rank sh)
  rfromS t | Dict <- lemKnownNatRank (knownShS @sh) =
    Flip $ OR.fromVector (Nested.shSToList (knownShS @sh)) $ Nested.stoVector {-Nested.rstoRanked -} (runFlipS t)
    -- TODO

  rscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  rsumIn = Flip . tsumInR . runFlip
  rdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)

  rconstant = id
  rprimalPart = id
  rdualPart _ = DummyDual
  rD u _ = u
  rScale _ _ = DummyDual

type instance BoolOf (OSArray) = Bool

instance EqF (OSArray) where
  u ==. v = u == v
  u /=. v = u /= v

instance OrdF (OSArray) where
  u <. v = u < v
  u <=. v = u <= v
  u >. v = u > v
  u >=. v = u >= v

instance IfF (OSArray) where
  ifF b v w = if b then v else w

type instance RankedOf (OSArray) = ORArray

type instance ShapedOf (OSArray) = OSArray

type instance PrimalOf (OSArray) = OSArray

type instance DualOf (OSArray) = DummyDual

instance ShapedTensor (OSArray) where
  sminIndex = FlipS . tminIndexS . runFlipS
  smaxIndex = FlipS . tmaxIndexS . runFlipS
  sfloor = FlipS . tfloorS . runFlipS
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => OSArray r '[n]  -- from 0 to n - 1
  siota = let n = valueOf @n :: Int
          in FlipS $ Nested.sfromList1 SNat
             $ NonEmpty.map fromIntegral $ NonEmpty.fromList [0 .. n - 1]
  sindex v ix = FlipS $ tindexZS (runFlipS v) (fromIndexOfS ix)
  sindex0 v ix = FlipS . tscalarS $ tindex0S (runFlipS v) (fromIndexOfS ix)
  ssum = FlipS . tsumS . runFlipS
-- TODO:  ssum0 = FlipS . tscalarS . tsum0S . runFlipS
  sdot0 u v = FlipS $ tscalarS $ tdot0S (runFlipS u) (runFlipS v)
  smatvecmul m v = FlipS $ tmatvecmulS (runFlipS m) (runFlipS v)
  smatmul2 m1 m2 = FlipS $ tmatmul2S (runFlipS m1) (runFlipS m2)
  sscatter t f = FlipS $ tscatterZS (runFlipS t)
                                   (fromIndexOfS . f . toIndexOfS)
  sscatter1 t f = FlipS $ tscatterZ1S (runFlipS t)
                                      (fromIndexOfS . f . shapedNat . Flip
                                       . tscalarR . unShapedNat)
  sfromList = FlipS . tfromListS . NonEmpty.map runFlipS
  sfromList0N = FlipS . tfromList0NS . map (tunScalarS . runFlipS)
  sfromVector = FlipS . tfromVectorS . V.map runFlipS
  sfromVector0N = FlipS . tfromVector0NS . V.map (tunScalarS . runFlipS)
  sunravelToList = map FlipS . tunravelToListS . runFlipS
  sreplicate = FlipS . treplicateS . runFlipS
  sreplicate0N = FlipS . treplicate0NS . tunScalarS . runFlipS
  sappend u v = FlipS $ tappendS (runFlipS u) (runFlipS v)
  sslice (_ :: Proxy i) _ = FlipS . tsliceS @i . runFlipS
  sreverse = FlipS . treverseS . runFlipS
  stranspose (_ :: Proxy perm) = FlipS . ttransposeS @perm . runFlipS
  sreshape = FlipS . treshapeS . runFlipS
  sbuild1 f = FlipS $ tbuild1S (runFlipS . f . shapedNat . Flip
                                . tscalarR . unShapedNat)
-- TODO
--  smap0N f t = FlipS $ tmap0NS (runFlipS . f . FlipS) (runFlipS t)
--  szipWith0N f t u = FlipS $ tzipWith0NS (\v w -> runFlipS $ f (FlipS v) (FlipS w))
--                                        (runFlipS t) (runFlipS u)
  sgather t f = FlipS $ tgatherZS (runFlipS t)
                                  (fromIndexOfS . f . toIndexOfS)
  sgather1 t f = FlipS $ tgatherZ1S (runFlipS t)
                                    (fromIndexOfS . f . shapedNat . Flip
                                     . tscalarR . unShapedNat)
  scast = FlipS . tcastS . runFlipS
  sfromIntegral = FlipS . tfromIntegralS . runFlipS
  sconst :: forall r sh.
            (GoodScalar r, KnownShS sh) => OS.Array sh r -> OSArray r sh
  sconst t | Dict <- lemShapeFromKnownShS (Proxy @sh)
           , Dict <- lemKnownNatRank (knownShS @sh) =
    gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: X.Rank sh) $
    FlipS $ Nested.rcastToShaped
              (Nested.rfromOrthotope (SNat @(X.Rank sh))
                                     (Data.Array.Convert.convert t))
              knownShS
  sletHVectorIn = (&)
  sletHFunIn = (&)
  sfromR :: forall r sh. (GoodScalar r, KnownShS sh)
         => ORArray r (Sh.Rank sh) -> OSArray r sh
  sfromR t | Dict <- lemShapeFromKnownShS (Proxy @sh)
           , Dict <- lemKnownNatRank (knownShS @sh) =
    gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: X.Rank sh) $
    FlipS $ Nested.rcastToShaped
              (Nested.rfromOrthotope (SNat @(X.Rank sh)) (runFlip t))
              knownShS

  sscaleByScalar s v =
    FlipS $ tscaleByScalarS (tunScalarS $ runFlipS s) (runFlipS v)
-- TODO:  ssumIn = FlipS . tsumInS . runFlipS
  sdot1In u v = FlipS $ tdot1InS (runFlipS u) (runFlipS v)

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual

instance HVectorTensor (ORArray) (OSArray) where
  dshape = voidFromHVector
  dmkHVector = id
  dlambda _ f = unHFun f  -- the eta-expansion is needed for typing
  dHApply f = f
  dunHVector = id
  dletHVectorInHVector = (&)
  dletHFunInHVector = (&)
  rletInHVector = (&)
  sletInHVector = (&)
  dbuild1 k f =
    ravelHVector $ map (f . fromIntegral) [0 .. (sNatValue k :: Int) - 1]
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ORArray)
       -> HVector (ORArray)
  rrev f _parameters0 parameters =
    -- This computes the derivative of g again for each new @parmeters@.
    let g :: HVector (ADVal (ORArray))
          -> ADVal (HVectorPseudoTensor (ORArray)) r y
        g !hv = let D a a' = f hv
                in dDnotShared (HVectorPseudoTensor $ dmkHVector
                                $ V.singleton $ DynamicRanked a)
                               (HVectorPseudoTensor $ HToH
                                $ V.singleton $ DynamicRanked a')
    in fst $ crevOnHVector Nothing g parameters
  -- The code for drevDt and dfwd in this instance is the same as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drevDt :: VoidHVector
         -> HFun
         -> HFunOf (ORArray)
  drevDt _shs h =
    let g :: ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) r y
        g !hv = let (as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
                               (HVectorPseudoTensor $ HToH as')
        rf :: [HVector (ORArray)] -> HVectorOf (ORArray)
        rf [!db, !a] =
          fst $ crevOnHVector (Just db) g a
        rf _ = error "rf: wrong number of arguments"
    in rf
  dfwd :: VoidHVector
       -> HFun
       -> HFunOf (ORArray)
  dfwd _shs h =
    let g :: ADReady f
          => HVector (ADVal f)
          -> ADVal (HVectorPseudoTensor f) r y
        g !hv = let (as, as') = unADValHVector $ unHFun h [hv]
                in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
                               (HVectorPseudoTensor $ HToH as')
        df :: [HVector (ORArray)] -> HVectorOf (ORArray)
        df [!da, !a] = fst $ cfwdOnHVector a g da
        df _ = error "df: wrong number of arguments"
    in df
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rscan f x0 as =
    rfromList $ NonEmpty.fromList $ scanl' f x0 (runravelToList as)
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sscan f x0 as =
    sfromList $ NonEmpty.fromList $ scanl' f x0 (sunravelToList as)
  -- The eta-expansion below is needed for typing.
  dmapAccumR _ k accShs bShs _eShs f acc0 es =
    oRdmapAccumR k accShs bShs _eShs f acc0 es
  dmapAccumRDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumR k accShs bShs eShs (\ !a !b -> f [a, b]) acc0 es
  dmapAccumL _ k accShs bShs _eShs f acc0 es =
    oRdmapAccumL k accShs bShs _eShs f acc0 es
  dmapAccumLDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumL k accShs bShs eShs (\ !a !b -> f [a, b]) acc0 es

oRdmapAccumR
  :: SNat k
  -> VoidHVector
  -> VoidHVector
  -> VoidHVector
  -> (HVector (ORArray) -> HVector (ORArray)
      -> HVectorOf (ORArray))
  -> HVector (ORArray)
  -> HVector (ORArray)
  -> HVector (ORArray)
oRdmapAccumR k accShs bShs _eShs f acc0 es = case sNatValue k :: Int of
  0 -> acc0 V.++ replicate1HVector k (V.map dynamicFromVoid bShs)
  _ -> let accLen = V.length accShs
           g :: HVector (ORArray) -> HVector (ORArray)
             -> (HVector (ORArray), HVector (ORArray))
           g !x !a = V.splitAt accLen $ f x a
           (xout, lout) = mapAccumR g acc0 (unravelHVector es)
       in xout V.++ ravelHVector lout
         -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: SNat k
  -> VoidHVector
  -> VoidHVector
  -> VoidHVector
  -> (HVector (ORArray) -> HVector (ORArray)
      -> HVectorOf (ORArray))
  -> HVector (ORArray)
  -> HVector (ORArray)
  -> HVector (ORArray)
oRdmapAccumL k accShs bShs _eShs f acc0 es = case sNatValue k :: Int of
  0 -> acc0 V.++ replicate1HVector k (V.map dynamicFromVoid bShs)
  _ -> let accLen = V.length accShs
           g :: HVector (ORArray) -> HVector (ORArray)
             -> (HVector (ORArray), HVector (ORArray))
           g !x !a = V.splitAt accLen $ f x a
           (xout, lout) = mapAccumL g acc0 (unravelHVector es)
       in xout V.++ ravelHVector lout

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector (ORArray) (ORArray r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector (ORArray) (ORArray Double n) #-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance ForgetShape (ORArray r n) where
  type NoShape (ORArray r n) = ORArray r n
  forgetShape = id

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector (ORArray) (OSArray r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance (GoodScalar r, KnownShS sh)
         => ForgetShape (OSArray r sh) where
  type NoShape (OSArray r sh) = ORArray r (Sh.Rank sh)  -- key case
  forgetShape t | Dict <- lemShapeFromKnownShS (Proxy @sh)
                , Dict <- lemKnownNatRank (knownShS @sh) =
    Flip $ OR.fromVector (Nested.shSToList (knownShS @sh)) $ Nested.stoVector {-Nested.rstoRanked -} (runFlipS t)

-- TODO: probably this or the next instance is eventually not needed:
instance (KnownShS sh, GoodScalar r, Fractional r, Random r, Num (Vector r))
         => RandomHVector (OSArray r sh) where
  randomVals range g | Dict <- lemShapeFromKnownShS (Proxy @sh) =
    let createRandomVector n seed =
          LA.scale (2 * realToFrac range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = Nested.sfromVector knownShS $ createRandomVector (sizeP (Proxy @sh)) g1
    in (FlipS arr, g2)

instance (KnownShS sh, Numeric r, Fractional r, Random r, Num (Vector r))
         => RandomHVector (FlipS OS.Array r sh) where
  randomVals range g | Dict <- lemShapeFromKnownShS (Proxy @sh) =
    let createRandomVector n seed =
          LA.scale (2 * realToFrac range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (sizeP (Proxy @sh)) g1
    in (FlipS arr, g2)

instance AdaptableHVector (ORArray)
                          (HVectorPseudoTensor (ORArray) r y) where
  toHVector = unHVectorPseudoTensor
  fromHVector (HVectorPseudoTensor aInit) params =
    let (portion, rest) = V.splitAt (V.length aInit) params
    in Just (HVectorPseudoTensor portion, rest)

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDeltaH
  :: VoidHVector
  -> HVector (ORArray)
  -> Maybe (HVector (ORArray))
  -> DeltaH (ORArray)
  -> HVector (ORArray) #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (ORArray) -> EvalState (ORArray) #-}

instance (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
         => DualNumberValue (DynamicTensor (ADVal ranked)) where
  type DValue (DynamicTensor (ADVal ranked)) = DynamicTensor (ORArray)
  fromDValue = \case
    DynamicRanked t -> DynamicRanked $ constantADVal $ rconst $ runFlip t
    DynamicShaped @_ @sh t | Dict <- lemShapeFromKnownShS (Proxy @sh) ->
      DynamicShaped $ constantADVal $ sconst $ OS.fromVector @sh $ Nested.stoVector $ runFlipS t
      -- TODO: this is probably very wrong
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
