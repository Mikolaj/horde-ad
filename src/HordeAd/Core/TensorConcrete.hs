{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for concrete Storable Vector-backed arrays.
module HordeAd.Core.TensorConcrete
  () where

import Prelude hiding (foldl')

import Data.Array.Internal (valueOf)
import Data.Array.RankedS qualified as OR
import Data.Array.ShapedS qualified as OS
import Data.Function ((&))
import Data.Kind (Type)
import Data.List (foldl', mapAccumL, mapAccumR, scanl')
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)
import System.Random

import Data.Array.Mixed.Shape qualified as X
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
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), FlipS (..))

type instance BoolOf (FlipR OR.Array) = Bool
type instance RankedOf (FlipR OR.Array) = FlipR OR.Array
type instance ShapedOf (FlipR OR.Array) = FlipS OS.Array
type instance HVectorOf (FlipR OR.Array) = HVector (FlipR OR.Array)
type instance PrimalOf (FlipR OR.Array) = FlipR OR.Array

type instance BoolOf (FlipS OS.Array) = Bool
type instance RankedOf (FlipS OS.Array) = FlipR OR.Array
type instance PrimalOf (FlipS OS.Array) = FlipS OS.Array

type instance BoolOf ORArray = Bool

instance EqF ORArray where
  u ==. v = u == v
  u /=. v = u /= v

instance OrdF ORArray where
  u <. v = u < v
  u <=. v = u <= v
  u >. v = u > v
  u >=. v = u >= v

instance IfF ORArray where
  ifF b v w = if b then v else w

type instance RankedOf ORArray = ORArray

type instance ShapedOf ORArray = OSArray

type instance HVectorOf ORArray = HVector ORArray

type instance HFunOf ORArray x z =
  InterpretationTarget ORArray x -> InterpretationTarget ORArray z

type instance PrimalOf ORArray = ORArray

type instance DualOf ORArray = DummyDual

type instance ShareOf ORArray = ORArray

instance LetTensor ORArray OSArray where
  rletHFunIn = (&)
  sletHFunIn = (&)
  dletHFunInHVector = (&)
  tlet :: forall x z. TensorKind x
       => InterpretationTarget ORArray x
       -> (ConcreteTarget ORArray x
           -> InterpretationTarget ORArray z)
       -> InterpretationTarget ORArray z
  tlet a f = case stensorKind @x of
    STKR{} -> f a
    STKS{} -> f a
    STKProduct{} -> f a
    STKUntyped{} -> f $ unHVectorPseudoTensor a
  blet = (&)
  toShare = id
  tunshare = id
  tconstant _ t = t
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector ORArray
       -> HVector ORArray
  rrev f _parameters0 parameters =
    -- This computes the derivative of g again for each new @parmeters@.
    let g :: InterpretationTarget (ADVal ORArray) TKUntyped
          -> InterpretationTarget (ADVal ORArray) TKUntyped
        g !hv = HVectorPseudoTensor $ V.singleton $ DynamicRanked
                $ f $ unHVectorPseudoTensor hv
    in unHVectorPseudoTensor $ fst $ crevOnHVector Nothing g
       $ HVectorPseudoTensor parameters

instance ShareTensor ORArray where
  tshare = id
  tunpair = id
  tunvector = unHVectorPseudoTensor

instance RankedTensor ORArray where
  rshape = tshapeR . runFlipR
  rminIndex = FlipR . tminIndexR . runFlipR
  rmaxIndex = FlipR . tmaxIndexR . runFlipR
  rfloor = FlipR . tfloorR . runFlipR
  rindex v ix = FlipR $ tindexZR (runFlipR v) (fromIndexOfR ix)
  rindex0 v ix = FlipR . tscalarR $ tindex0R (runFlipR v) (fromIndexOfR ix)
  rsum = FlipR . tsumR . runFlipR
  rsum0 = FlipR . tscalarR . tsum0R . runFlipR
  rdot0 u v = FlipR $ tscalarR $ tdot0R (runFlipR u) (runFlipR v)
  rmatvecmul m v = FlipR $ tmatvecmulR (runFlipR m) (runFlipR v)
  rmatmul2 m1 m2 = FlipR $ tmatmul2R (runFlipR m1) (runFlipR m2)
  rscatter sh t f = FlipR $ tscatterZR sh (runFlipR t)
                                         (fromIndexOfR . f . toIndexOfR)
  rscatter1 sh t f = FlipR $ tscatterZ1R sh (runFlipR t)
                                           (fromIndexOfR . f . FlipR . tscalarR)
  rfromList = FlipR . tfromListR . NonEmpty.map runFlipR
  rfromList0N sh = FlipR . tfromList0NR sh . map (tunScalarR . runFlipR)
  rfromVector = FlipR . tfromVectorR . V.map runFlipR
  rfromVector0N sh = FlipR . tfromVector0NR sh . V.map (tunScalarR . runFlipR)
  runravelToList = map FlipR . tunravelToListR . runFlipR
  rreplicate k = FlipR . treplicateR k . runFlipR
  rreplicate0N sh = FlipR . treplicate0NR sh . tunScalarR . runFlipR
  rappend u v = FlipR $ tappendR (runFlipR u) (runFlipR v)
  rslice i n = FlipR . tsliceR i n . runFlipR
  rreverse = FlipR . treverseR . runFlipR
  rtranspose perm = FlipR . ttransposeR perm . runFlipR
  rreshape sh = FlipR . treshapeR sh . runFlipR
  rbuild1 k f = FlipR $ tbuild1R k (runFlipR . f . FlipR . tscalarR)
  rmap0N f t = FlipR $ tmap0NR (runFlipR . f . FlipR) (runFlipR t)
  rzipWith0N f t u =
    FlipR $ tzipWith0NR (\v w -> runFlipR $ f (FlipR v) (FlipR w))
                        (runFlipR t) (runFlipR u)
  rgather sh t f = FlipR $ tgatherZR sh (runFlipR t)
                                       (fromIndexOfR . f . toIndexOfR)
  rgather1 k t f = FlipR $ tgatherZ1R k (runFlipR t)
                                       (fromIndexOfR . f . FlipR . tscalarR)
  rcast = FlipR . tcastR . runFlipR
  rfromIntegral = FlipR . tfromIntegralR . runFlipR
  rconst = FlipR
  rfromS = FlipR . Nested.stoRanked . runFlipS

  rscaleByScalar s v =
    FlipR $ tscaleByScalarR (tunScalarR $ runFlipR s) (runFlipR v)
  rdot1In u v = FlipR $ tdot1InR (runFlipR u) (runFlipR v)

  rconstant = id
  rprimalPart = id
  rdualPart _ = DummyDual
  rD u _ = u
  rScale _ _ = DummyDual

type instance BoolOf OSArray = Bool

instance EqF OSArray where
  u ==. v = u == v
  u /=. v = u /= v

instance OrdF OSArray where
  u <. v = u < v
  u <=. v = u <= v
  u >. v = u > v
  u >=. v = u >= v

instance IfF OSArray where
  ifF b v w = if b then v else w

type instance RankedOf OSArray = ORArray

type instance PrimalOf OSArray = OSArray

type instance DualOf OSArray = DummyDual

type role DummyProduct representational representational
type DummyProduct :: Type -> Type -> Type
data DummyProduct vx vz = DummyProduct vx vz

type instance InterpretationTarget DummyDual (TKProduct x z) =
  DummyProduct (InterpretationTarget DummyDual x)
               (InterpretationTarget DummyDual z)

instance ProductTensor DummyDual where
  ttuple = DummyProduct
  tproject1 (DummyProduct vx _vz) = vx
  tproject2 (DummyProduct _vx vz) = vz
  tmkHVector = error "tmkHVector of DummyDual"

instance ShapedTensor OSArray where
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
  ssum0 = FlipS . tscalarS . tsum0S . runFlipS
  sdot0 u v = FlipS $ tscalarS $ tdot0S (runFlipS u) (runFlipS v)
  smatvecmul m v = FlipS $ tmatvecmulS (runFlipS m) (runFlipS v)
  smatmul2 m1 m2 = FlipS $ tmatmul2S (runFlipS m1) (runFlipS m2)
  sscatter t f = FlipS $ tscatterZS (runFlipS t)
                                   (fromIndexOfS . f . toIndexOfS)
  sscatter1 t f = FlipS $ tscatterZ1S (runFlipS t)
                                      (fromIndexOfS . f . FlipR . tscalarR)
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
  stranspose perm = FlipS . ttransposeS perm . runFlipS
  sreshape = FlipS . treshapeS . runFlipS
  sbuild1 f = FlipS $ tbuild1S (runFlipS . f . FlipR . tscalarR)
  smap0N f t = FlipS $ tmap0NS (runFlipS . f . FlipS) (runFlipS t)
  szipWith0N f t u =
    FlipS $ tzipWith0NS (\v w -> runFlipS $ f (FlipS v) (FlipS w))
                        (runFlipS t) (runFlipS u)
  sgather t f = FlipS $ tgatherZS (runFlipS t)
                                  (fromIndexOfS . f . toIndexOfS)
  sgather1 t f = FlipS $ tgatherZ1S (runFlipS t)
                                    (fromIndexOfS . f . FlipR . tscalarR)
  scast = FlipS . tcastS . runFlipS
  sfromIntegral = FlipS . tfromIntegralS . runFlipS
  sconst = FlipS
  sfromR :: forall r sh. (GoodScalar r, KnownShS sh)
         => ORArray r (X.Rank sh) -> OSArray r sh
  sfromR = FlipS . flip Nested.rcastToShaped knownShS . runFlipR

  sscaleByScalar s v =
    FlipS $ tscaleByScalarS (tunScalarS $ runFlipS s) (runFlipS v)
  sdot1In proxy u v = FlipS $ tdot1InS proxy (runFlipS u) (runFlipS v)

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual

instance HVectorTensor ORArray OSArray where
  dshape = voidFromHVector
  tshapeFull stk t = case stk of
    STKR{} -> FTKR $ tshapeR $ runFlipR t
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (fst t))
                                       (tshapeFull stk2 (snd t))
    STKUntyped -> FTKUntyped $ voidFromHVector $ unHVectorPseudoTensor t
  tcond _ b u v = if b then u else v
  tprimalPart _ = id
  dmkHVector = id
  dlambda _ f = unHFun f  -- the eta-expansion is needed for typing
  dHApply f = f
  dunHVector = id
  dbuild1 k f =
    ravelHVector $ map (f . fromIntegral) [0 .. sNatValue k - 1]
  -- The code for drevDt and dfwd in this instance is the same as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> HFunOf ORArray (TKProduct z x) x
  drevDt _ftk h =
    let rf :: InterpretationTarget ORArray (TKProduct z x)
           -> InterpretationTarget ORArray x
        rf !db_a = fst $ crevOnHVector (Just $ fst db_a) (unHFun h) (snd db_a)
    in rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
            => TensorKindFull x
            -> HFun x z
            -> HFunOf ORArray (TKProduct x x) z
  dfwd _shs h =
    let df :: InterpretationTarget ORArray (TKProduct x x)
           -> InterpretationTarget ORArray z
        df !da_a = fst $ cfwdOnHVector (snd da_a) (unHFun h) (fst da_a)
    in df
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rscan f x0 as =
    rfromList $ NonEmpty.fromList $ scanl' f x0 (runravelToList as)
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sscan f x0 as =
    sfromList $ NonEmpty.fromList $ scanl' f x0 (sunravelToList as)
  -- The eta-expansion below is needed for typing.
  dmapAccumR _ k _ bShs _ f acc0 es = oRdmapAccumR k bShs f acc0 es
  dmapAccumRDer _ k _ bShs _ f _df _rf acc0 es =
    oRdmapAccumR k bShs (\ !a !b ->
      f (HVectorPseudoTensor a, HVectorPseudoTensor b)) acc0 es
  dmapAccumL _ k _ bShs _ f acc0 es = oRdmapAccumL k bShs f acc0 es
  dmapAccumLDer _ k _ bShs _ f _df _rf acc0 es =
    oRdmapAccumL k bShs (\ !a !b ->
      f (HVectorPseudoTensor a, HVectorPseudoTensor b)) acc0 es

type instance InterpretationTarget ORArray (TKProduct x z) =
  (InterpretationTarget ORArray x, InterpretationTarget ORArray z)

instance (Show (InterpretationTargetN ORArray x), Show (InterpretationTargetN ORArray y))
         => Show (InterpretationTargetProductN ORArray x y) where
  showsPrec d (InterpretationTargetProductN (t1, t2)) = showsPrec d (InterpretationTargetN t1, InterpretationTargetN t2)

instance ProductTensor ORArray where
  ttuple u v = (u, v)
  tproject1 = fst
  tproject2 = snd
  tmkHVector = id

oRdmapAccumR
  :: forall k accShs bShs eShs.
     (accShs ~ TKUntyped, bShs ~ TKUntyped, eShs ~ TKUntyped)
  => SNat k
  -> TensorKindFull bShs
  -> (ConcreteTarget ORArray accShs -> ConcreteTarget ORArray eShs
      -> InterpretationTarget ORArray (TKProduct accShs bShs))
  -> InterpretationTarget ORArray accShs
  -> InterpretationTarget ORArray (BuildTensorKind k eShs)
  -> InterpretationTarget ORArray (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumR k bShs f acc0 es = case sNatValue k of
  0 -> (acc0, treplicate k (stensorKind @bShs) (interpretationConstant 0 bShs))
  _ -> let g :: ConcreteTarget ORArray accShs -> ConcreteTarget ORArray eShs
             -> ( ConcreteTarget ORArray accShs
                , ConcreteTarget ORArray bShs )
           g !x !a = let (a1, b1) = f x a
                     in (unHVectorPseudoTensor a1, unHVectorPseudoTensor b1)
           (xout, lout) = mapAccumR g (unHVectorPseudoTensor acc0)
                                      (unravelHVector $ unHVectorPseudoTensor es)
       in ( HVectorPseudoTensor xout
          , HVectorPseudoTensor $ ravelHVector lout )
         -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: forall k accShs bShs eShs.
     (accShs ~ TKUntyped, bShs ~ TKUntyped, eShs ~ TKUntyped)
  => SNat k
  -> TensorKindFull bShs
  -> (ConcreteTarget ORArray accShs -> ConcreteTarget ORArray eShs
      -> InterpretationTarget ORArray (TKProduct accShs bShs))
  -> InterpretationTarget ORArray accShs
  -> InterpretationTarget ORArray (BuildTensorKind k eShs)
  -> InterpretationTarget ORArray (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumL k bShs f acc0 es = case sNatValue k of
  0 -> (acc0, treplicate k (stensorKind @bShs) (interpretationConstant 0 bShs))
  _ -> let g :: ConcreteTarget ORArray accShs -> ConcreteTarget ORArray eShs
             -> ( ConcreteTarget ORArray accShs
                , ConcreteTarget ORArray bShs )
           g !x !a = let (a1, b1) = f x a
                     in (unHVectorPseudoTensor a1, unHVectorPseudoTensor b1)
           (xout, lout) = mapAccumL g (unHVectorPseudoTensor acc0)
                                      (unravelHVector $ unHVectorPseudoTensor es)
       in ( HVectorPseudoTensor xout
          , HVectorPseudoTensor $ ravelHVector lout )

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector ORArray (ORArray r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector ORArray (ORArray Double n) #-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance ForgetShape (ORArray r n) where
  type NoShape (ORArray r n) = ORArray r n
  forgetShape = id

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector ORArray (OSArray r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance GoodScalar r
         => ForgetShape (OSArray r sh) where
  type NoShape (OSArray r sh) = ORArray r (X.Rank sh)  -- key case
  forgetShape = FlipR . Nested.stoRanked . runFlipS

instance (KnownShS sh, GoodScalar r, Fractional r, Random r)
         => RandomHVector (OSArray r sh) where
  randomVals :: forall g. RandomGen g => Double -> g -> (OSArray r sh, g)
  randomVals range g =
    let createRandomVector :: Int -> g -> OSArray r sh
        createRandomVector n seed =
          srepl (2 * realToFrac range)
          * (FlipS (Nested.sfromVector knownShS (V.fromListN n (randoms seed)))
             - srepl 0.5)
        (g1, g2) = split g
        arr = createRandomVector (sizeP (Proxy @sh)) g1
    in (arr, g2)

instance AdaptableHVector ORArray
                          (HVectorPseudoTensor ORArray r y) where
  toHVector = unHVectorPseudoTensor
  fromHVector (HVectorPseudoTensor aInit) params =
    let (portion, rest) = V.splitAt (V.length aInit) params
    in Just (HVectorPseudoTensor portion, rest)

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: TensorKindFull TKUntyped
  -> HVectorPseudoTensor ORArray Float '()
  -> Maybe (HVectorPseudoTensor ORArray Float '())
  -> Delta ORArray TKUntyped
  -> InterpretationTarget ORArray TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState ORArray -> EvalState ORArray #-}

instance ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
         , ProductTensor ranked, ShareTensor ranked
         , RankedOf (ShapedOf ranked) ~ ranked )
         => DualNumberValue (DynamicTensor (ADVal ranked)) where
  type DValue (DynamicTensor (ADVal ranked)) = DynamicTensor ORArray
  fromDValue = \case
    DynamicRanked t -> DynamicRanked $ constantADVal $ rconst $ runFlipR t
    DynamicShaped t -> DynamicShaped $ constantADVal $ sconst $ runFlipS t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2
