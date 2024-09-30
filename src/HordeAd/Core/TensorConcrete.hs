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
  Rep ORArray x -> Rep ORArray z

type instance PrimalOf ORArray = ORArray

type instance DualOf ORArray = DummyDual

type instance ShareOf ORArray = ORArray

instance LetTensor ORArray OSArray where
  rletHFunIn = (&)
  sletHFunIn = (&)
  dletHFunInHVector = (&)
  dlet :: forall x z. TensorKind x
       => Rep ORArray x
       -> (RepDeep ORArray x
           -> Rep ORArray z)
       -> Rep ORArray z
  dlet a f = case stensorKind @x of
    STKR{} -> f a
    STKS{} -> f a
    stk@STKProduct{} -> f (repDeepUnshared stk a)
    STKUntyped{} -> f $ unHVectorPseudoTensor a
  tlet :: forall x z. TensorKind x
       => Rep ORArray x
       -> (RepShallow ORArray x
           -> Rep ORArray z)
       -> Rep ORArray z
  tlet a f = case stensorKind @x of
    STKR{} -> f a
    STKS{} -> f a
    STKProduct{} -> f a
    STKUntyped{} -> f $ unHVectorPseudoTensor a
  blet = (&)
  toShare = id
  tunshare = id
  tconstant _ t = t
  taddLet t1 t2 =
    blet t1 $ \ !u1 ->
    blet t2 $ \ !u2 ->
      fromRepD $ addRepD (toRepDUnshared stensorKind u1)
                         (toRepDUnshared stensorKind u2)

instance ShareTensor ORArray where
  tshare = id
  tunpair = id
  tunvector = unHVectorPseudoTensor
  taddShare t1 t2 = fromRepD $ addRepD (toRepDShare stensorKind t1)
                                       (toRepDShare stensorKind t2)

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

type instance Rep DummyDual (TKProduct x z) =
  DummyProduct (Rep DummyDual x)
               (Rep DummyDual z)

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
  -- The code for drevDt and dfwd in this instance is similar as for the
  -- ADVal ranked instance, because the type family instance is the same.
  drev :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFunOf ORArray x x
  drev _ftk h =
    let rf :: Rep ORArray x
           -> Rep ORArray x
        rf !a = fst $ crevOnHVector Nothing (unHFun h) a
    in rf
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> HFunOf ORArray (TKProduct z x) x
  drevDt _ftk h =
    let rf :: Rep ORArray (TKProduct z x)
           -> Rep ORArray x
        rf !db_a = fst $ crevOnHVector (Just $ fst db_a) (unHFun h) (snd db_a)
    in rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
            => TensorKindFull x
            -> HFun x z
            -> HFunOf ORArray (TKProduct x x) z
  dfwd _shs h =
    let df :: Rep ORArray (TKProduct x x)
           -> Rep ORArray z
        df !da_a = fst $ cfwdOnHVector (snd da_a) (unHFun h) (fst da_a)
    in df
  rfold f x0 as = foldl' f x0 (runravelToList as)
  rscan f x0 as =
    rfromList $ NonEmpty.fromList $ scanl' f x0 (runravelToList as)
  sfold f x0 as = foldl' f x0 (sunravelToList as)
  sscan f x0 as =
    sfromList $ NonEmpty.fromList $ scanl' f x0 (sunravelToList as)
  -- The eta-expansion below is needed for typing.
  dmapAccumR _ k accShs bShs eShs f acc0 es = oRdmapAccumR k accShs bShs eShs f acc0 es
  dmapAccumRDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumR k accShs bShs eShs (\ !a !b ->
      f (unrepShallow a, unrepShallow b)) acc0 es
  dmapAccumL _ k accShs bShs eShs f acc0 es = oRdmapAccumL k accShs bShs eShs f acc0 es
  dmapAccumLDer _ k accShs bShs eShs f _df _rf acc0 es =
    oRdmapAccumL k accShs bShs eShs (\ !a !b ->
      f (unrepShallow a, unrepShallow b)) acc0 es

type instance Rep ORArray (TKProduct x z) =
  (Rep ORArray x, Rep ORArray z)

instance (Show (RepN ORArray x), Show (RepN ORArray y))
         => Show (RepProductN ORArray x y) where
  showsPrec d (RepProductN (t1, t2)) = showsPrec d (RepN t1, RepN t2)

instance ProductTensor ORArray where
  ttuple u v = (u, v)
  tproject1 = fst
  tproject2 = snd
  tmkHVector = id

ravel :: forall k y. TensorKind y
      => SNat k -> [Rep ORArray y]
      -> Rep ORArray (BuildTensorKind k y)
ravel k@SNat t = case stensorKind @y of
  STKR{} -> rfromList $ NonEmpty.fromList t
  STKS{} -> sfromList $ NonEmpty.fromList t
  STKProduct{} ->
    let (lt1, lt2) = unzip t
    in (ravel k lt1, ravel k lt2)
  STKUntyped -> HVectorPseudoTensor $ ravelHVector $ map unHVectorPseudoTensor t

unravel :: forall k y. TensorKind y
        => SNat k -> Rep ORArray (BuildTensorKind k y)
        -> [Rep ORArray y]
unravel k@SNat t = case stensorKind @y of
  STKR{} -> runravelToList t
  STKS{} -> sunravelToList t
  STKProduct{} ->
    let lt1 = unravel k $ fst t
        lt2 = unravel k $ snd t
    in zip lt1 lt2
  STKUntyped ->
    if V.null $ unHVectorPseudoTensor t
    then replicate (sNatValue k) (HVectorPseudoTensor V.empty)
    else map HVectorPseudoTensor $ unravelHVector $ unHVectorPseudoTensor t

repShallow :: forall y. TensorKind y
               => Rep ORArray y
               -> RepShallow ORArray y
repShallow t = case stensorKind @y of
  STKR{} -> t
  STKS{} -> t
  STKProduct{} -> t
  STKUntyped -> unHVectorPseudoTensor t

oRdmapAccumR
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> TensorKindFull accShs
  -> TensorKindFull bShs
  -> TensorKindFull eShs
  -> (RepShallow ORArray accShs -> RepShallow ORArray eShs
      -> Rep ORArray (TKProduct accShs bShs))
  -> Rep ORArray accShs
  -> Rep ORArray (BuildTensorKind k eShs)
  -> Rep ORArray (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumR k _ bShs _ f acc0 es = case sNatValue k of
  0 -> (acc0, treplicate k (stensorKind @bShs) (repConstant 0 bShs))
  _ ->
    let g :: RepShallow ORArray accShs -> RepShallow ORArray eShs
          -> ( RepShallow ORArray accShs
             , RepShallow ORArray bShs )
        g !x !a = let (a1, b1) = f x a
                  in (repShallow a1, repShallow b1)
        (xout, lout) = mapAccumR g (repShallow acc0)
                                   (map repShallow $ unravel k es)
    in ( unrepShallow xout
       , ravel k $ map unrepShallow lout )
      -- TODO: reimplement not with Haskell's mapAccumR to avoid the ravels

oRdmapAccumL
  :: forall k accShs bShs eShs.
     (TensorKind accShs, TensorKind bShs, TensorKind eShs)
  => SNat k
  -> TensorKindFull accShs
  -> TensorKindFull bShs
  -> TensorKindFull eShs
  -> (RepShallow ORArray accShs -> RepShallow ORArray eShs
      -> Rep ORArray (TKProduct accShs bShs))
  -> Rep ORArray accShs
  -> Rep ORArray (BuildTensorKind k eShs)
  -> Rep ORArray (TKProduct accShs (BuildTensorKind k bShs))
oRdmapAccumL k _ bShs _ f acc0 es = case sNatValue k of
  0 -> (acc0, treplicate k (stensorKind @bShs) (repConstant 0 bShs))
  _ ->
    let g :: RepShallow ORArray accShs -> RepShallow ORArray eShs
          -> ( RepShallow ORArray accShs
             , RepShallow ORArray bShs )
        g !x !a = let (a1, b1) = f x a
                  in (repShallow a1, repShallow b1)
        (xout, lout) = mapAccumL g (repShallow acc0)
                                   (map repShallow $ unravel k es)
    in ( unrepShallow xout
       , ravel k $ map unrepShallow lout )

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector ORArray (ORArray r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector ORArray (ORArray Double n) #-}
  type X (ORArray r n) = TKR r n
  toHVector = id
  fromHVector _aInit t = Just (t, Nothing)

instance (GoodScalar r, KnownNat n)
         => AdaptableHVector ORArray (AsHVector (ORArray r n)) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableHVector ORArray (AsHVector (ORArray Double n)) #-}
  type X (AsHVector (ORArray r n)) = TKUntyped
  toHVector = V.singleton . DynamicRanked . unAsHVector
  fromHVector _aInit = fromHVectorR

instance ForgetShape (ORArray r n) where
  type NoShape (ORArray r n) = ORArray r n
  forgetShape = id

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector ORArray (OSArray r sh) where
  type X (OSArray r sh) = TKS r sh
  toHVector = id
  fromHVector _aInit t = Just (t, Nothing)

instance (GoodScalar r, KnownShS sh)
         => AdaptableHVector ORArray (AsHVector (OSArray r sh)) where
  type X (AsHVector (OSArray r sh)) = TKUntyped
  toHVector = V.singleton . DynamicShaped . unAsHVector
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
                          (HVectorPseudoTensor ORArray Float '()) where
  type X (HVectorPseudoTensor ORArray Float '()) = TKUntyped
  toHVector = unHVectorPseudoTensor
  fromHVector (HVectorPseudoTensor aInit) params =
    let (portion, rest) = V.splitAt (V.length aInit) params
    in Just (HVectorPseudoTensor portion, Just rest)

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: TensorKindFull TKUntyped
  -> HVectorPseudoTensor ORArray Float '()
  -> Maybe (HVectorPseudoTensor ORArray Float '())
  -> Delta ORArray TKUntyped
  -> Rep ORArray TKUntyped #-}
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
