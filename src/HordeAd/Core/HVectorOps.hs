{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.HVectorOps
  ( toRepDShare, toRepDDuplicable, fromRepD, addRepD
  , raddDynamic, saddDynamic, sumDynamicRanked, sumDynamicShaped, addDynamic
  , sizeHVector, shapeDynamic
  , dynamicsMatch, hVectorsMatch, voidHVectorMatches, voidHVectorsMatch
  , voidFromDynamic, voidFromHVector, dynamicFromVoid
  , fromDynamicR, fromDynamicS, fromHVectorR, fromHVectorS
  , unravelHVector, ravelHVector
  , mapHVectorRanked, mapHVectorRanked01, mapHVectorRanked10, mapHVectorRanked11
  , mapHVectorShaped11, mapHVectorShaped
  , mapRanked, mapRanked01, mapRanked10, mapRanked11
  , index1HVector, replicate1HVector, mkreplicate1HVector
  , repConstant, repConstant0Old, toADTensorKindShared
  ) where

import Prelude

import Data.Array.Internal (valueOf)
import Data.List (foldl', transpose)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape (ssxFromShape)
import Data.Array.Nested (Rank)
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Adaptor
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

toRepDShare
  :: ShareTensor target
  => STensorKindType x -> target x -> RepD target x
toRepDShare stk t = case stk of
  STKScalar _ -> DTKScalar t
  STKR STKScalar{} SNat -> DTKR t
  STKS STKScalar{} sh -> withKnownShS sh $ DTKS t
  STKX STKScalar{} sh -> withKnownShX sh $ DTKX t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    let (t1, t2) = tunpair t
    in DTKProduct (toRepDShare stk1 t1) (toRepDShare stk2 t2)
  STKUntyped{} -> DTKUntyped $ tunvector t
  _ -> error "TODO"

-- The argument of the first call (but not of recursive calls)
-- is assumed to be duplicable. In AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
-- See repDeepDuplicable.
toRepDDuplicable
  :: BaseTensor target
  => STensorKindType x -> target x -> RepD target x
toRepDDuplicable stk t = case stk of
  STKScalar _ -> DTKScalar t
  STKR STKScalar{} SNat -> DTKR t
  STKS STKScalar{} sh -> withKnownShS sh $ DTKS t
  STKX STKScalar{} sh -> withKnownShX sh $ DTKX t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    DTKProduct (toRepDDuplicable stk1 (tproject1 t))
               (toRepDDuplicable stk2 (tproject2 t))
  STKUntyped{} -> DTKUntyped $ dunHVector t
  _ -> error "TODO"

fromRepD :: BaseTensor target
         => RepD target y -> target y
fromRepD = \case
  DTKScalar t -> t
  DTKR t -> t
  DTKS t -> t
  DTKX t -> t
  DTKProduct t1 t2 -> tpair (fromRepD t1) (fromRepD t2)
  DTKUntyped t -> dmkHVector t

addRepD ::
  ADReadyNoLet target
  => RepD target y
  -> RepD target y
  -> RepD target y
addRepD a b = case (a, b) of
  (DTKScalar ta, DTKScalar tb) ->
    DTKScalar $ mkRepScalar $ runRepScalar ta + runRepScalar tb
  (DTKR ta, DTKR tb) -> DTKR $ ta + tb
  (DTKS ta, DTKS tb) -> DTKS $ ta + tb
  (DTKX ta, DTKX tb) -> DTKX $ ta + tb
  (DTKProduct ta1 ta2, DTKProduct tb1 tb2) ->
    DTKProduct (addRepD ta1 tb1) (addRepD ta2 tb2)
  (DTKUntyped hv1, DTKUntyped hv2) ->
    DTKUntyped $ V.zipWith addDynamic hv1 hv2

raddDynamic :: forall target r n.
               (BaseTensor target, GoodScalar r, KnownNat n)
            => target (TKR r n) -> DynamicTensor target -> target (TKR r n)
raddDynamic !r (DynamicRanked @r2 @n2 t) = case sameNat (Proxy @n2)
                                                        (Proxy @n) of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> r + t
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"
raddDynamic r (DynamicShaped @r2 @sh2 t) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r + rfromS t
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: shape mismatch"
raddDynamic r (DynamicRankedDummy @r2 @sh2 _ _) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: target (TKR r2 (Rank sh2))
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"
raddDynamic r (DynamicShapedDummy @r2 @sh2 _ _) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: target (TKR r2 (Rank sh2))
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"

saddDynamic :: forall target sh r.
               (BaseTensor target, GoodScalar r, KnownShS sh)
            => target (TKS r sh) -> DynamicTensor target -> target (TKS r sh)
saddDynamic !r (DynamicRanked @r2 @n2 t) = case matchingRank @sh @n2 of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> r + sfromR t
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"
saddDynamic r (DynamicShaped @r2 @sh2 t) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r + t
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"
saddDynamic r (DynamicRankedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: target (TKS r2 sh2)
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"
saddDynamic r (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: target (TKS r2 sh2)
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"

sumDynamicRanked :: BaseTensor target
                 => [DynamicTensor target] -> DynamicTensor target
sumDynamicRanked [] = error "sumDynamicRanked: empty list"
sumDynamicRanked dsOrig@(d : _) =
  let dsFiltered = filter (not . isDynamicDummy) dsOrig
  in case (dsFiltered, d) of
    (DynamicRanked t : ds, _) ->
      DynamicRanked $ foldl' raddDynamic t ds
    (DynamicShaped @_ @sh t : ds, _) ->
      withListSh (Proxy @sh) $ \_ ->
        DynamicRanked $ foldl' raddDynamic (rfromS t) ds
    (_ : _, _) -> error "sumDynamicRanked: wrong filtering"
    ([], DynamicRankedDummy @r @sh _ _) ->
      withListSh (Proxy @sh) $ \sh1 ->
        DynamicRanked @r (rzero sh1)
    ([], DynamicShapedDummy @r @sh _ _) ->
      withListSh (Proxy @sh) $ \sh1 ->
        DynamicRanked @r (rzero sh1)
    ([], _) -> error "sumDynamicRanked: wrong filtering"

sumDynamicShaped :: BaseTensor target
                 => [DynamicTensor target]
                 -> DynamicTensor target
sumDynamicShaped [] = error "sumDynamicShaped: empty list"
sumDynamicShaped dsOrig@(d : _) =
  let dsFiltered = filter (not . isDynamicDummy) dsOrig
  in case (dsFiltered, d) of
    (DynamicRanked @_ @n t : ds, _) ->
      withShapeP (shapeToList $ rshape t) $ \(Proxy @sh) ->
        gcastWith (unsafeCoerce Refl :: Rank sh :~: n) $
        DynamicShaped $ foldl' saddDynamic (sfromR @_ @_ @sh t) ds
    (DynamicShaped t : ds, _) ->
      DynamicShaped $ foldl' saddDynamic t ds
    (_ : _, _) -> error "sumDynamicShaped: wrong filtering"
    ([], DynamicRankedDummy @r @sh _ _) ->
      DynamicShaped @r @sh (srepl 0)
    ([], DynamicShapedDummy @r @sh _ _) ->
      DynamicShaped @r @sh (srepl 0)
    ([], _) -> error "sumDynamicShaped: wrong filtering"

addDynamic :: forall target.
              (BaseTensor target, CRanked target Show)
           => DynamicTensor target -> DynamicTensor target
           -> DynamicTensor target
addDynamic (DynamicRanked @r1 @n1 t) (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameNat (Proxy @n1) (Proxy @n2) =
    DynamicRanked $ t + t'
addDynamic (DynamicShaped @r1 @sh1 t) (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped $ t + t'
addDynamic DynamicRankedDummy{} u@DynamicRanked{} = u
addDynamic DynamicRankedDummy{} u@DynamicRankedDummy{} = u
addDynamic t@DynamicRanked{} DynamicRankedDummy{} = t
addDynamic DynamicShapedDummy{} u@DynamicShaped{} = u
addDynamic DynamicShapedDummy{} u@DynamicShapedDummy{} = u
addDynamic t@DynamicShaped{} DynamicShapedDummy{} = t
addDynamic t u = error $ "addDynamic: wrong arguments: " ++ show (t, u)

sizeHVector :: forall target. BaseTensor target => HVector target -> Int
sizeHVector = let f (DynamicRanked @r t) = rsize @target @r t
                  f (DynamicShaped @_ @sh _) = sizeT @sh
                  f (DynamicRankedDummy _ proxy_sh) = sizeP proxy_sh
                  f (DynamicShapedDummy _ proxy_sh) = sizeP proxy_sh
              in V.sum . V.map f

shapeDynamic :: BaseTensor target
             => DynamicTensor target -> [Int]
shapeDynamic = shapeDynamicF (shapeToList . rshape)

dynamicsMatch :: forall f g. (BaseTensor f, BaseTensor g)
              => DynamicTensor f -> DynamicTensor g -> Bool
dynamicsMatch t u = case (scalarDynamic t, scalarDynamic @g u) of
  (DynamicScalar @ru _, DynamicScalar @rt _) ->
    isJust (testEquality (typeRep @rt) (typeRep @ru))
    && shapeDynamic t == shapeDynamic @g u
    && isDynamicRanked t == isDynamicRanked @g u

hVectorsMatch :: forall f g. (BaseTensor f, BaseTensor g)
              => HVector f -> HVector g -> Bool
hVectorsMatch v1 v2 =
  V.length v1 == V.length v2
  && and (V.zipWith dynamicsMatch v1 v2)

voidHVectorMatches :: forall g. BaseTensor g
                   => HVector VoidTensor -> HVector g -> Bool
voidHVectorMatches v1 v2 =
  let voidDynamicsMatch :: DynamicTensor VoidTensor -> DynamicTensor g -> Bool
      voidDynamicsMatch t u = case (scalarDynamic t, scalarDynamic @g u) of
        (DynamicScalar @ru _, DynamicScalar @rt _) ->
          isJust (testEquality (typeRep @rt) (typeRep @ru))
          && shapeVoidDynamic t == shapeDynamic @g u
          && isDynamicRanked t == isDynamicRanked @g u
  in V.length v1 == V.length v2
     && and (V.zipWith voidDynamicsMatch v1 v2)

voidHVectorsMatch :: HVector VoidTensor -> HVector VoidTensor -> Bool
voidHVectorsMatch v1 v2 =
  let voidDynamicsMatch :: DynamicTensor VoidTensor -> DynamicTensor VoidTensor
                        -> Bool
      voidDynamicsMatch t u = case (scalarDynamic t, scalarDynamic u) of
        (DynamicScalar @ru _, DynamicScalar @rt _) ->
          isJust (testEquality (typeRep @rt) (typeRep @ru))
          && shapeVoidDynamic t == shapeVoidDynamic u
          && isDynamicRanked t == isDynamicRanked u
  in V.length v1 == V.length v2
     && and (V.zipWith voidDynamicsMatch v1 v2)

-- This is useful for when the normal main parameters to an objective
-- function are used to generate the parameter template
-- as well as when generating dummy zero parameters based on a template.
voidFromDynamic :: forall target. BaseTensor target
                => DynamicTensor target -> DynamicTensor VoidTensor
voidFromDynamic = voidFromDynamicF (shapeToList . rshape)

voidFromHVector :: forall target. BaseTensor target
                => HVector target -> VoidHVector
voidFromHVector = V.map voidFromDynamic

dynamicFromVoid :: DynamicTensor VoidTensor -> DynamicTensor target
dynamicFromVoid (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
dynamicFromVoid (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2

fromDynamicR :: forall r n target.
                (GoodScalar r, KnownNat n)
             => (IShR n -> target (TKR r n)) -> DynamicTensor target
             -> target (TKR r n)
fromDynamicR zero = \case
  DynamicRanked @r2 @n2 t -> case sameNat (Proxy @n2) (Proxy @n) of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> t
      _ -> error $ "fromDynamicR: scalar mismatch in "
                   ++ show (typeRep @r2, typeRep @r)
    _ -> error "fromDynamicR: rank mismatch"
  DynamicShaped{} -> error "fromDynamicR: ranked from shaped"
  DynamicRankedDummy @r2 @sh2 _ _ -> case matchingRank @sh2 @n of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> let sh2 = listToShape (shapeT @sh2)
                   in zero sh2
      _ -> error "fromDynamicR: scalar mismatch"
    _ -> error "fromDynamicR: shape mismatch"
  DynamicShapedDummy{} -> error "fromDynamicR: ranked from shaped"

fromDynamicS :: forall r sh target.
                (GoodScalar r, KnownShS sh)
             => target (TKS r sh) -> DynamicTensor target
             -> target (TKS r sh)
fromDynamicS zero = \case
  DynamicRanked{} -> error "fromDynamicS: shaped from ranked"
  DynamicShaped @r2 @sh2 t -> case sameShape @sh2 @sh of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> t
      _ -> error "fromDynamicS: scalar mismatch"
    _ -> error "fromDynamicS: shape mismatch"
  DynamicRankedDummy{} -> error "fromDynamicS: shaped from ranked"
  DynamicShapedDummy @r2 @sh2 _ _ -> case sameShape @sh2 @sh of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> zero
      _ -> error "fromDynamicS: scalar mismatch"
    _ -> error "fromDynamicS: shape mismatch"

fromHVectorR :: forall r n target.
                (BaseTensor target, GoodScalar r, KnownNat n)
             => HVectorOf target
             -> Maybe (AsHVector (target (TKR r n)), Maybe (HVectorOf target))
fromHVectorR params = case V.uncons $ dunHVector2 params of
  Just (dynamic, rest) ->
    Just (AsHVector $ fromDynamicR rzero dynamic, Just $ dmkHVector2 rest)
  Nothing -> Nothing

fromHVectorS :: forall r sh target.
                (BaseTensor target, GoodScalar r, KnownShS sh)
             => HVectorOf target
             -> Maybe (AsHVector (target (TKS r sh)), Maybe (HVectorOf target))
fromHVectorS params = case V.uncons $ dunHVector2 $ params of
  Just (dynamic, rest) ->
    Just (AsHVector $ fromDynamicS (srepl 0) dynamic, Just $ dmkHVector2 rest)
  Nothing -> Nothing

unravelDynamic
  :: forall target. BaseTensor target
  => DynamicTensor target -> [DynamicTensor target]
unravelDynamic (DynamicRanked @rp @p t) =
  case someNatVal $ valueOf @p - 1 of
    Just (SomeNat @p1 _) ->
      gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
      map (DynamicRanked @rp @p1) $ runravelToList t
    Nothing -> error "unravelDynamic: rank 0"
unravelDynamic (DynamicShaped @_ @sh t) = case knownShS @sh of
  ZSS -> error "unravelDynamic: rank 0"
  (:$$) SNat tl | Dict <- sshapeKnown tl -> map DynamicShaped $ sunravelToList t
unravelDynamic (DynamicRankedDummy @rp @sh _ _) =
  withListSh (Proxy @sh) $ \(sh :: IShR p) ->
    case someNatVal $ valueOf @p - 1 of
      Just (SomeNat @p1 _) ->
        gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
        map (DynamicRanked @rp @p1) $ runravelToList (rzero sh)
      Nothing -> error "unravelDynamic: rank 0"
unravelDynamic (DynamicShapedDummy @rp @sh _ _) = case knownShS @sh of
  ZSS -> error "unravelDynamic: rank 0"
  (:$$) SNat tl | Dict <- sshapeKnown tl ->
    map DynamicShaped $ sunravelToList (srepl 0 :: target (TKS rp sh))

unravelHVector
  :: forall target. BaseTensor target
  => HVector target  -- each tensor has outermost dimension size p
  -> [HVector target]  -- p hVectors; each tensor of one rank lower
unravelHVector = map V.fromList . transpose
                 . map unravelDynamic . V.toList

ravelDynamicRanked
  :: forall target. BaseTensor target
  => [DynamicTensor target] -> DynamicTensor target
ravelDynamicRanked ld = case ld of
  [] -> error "ravelDynamicRanked: empty list"
  d : _ -> case ( someNatVal $ toInteger (length $ shapeDynamic d)
                , scalarDynamic d ) of
    (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
      let g :: DynamicTensor target -> target (TKR rp p1)
          g (DynamicRanked @rq @q t)
            | Just Refl <- sameNat (Proxy @q) (Proxy @p1)
            , Just Refl <- testEquality (typeRep @rq) (typeRep @rp) = t
          g DynamicShaped{} =
            error "ravelDynamicRanked: DynamicShaped"
          g (DynamicRankedDummy @rq @shq _ _)
            | Just Refl <- matchingRank @shq @p1
            , Just Refl <- testEquality (typeRep @rq) (typeRep @rp) =
                withListSh (Proxy @shq) $ \(sh :: IShR q1) ->
                  case sameNat (Proxy @q1) (Proxy @p1) of
                    Just Refl -> rzero @target sh
                    Nothing -> error "ravelDynamicRanked: wrong rank"
          g DynamicShapedDummy{} =
            error "ravelDynamicRanked: DynamicShapedDummy"
          g _ = error "ravelDynamicRanked: wrong scalar or rank"
      in DynamicRanked $ rfromList $ NonEmpty.fromList $ map g ld
    _ -> error "ravelDynamicRanked: impossible someNatVal"

ravelDynamicShaped
  :: forall target. BaseTensor target
  => [DynamicTensor target] -> DynamicTensor target
ravelDynamicShaped ld = case ld of
  [] -> error "ravelDynamicShaped: empty list"
  d : _ ->
    withShapeP (shapeDynamic d)
    $ \(Proxy @shp) -> case ( someNatVal $ toInteger $ length ld
                            , scalarDynamic d ) of
      (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
        let g :: DynamicTensor target -> target (TKS rp shp)
            g DynamicRanked{} =
              error "ravelDynamicShaped: DynamicRanked"
            g (DynamicShaped @rq @shq t)
              | Just Refl <- sameShape @shq @shp
              , Just Refl <- testEquality (typeRep @rq) (typeRep @rp) = t
            g DynamicRankedDummy{} =
              error "ravelDynamicShaped: DynamicRankedDummy"
            g (DynamicShapedDummy @rq @shq _ _)
              | Just Refl <- sameShape @shq @shp
              , Just Refl <- testEquality (typeRep @rq) (typeRep @rp) = srepl 0
            g _ = error "ravelDynamicShaped: wrong scalar or rank"
        in DynamicShaped $ sfromList @_ @_ @p1 $ NonEmpty.fromList $ map g ld
      _ -> error "ravelDynamicShaped: impossible someNatVal"

ravelDynamic
  :: BaseTensor target
  => [DynamicTensor target] -> DynamicTensor target
ravelDynamic ld = case ld of
  [] -> error "ravelDynamic: empty list"
  DynamicRanked{} : _ -> ravelDynamicRanked ld
  DynamicShaped{} : _ -> ravelDynamicShaped ld
  DynamicRankedDummy{} : _ -> ravelDynamicRanked ld
  DynamicShapedDummy{} : _ -> ravelDynamicShaped ld

ravelHVector  -- the inverse of unravelHVector
  :: BaseTensor target
  => [HVector target] -> HVector target
ravelHVector = V.fromList . map ravelDynamic
               . transpose . map V.toList

mapHVectorRanked
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq q) -> target (TKR rq q))
  -> HVector target -> HVector target
mapHVectorRanked f = V.map (mapRanked f)

mapRanked
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq q) -> target (TKR rq q))
  -> DynamicTensor target -> DynamicTensor target
mapRanked f (DynamicRanked t) = DynamicRanked $ f t
mapRanked f (DynamicShaped @_ @sh t) =
  withListSh (Proxy @sh) $ \(_ :: IShR n) ->
    let res = f $ rfromS @_ @_ @sh t
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res
mapRanked f (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh1 ->
    DynamicRanked @r $ f (rzero sh1)
mapRanked f (DynamicShapedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \(sh1 :: IShR n) ->
    let res = f @r (rzero sh1)
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res

-- Hindler-Milner polymorphism is not great for existential types programming.
mapHVectorRanked01
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq q) -> target (TKR rq (1 + q)))
  -> HVector target -> HVector target
mapHVectorRanked01 f = V.map (mapRanked01 f)

mapRanked01
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq q) -> target (TKR rq (1 + q)))
  -> DynamicTensor target -> DynamicTensor target
mapRanked01 f (DynamicRanked t) = DynamicRanked $ f t
mapRanked01 f (DynamicShaped @_ @sh t) =
  withListSh (Proxy @sh) $ \(_ :: IShR n) ->
    let res = f $ rfromS @_ @_ @sh t
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
      case someNatVal $ 1 + valueOf @n of
        Just (SomeNat @n1 _) ->
          gcastWith (unsafeCoerce Refl :: n1 :~: 1 + n) $
          gcastWith (unsafeCoerce Refl :: Rank shr :~: n1) $
          DynamicShaped $ sfromR @_ @_ @shr res
        _ -> error "mapRanked01: impossible someNatVal"
mapRanked01 f (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh1 ->
    DynamicRanked @r $ f (rzero sh1)
mapRanked01 f (DynamicShapedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \(sh1 :: IShR n) ->
    let res = f @r (rzero sh1)
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
      case someNatVal $ 1 + valueOf @n of
        Just (SomeNat @n1 _) ->
          gcastWith (unsafeCoerce Refl :: n1 :~: 1 + n) $
          gcastWith (unsafeCoerce Refl :: Rank shr :~: n1) $
          DynamicShaped $ sfromR @_ @_ @shr res
        _ -> error "mapRanked01: impossible someNatVal"

mapHVectorRanked10
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq (1 + q)) -> target (TKR rq q))
  -> HVector target -> HVector target
mapHVectorRanked10 f = V.map (mapRanked10 f)

mapRanked10
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq (1 + q)) -> target (TKR rq q))
  -> DynamicTensor target -> DynamicTensor target
mapRanked10 f (DynamicRanked t) = case rshape t of
  ZSR -> error "mapRanked10: rank 0"
  _ :$: _ -> DynamicRanked $ f t
mapRanked10 f (DynamicShaped @_ @sh t) = case knownShS @sh of
  ZSS -> error "mapRanked10: rank 0"
  (:$$) @_ @sh0 _ tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \(_ :: IShR n) ->
      let res = f $ rfromS @_ @_ @sh t
      in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res
mapRanked10 f (DynamicRankedDummy @r @sh _ _) = case knownShS @sh of
  ZSS -> error "mapRanked10: rank 0"
  (:$$) @_ @sh0 k tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \sh1 ->
      DynamicRanked @r $ f (rzero $ sNatValue k :$: sh1)
mapRanked10 f (DynamicShapedDummy @r @sh _ _) = case knownShS @sh of
  ZSS -> error "mapRanked10: rank 0"
  (:$$) @_ @sh0 k tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \(sh1 :: IShR n) ->
      let res = f @r (rzero $ sNatValue k :$: sh1)
      in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res

mapHVectorRanked11
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq (1 + q)) -> target (TKR rq (1 + q)))
  -> HVector target -> HVector target
mapHVectorRanked11 f = V.map (mapRanked11 f)

mapRanked11
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR rq (1 + q)) -> target (TKR rq (1 + q)))
  -> DynamicTensor target -> DynamicTensor target
mapRanked11 f (DynamicRanked t) = case rshape t of
  ZSR -> error "mapRanked11: rank 0"
  _ :$: _ -> DynamicRanked $ f t
mapRanked11 f (DynamicShaped @_ @sh t) = case knownShS @sh of
  ZSS -> error "mapRanked11: rank 0"
  (:$$) @_ @sh0 _ tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \(_ :: IShR n) ->
      let res = f $ rfromS @_ @_ @sh t
      in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        case someNatVal $ 1 + valueOf @n of
          Just (SomeNat @n1 _) ->
            gcastWith (unsafeCoerce Refl :: n1 :~: 1 + n) $
            gcastWith (unsafeCoerce Refl :: Rank shr :~: n1) $
            DynamicShaped $ sfromR @_ @_ @shr res
          _ -> error "mapRanked01: impossible someNatVal"
mapRanked11 f (DynamicRankedDummy @r @sh _ _) = case knownShS @sh of
  ZSS -> error "mapRanked11: rank 0"
  (:$$) @_ @sh0 k tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \sh1 ->
      DynamicRanked @r $ f (rzero $ sNatValue k :$: sh1)
mapRanked11 f (DynamicShapedDummy @r @sh _ _) = case knownShS @sh of
  ZSS -> error "mapRanked11: rank 0"
  (:$$) @_ @sh0 k tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \(sh1 :: IShR n) ->
      let res = f @r (rzero $ sNatValue k :$: sh1)
      in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        case someNatVal $ 1 + valueOf @n of
          Just (SomeNat @n1 _) ->
            gcastWith (unsafeCoerce Refl :: n1 :~: 1 + n) $
            gcastWith (unsafeCoerce Refl :: Rank shr :~: n1) $
            DynamicShaped $ sfromR @_ @_ @shr res
          _ -> error "mapRanked01: impossible someNatVal"

mapHVectorShaped
  :: forall target.
     BaseTensor target
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS rq shq) -> target (TKS rq shq))
  -> HVector target -> HVector target
mapHVectorShaped f = V.map (mapShaped f)

mapShaped
  :: forall target.
     BaseTensor target
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS rq shq) -> target (TKS rq shq))
  -> DynamicTensor target -> DynamicTensor target
mapShaped f (DynamicRanked @r @n t) =
  withShapeP (shapeToList $ rshape t) $ \(Proxy @sh) ->
    withListSh (Proxy @sh) $ \(_ :: IShR m) ->
      gcastWith (unsafeCoerce Refl :: n :~: m) $
      DynamicRanked $ rfromS $ f @r @sh $ sfromR t
mapShaped f (DynamicShaped t) = DynamicShaped $ f t
mapShaped f (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \_ ->
    DynamicRanked $ rfromS $ f @r @sh (srepl 0)
mapShaped f (DynamicShapedDummy @r @sh _ _) = DynamicShaped $ f @r @sh (srepl 0)

mapHVectorShaped11
  :: forall k k1 target.
     (BaseTensor target, KnownNat k, KnownNat k1)
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS rq (k ': shq)) -> target (TKS rq (k1 ': shq)))
  -> HVector target -> HVector target
mapHVectorShaped11 f = V.map (mapShaped11 f)

mapShaped11
  :: forall k k1 target.
     (BaseTensor target, KnownNat k, KnownNat k1)
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS rq (k ': shq)) -> target (TKS rq (k1 ': shq)))
  -> DynamicTensor target -> DynamicTensor target
mapShaped11 f (DynamicRanked @r @n2 t) =
  withShapeP (shapeToList $ rshape t) $ \(Proxy @sh) ->
    case knownShS @sh of
      ZSS -> error "mapShaped11: rank 0"
      (:$$) @n @shr SNat tl
        | Dict <- sshapeKnown tl -> case sameNat (Proxy @n) (Proxy @k) of
          Just Refl -> withListSh (Proxy @shr) $ \(_ :: IShR m) ->
            gcastWith (unsafeCoerce Refl :: n2 :~: 1 + m) $
            DynamicRanked $ rfromS $ f @r @shr $ sfromR t
          Nothing -> error "mapShaped11: wrong width"
mapShaped11 f (DynamicShaped t) = case sshape t of
  ZSS -> error "mapShaped11: rank 0"
  (:$$) @n SNat tl
    | Dict <- sshapeKnown tl -> case sameNat (Proxy @n) (Proxy @k) of
      Just Refl -> DynamicShaped $ f t
      Nothing -> error "mapShaped11: wrong width"
mapShaped11 f (DynamicRankedDummy @r @sh _ _) =
  case knownShS @sh of
    ZSS -> error "mapShaped11: rank 0"
    (:$$) @n @shr SNat tl
      | Dict <- sshapeKnown tl -> case sameNat (Proxy @n) (Proxy @k) of
        Just Refl -> withListSh (Proxy @shr) $ \_ ->
          DynamicRanked $ rfromS $ f @r @shr (srepl 0)
        Nothing -> error "mapShaped11: wrong width"
mapShaped11 f (DynamicShapedDummy @r @sh _ _) =
  case knownShS @sh of
    ZSS -> error "mapShaped11: rank 0"
    (:$$) @n @shr SNat tl
      | Dict <- sshapeKnown tl -> case sameNat (Proxy @n) (Proxy @k) of
        Just Refl -> DynamicShaped $ f @r @shr (srepl 0)
        Nothing -> error "mapShaped11: wrong width"

index1HVector :: BaseTensor target
              => HVector target -> IntOf target -> HVector target
index1HVector = index1HVectorF rshape sshape rindex sindex

replicate1HVector :: BaseTensor target
                  => SNat k -> HVector target -> HVector target
replicate1HVector = replicate1HVectorF rreplicate sreplicate

mkreplicate1HVector :: ADReady target
                    => SNat k -> HVector target -> HVectorOf target
mkreplicate1HVector k = dmkHVector2 . replicate1HVector k

repConstant :: forall y target. ADReadyNoLet target
            => (forall r. GoodScalar r => r)
            -> TensorKindFull y -> target y
repConstant r = \case
  FTKScalar -> mkRepScalar $ rscalar r
  FTKR sh | SNat <- shrRank sh -> rrepl (toList sh) r
  FTKS sh -> withKnownShS sh $ srepl r
  FTKX sh -> withKnownShX (ssxFromShape sh) $ xrepl sh r
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                       , Dict <- lemTensorKindOfF ftk2 ->
    tpair (repConstant r ftk1)
          (repConstant r ftk2)
  FTKUntyped ssh ->  -- TODO: if r is 0, this would be cheaper with Dummy
    dmkHVector
    $ mapHVectorShaped (const $ srepl @_ @_ @target r)
    $ V.map dynamicFromVoid ssh

repConstant0Old :: forall y target. ADReadyNoLet target
                => TensorKindFull y -> target y
repConstant0Old = \case
  FTKScalar -> mkRepScalar $ rscalar 0
  FTKR sh | SNat <- shrRank sh -> rzero sh
  FTKS sh -> withKnownShS sh $ srepl 0
  FTKX sh -> withKnownShX (ssxFromShape sh) $ xzero sh
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfF ftk1
                       , Dict <- lemTensorKindOfF ftk2 ->
    tpair (repConstant0Old ftk1)
          (repConstant0Old ftk2)
  FTKUntyped ssh -> dmkHVector $ V.map dynamicFromVoid ssh

toADTensorKindShared
  :: forall target y. (BaseTensor target, ShareTensor target)
  => STensorKindType y -> target y
  -> target (ADTensorKind y)
toADTensorKindShared stk t = case stk of
  STKScalar @r _ -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           mkRepScalar $ rscalar ()
  STKR (STKScalar @r _) SNat -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           rrepl @_ @_ @target (toList $ rshape t) ()
  STKS @_ @sh (STKScalar @r _) sh -> withKnownShS sh
                      $ case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           srepl @sh @() @target ()
  STKX (STKScalar @r _) sh -> withKnownShX sh
                  $ case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: ()) $
           xrepl @_ @_ @target (xshape t) ()
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2
                       , Dict <- lemTensorKindOfAD stk1
                       , Dict <- lemTensorKindOfAD stk2 ->
    let (t1, t2) = tunpair t
    in tpair (toADTensorKindShared stk1 t1) (toADTensorKindShared stk2 t2)
  STKUntyped -> t
  _ -> error "TODO"
