{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.HVectorOps
  ( raddDynamic, saddDynamic, sumDynamicRanked, sumDynamicShaped, addDynamic
  , sizeHVector, shapeDynamic
  , dynamicsMatch, hVectorsMatch, voidHVectorMatches, voidHVectorsMatch
  , voidFromDynamic, voidFromHVector, dynamicFromVoid
  , fromDynamicR, fromDynamicS, fromHVectorR, fromHVectorS
  , unravelHVector, ravelHVector
  , mapHVectorRanked, mapHVectorRanked01, mapHVectorRanked10, mapHVectorRanked11
  , mapHVectorShaped11, mapHVectorShaped
  , mapRanked, mapRanked01, mapRanked10, mapRanked11
  , index1HVector, replicate1HVector, mkreplicate1HVector
  , interpretationConstant
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

import Data.Array.Mixed.Shape qualified as X

import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

raddDynamic :: forall ranked r n.
               (RankedTensor ranked, GoodScalar r, KnownNat n)
            => ranked r n -> DynamicTensor ranked -> ranked r n
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
    Just Refl -> r :: ranked r2 (X.Rank sh2)
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"
raddDynamic r (DynamicShapedDummy @r2 @sh2 _ _) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: ranked r2 (X.Rank sh2)
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"

saddDynamic :: forall shaped sh r.
               ( ShapedTensor shaped, GoodScalar r, KnownShS sh
               , ShapedOf (RankedOf shaped) ~ shaped )
            => shaped r sh -> DynamicTensor (RankedOf shaped) -> shaped r sh
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
    Just Refl -> r :: shaped r2 sh2
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"
saddDynamic r (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: shaped r2 sh2
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"

sumDynamicRanked :: RankedTensor ranked
                 => [DynamicTensor ranked] -> DynamicTensor ranked
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

sumDynamicShaped :: ( RankedTensor (RankedOf shaped), ShapedTensor shaped
                    , ShapedOf (RankedOf shaped) ~ shaped )
                 => [DynamicTensor (RankedOf shaped)]
                 -> DynamicTensor (RankedOf shaped)
sumDynamicShaped [] = error "sumDynamicShaped: empty list"
sumDynamicShaped dsOrig@(d : _) =
  let dsFiltered = filter (not . isDynamicDummy) dsOrig
  in case (dsFiltered, d) of
    (DynamicRanked @_ @n t : ds, _) ->
      withShapeP (shapeToList $ rshape t) $ \(Proxy @sh) ->
        gcastWith (unsafeCoerce Refl :: X.Rank sh :~: n) $
        DynamicShaped $ foldl' saddDynamic (sfromR @_ @_ @sh t) ds
    (DynamicShaped t : ds, _) ->
      DynamicShaped $ foldl' saddDynamic t ds
    (_ : _, _) -> error "sumDynamicShaped: wrong filtering"
    ([], DynamicRankedDummy @r @sh _ _) ->
      DynamicShaped @r @sh (srepl 0)
    ([], DynamicShapedDummy @r @sh _ _) ->
      DynamicShaped @r @sh (srepl 0)
    ([], _) -> error "sumDynamicShaped: wrong filtering"

addDynamic :: forall ranked.
              ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
              , CRanked ranked Show, CShaped (ShapedOf ranked) Show )
           => DynamicTensor ranked -> DynamicTensor ranked
           -> DynamicTensor ranked
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

sizeHVector :: forall ranked. RankedTensor ranked => HVector ranked -> Int
sizeHVector = let f (DynamicRanked @r t) = rsize @ranked @r t
                  f (DynamicShaped @_ @sh _) = sizeT @sh
                  f (DynamicRankedDummy _ proxy_sh) = sizeP proxy_sh
                  f (DynamicShapedDummy _ proxy_sh) = sizeP proxy_sh
              in V.sum . V.map f

shapeDynamic :: RankedTensor ranked
             => DynamicTensor ranked -> [Int]
shapeDynamic = shapeDynamicF (shapeToList . rshape)

dynamicsMatch :: forall f g. (RankedTensor f, RankedTensor g)
              => DynamicTensor f -> DynamicTensor g -> Bool
dynamicsMatch t u = case (scalarDynamic t, scalarDynamic @g u) of
  (DynamicScalar @ru _, DynamicScalar @rt _) ->
    isJust (testEquality (typeRep @rt) (typeRep @ru))
    && shapeDynamic t == shapeDynamic @g u
    && isDynamicRanked t == isDynamicRanked @g u

hVectorsMatch :: forall f g. (RankedTensor f, RankedTensor g)
              => HVector f -> HVector g -> Bool
hVectorsMatch v1 v2 =
  V.length v1 == V.length v2
  && and (V.zipWith dynamicsMatch v1 v2)

voidHVectorMatches :: forall g. RankedTensor g
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
voidFromDynamic :: forall ranked. RankedTensor ranked
                => DynamicTensor ranked -> DynamicTensor VoidTensor
voidFromDynamic = voidFromDynamicF (shapeToList . rshape)

voidFromHVector :: forall ranked. RankedTensor ranked
                => HVector ranked -> VoidHVector
voidFromHVector = V.map voidFromDynamic

dynamicFromVoid :: DynamicTensor VoidTensor -> DynamicTensor ranked
dynamicFromVoid (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
dynamicFromVoid (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2

fromDynamicR :: forall r n ranked.
                (GoodScalar r, KnownNat n)
             => (IShR n -> ranked r n) -> DynamicTensor ranked
             -> ranked r n
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

fromDynamicS :: forall r sh shaped
              . ( GoodScalar r, KnownShS sh
                , ShapedOf (RankedOf shaped) ~ shaped )
             => shaped r sh -> DynamicTensor (RankedOf shaped)
             -> shaped r sh
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

fromHVectorR :: forall r n ranked.
                (RankedTensor ranked, GoodScalar r, KnownNat n)
             => HVector ranked
             -> Maybe (ranked r n, HVector ranked)
fromHVectorR params = case V.uncons params of
  Just (dynamic, rest) -> Just (fromDynamicR rzero dynamic, rest)
  Nothing -> Nothing

fromHVectorS :: forall r sh shaped
              . ( ShapedTensor shaped, GoodScalar r, KnownShS sh
                , ShapedOf (RankedOf shaped) ~ shaped )
             => HVector (RankedOf shaped)
             -> Maybe (shaped r sh,  HVector (RankedOf shaped))
fromHVectorS params = case V.uncons params of
  Just (dynamic, rest) -> Just (fromDynamicS (srepl 0) dynamic, rest)
  Nothing -> Nothing

unravelDynamic
  :: forall ranked. (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => DynamicTensor ranked -> [DynamicTensor ranked]
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
    map DynamicShaped $ sunravelToList (srepl 0 :: ShapedOf ranked rp sh)

unravelHVector
  :: forall ranked. (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => HVector ranked  -- each tensor has outermost dimension size p
  -> [HVector ranked]  -- p hVectors; each tensor of one rank lower
unravelHVector = map V.fromList . transpose
                 . map unravelDynamic . V.toList

ravelDynamicRanked
  :: forall ranked. RankedTensor ranked
  => [DynamicTensor ranked] -> DynamicTensor ranked
ravelDynamicRanked ld = case ld of
  [] -> error "ravelDynamicRanked: empty list"
  d : _ -> case ( someNatVal $ toInteger (length $ shapeDynamic d)
                , scalarDynamic d ) of
    (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
      let g :: DynamicTensor ranked -> ranked rp p1
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
                    Just Refl -> rzero @ranked sh
                    Nothing -> error "ravelDynamicRanked: wrong rank"
          g DynamicShapedDummy{} =
            error "ravelDynamicRanked: DynamicShapedDummy"
          g _ = error "ravelDynamicRanked: wrong scalar or rank"
      in DynamicRanked $ rfromList $ NonEmpty.fromList $ map g ld
    _ -> error "ravelDynamicRanked: impossible someNatVal"

ravelDynamicShaped
  :: forall shaped.
     ( RankedTensor (RankedOf shaped), ShapedTensor shaped
     , ShapedOf (RankedOf shaped) ~ shaped )
  => [DynamicTensor (RankedOf shaped)] -> DynamicTensor (RankedOf shaped)
ravelDynamicShaped ld = case ld of
  [] -> error "ravelDynamicShaped: empty list"
  d : _ ->
    withShapeP (shapeDynamic d)
    $ \(Proxy @shp) -> case ( someNatVal $ toInteger $ length ld
                            , scalarDynamic d ) of
      (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
        let g :: DynamicTensor (RankedOf shaped) -> shaped rp shp
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
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => [DynamicTensor ranked] -> DynamicTensor ranked
ravelDynamic ld = case ld of
  [] -> error "ravelDynamic: empty list"
  DynamicRanked{} : _ -> ravelDynamicRanked ld
  DynamicShaped{} : _ -> ravelDynamicShaped ld
  DynamicRankedDummy{} : _ -> ravelDynamicRanked ld
  DynamicShapedDummy{} : _ -> ravelDynamicShaped ld

ravelHVector  -- the inverse of unravelHVector
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => [HVector ranked] -> HVector ranked
ravelHVector = V.fromList . map ravelDynamic
               . transpose . map V.toList

mapHVectorRanked
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq q)
  -> HVector ranked -> HVector ranked
mapHVectorRanked f = V.map (mapRanked f)

mapRanked
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq q)
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked f (DynamicRanked t) = DynamicRanked $ f t
mapRanked f (DynamicShaped @_ @sh t) =
  withListSh (Proxy @sh) $ \(_ :: IShR n) ->
    let res = f $ rfromS @_ @_ @sh t
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res
mapRanked f (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh1 ->
    DynamicRanked @r $ f (rzero sh1)
mapRanked f (DynamicShapedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \(sh1 :: IShR n) ->
    let res = f @r (rzero sh1)
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res

-- Hindler-Milner polymorphism is not great for existential types programming.
mapHVectorRanked01
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq (1 + q))
  -> HVector ranked -> HVector ranked
mapHVectorRanked01 f = V.map (mapRanked01 f)

mapRanked01
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq (1 + q))
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked01 f (DynamicRanked t) = DynamicRanked $ f t
mapRanked01 f (DynamicShaped @_ @sh t) =
  withListSh (Proxy @sh) $ \(_ :: IShR n) ->
    let res = f $ rfromS @_ @_ @sh t
    in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
      case someNatVal $ 1 + valueOf @n of
        Just (SomeNat @n1 _) ->
          gcastWith (unsafeCoerce Refl :: n1 :~: 1 + n) $
          gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n1) $
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
          gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n1) $
          DynamicShaped $ sfromR @_ @_ @shr res
        _ -> error "mapRanked01: impossible someNatVal"

mapHVectorRanked10
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq q)
  -> HVector ranked -> HVector ranked
mapHVectorRanked10 f = V.map (mapRanked10 f)

mapRanked10
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq q)
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked10 f (DynamicRanked t) = case rshape t of
  ZSR -> error "mapRanked10: rank 0"
  _ :$: _ -> DynamicRanked $ f t
mapRanked10 f (DynamicShaped @_ @sh t) = case knownShS @sh of
  ZSS -> error "mapRanked10: rank 0"
  (:$$) @_ @sh0 _ tl | Dict <- sshapeKnown tl ->
    withListSh (Proxy @sh0) $ \(_ :: IShR n) ->
      let res = f $ rfromS @_ @_ @sh t
      in withShapeP (shapeToList $ rshape res) $ \(Proxy @shr) ->
        gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n) $
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
        gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n) $
        DynamicShaped $ sfromR @_ @_ @shr res

mapHVectorRanked11
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq (1 + q))
  -> HVector ranked -> HVector ranked
mapHVectorRanked11 f = V.map (mapRanked11 f)

mapRanked11
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq (1 + q))
  -> DynamicTensor ranked -> DynamicTensor ranked
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
            gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n1) $
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
            gcastWith (unsafeCoerce Refl :: X.Rank shr :~: n1) $
            DynamicShaped $ sfromR @_ @_ @shr res
          _ -> error "mapRanked01: impossible someNatVal"

mapHVectorShaped
  :: forall shaped.
     ( ShapedTensor shaped, RankedTensor (RankedOf shaped)
     , ShapedOf (RankedOf shaped) ~ shaped )
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => shaped rq shq -> shaped rq shq)
  -> HVector (RankedOf shaped) -> HVector (RankedOf shaped)
mapHVectorShaped f = V.map (mapShaped f)

mapShaped
  :: forall shaped.
     ( ShapedTensor shaped, RankedTensor (RankedOf shaped)
     , ShapedOf (RankedOf shaped) ~ shaped )
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => shaped rq shq -> shaped rq shq)
  -> DynamicTensor (RankedOf shaped) -> DynamicTensor (RankedOf shaped)
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
  :: forall k k1 shaped.
     ( ShapedTensor shaped, RankedTensor (RankedOf shaped)
     , ShapedOf (RankedOf shaped) ~ shaped
     , KnownNat k, KnownNat k1 )
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => shaped rq (k ': shq) -> shaped rq (k1 ': shq))
  -> HVector (RankedOf shaped) -> HVector (RankedOf shaped)
mapHVectorShaped11 f = V.map (mapShaped11 f)

mapShaped11
  :: forall k k1 shaped.
     ( ShapedTensor shaped, RankedTensor (RankedOf shaped)
     , ShapedOf (RankedOf shaped) ~ shaped
     , KnownNat k, KnownNat k1 )
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => shaped rq (k ': shq) -> shaped rq (k1 ': shq))
  -> DynamicTensor (RankedOf shaped) -> DynamicTensor (RankedOf shaped)
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

index1HVector :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
                 , RankedOf (PrimalOf (ShapedOf ranked))
                   ~ RankedOf (PrimalOf ranked) )
              => HVector ranked -> IntOf ranked -> HVector ranked
index1HVector = index1HVectorF rshape sshape rindex sindex

replicate1HVector :: (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
                  => SNat k -> HVector ranked -> HVector ranked
replicate1HVector = replicate1HVectorF rreplicate sreplicate

mkreplicate1HVector :: ADReady ranked
                    => SNat k -> HVector ranked -> HVectorOf ranked
mkreplicate1HVector k = dmkHVector . replicate1HVector k

interpretationConstant :: forall y ranked. ADReadyNoLet ranked
                       => (forall r. GoodScalar r => r)
                       -> TensorKindFull y -> InterpretationTarget ranked y
interpretationConstant r = \case
  FTKR sh -> rrepl (toList sh) r
  FTKS -> srepl r
  FTKProduct ftk1 ftk2 -> ttuple (interpretationConstant r ftk1)
                                 (interpretationConstant r ftk2)
  FTKUntyped ssh ->  -- TODO: if r is 0, this would be cheaper with Dummy
    HVectorPseudoTensor $ dmkHVector
    $ mapHVectorShaped (const $ srepl @_ @_ @(ShapedOf ranked) r)
    $ V.map dynamicFromVoid ssh
