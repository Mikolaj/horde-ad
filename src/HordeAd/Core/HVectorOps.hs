{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.HVectorOps
  ( addTarget, RepD(..), addDynamic
  , sizeHVector, shapeDynamic, dynamicsMatch, voidHVectorMatches
  , voidFromDynamic, voidFromHVector, dynamicFromVoid
  , fromDynamicR, fromDynamicS, unravelHVector, ravelHVector
  , mapHVectorRanked, mapHVectorRanked01, mapHVectorRanked10, mapHVectorRanked11
  , mapHVectorShaped
  , mapRanked, mapRanked01, mapRanked10, mapRanked11
  , replicate1HVector, repConstant, repConstant0Old, toADTensorKindShared
  ) where

import Prelude

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

import Data.Array.Mixed.Shape
  (KnownShX (..), ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Nested
  ( IShR
  , KnownShS (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , pattern (:$:)
  , pattern ZSR
  , type (++)
  )
import Data.Array.Nested.Internal.Shape (shCvtSX, shrRank, shsAppend)

import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.SizedList

-- This captures the normal form of type family UnWind and also
-- corresponds to the portion of ox-arrays that has Num defined.
type role RepD nominal nominal
data RepD target y where
  DTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepD target (TKScalar r)
  DTKR :: (GoodScalar r, KnownNat n)
       => target (TKR n r)
       -> RepD target (TKR n r)
  DTKS :: (GoodScalar r, KnownShS sh)
       => target (TKS sh r)
       -> RepD target (TKS sh r)
  DTKX :: (GoodScalar r, KnownShX sh)
       => target (TKX sh r)
       -> RepD target (TKX sh r)
  DTKProduct :: forall x z target. (TensorKind1 x, TensorKind1 z)
             => RepD target x -> RepD target z
             -> RepD target (TKProduct x z)
  DTKUntyped :: HVector target
             -> RepD target TKUntyped

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
    DTKScalar $ rtoScalar $ rfromScalar ta + rfromScalar tb
      -- somehow this results in shorter terms than @ta + tb@
      -- TODO: re-evaluate once scalar term simplification is complete
  (DTKR ta, DTKR tb) -> DTKR $ ta + tb
  (DTKS ta, DTKS tb) -> DTKS $ ta + tb
  (DTKX ta, DTKX tb) -> DTKX $ ta + tb
  (DTKProduct ta1 ta2, DTKProduct tb1 tb2) ->
    DTKProduct (addRepD ta1 tb1) (addRepD ta2 tb2)
  (DTKUntyped hv1, DTKUntyped hv2) ->
    DTKUntyped $ V.zipWith addDynamic hv1 hv2


-- * Winding

type family UnWind tk where
  UnWind (TKScalar r) =
    TKScalar r
  UnWind (TKR2 n (TKScalar r)) =
    TKR2 n (TKScalar r)
  UnWind (TKR2 n (TKR2 m x)) =
    UnWind (TKR2 (n + m) x)
  UnWind (TKR2 n (TKS2 sh2 x)) =
    UnWind (TKX2 (Replicate n Nothing ++ MapJust sh2) x)
  UnWind (TKR2 n (TKX2 sh2 x)) =
    UnWind (TKX2 (Replicate n Nothing ++ sh2) x)
  UnWind (TKR2 n (TKProduct y z)) =
    TKProduct (UnWind (TKR2 n y)) (UnWind (TKR2 n z))
  UnWind (TKS2 sh1 (TKScalar r)) =
    TKS2 sh1 (TKScalar r)
  UnWind (TKS2 sh1 (TKR2 m x)) =
    UnWind (TKX2 (MapJust sh1 ++ Replicate m Nothing) x)
  UnWind (TKS2 sh1 (TKS2 sh2 x)) =
    UnWind (TKS2 (sh1 ++ sh2) x)
  UnWind (TKS2 sh1 (TKX2 sh2 x)) =
    UnWind (TKX2 (MapJust sh1 ++ sh2) x)
  UnWind (TKS2 sh1 (TKProduct y z)) =
    TKProduct (UnWind (TKS2 sh1 y)) (UnWind (TKS2 sh1 z))
  UnWind (TKX2 sh1 (TKScalar r)) =
    TKX2 sh1 (TKScalar r)
  UnWind (TKX2 sh1 (TKR2 m x)) =
    UnWind (TKX2 (sh1 ++ Replicate m Nothing) x)
  UnWind (TKX2 sh1 (TKS2 sh2 x)) =
    UnWind (TKX2 (sh1 ++ MapJust sh2) x)
  UnWind (TKX2 sh1 (TKX2 sh2 x)) =
    UnWind (TKX2 (sh1 ++ sh2) x)
  UnWind (TKX2 sh1 (TKProduct y z)) =
    TKProduct (UnWind (TKX2 sh1 y)) (UnWind (TKX2 sh1 z))
  UnWind (TKProduct y z) =
    TKProduct (UnWind y) (UnWind z)
  UnWind TKUntyped =
    TKUntyped

-- TODO: should be unused now that we removed addWindShare?
unWindSTK :: STensorKindType y -> STensorKindType (UnWind y)
unWindSTK = \case
  stk@STKScalar{} -> stk
  stk@(STKR _ STKScalar{}) -> stk
  STKR (SNat @n) (STKR (SNat @m) stk2) ->
    unWindSTK $ STKR (SNat @(n + m)) stk2
  STKR n (STKS sh2 stk2) ->
    unWindSTK
    $ STKX (ssxReplicate n `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2
  STKR n (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxReplicate n `ssxAppend` sh2) stk2
  STKR n (STKProduct y z) ->
    unWindSTK $ STKProduct (STKR n y) (STKR n z)
  stk@(STKS _ STKScalar{}) -> stk
  STKS sh1 (STKR m stk2) ->
    unWindSTK
    $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` ssxReplicate m) stk2
  STKS sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKS (sh1 `shsAppend` sh2) stk2
  STKS sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2
  STKS sh1 (STKProduct y z) ->
    unWindSTK $ STKProduct (STKS sh1 y) (STKS sh1 z)
  stk@(STKX _ STKScalar{}) -> stk
  STKX sh1 (STKR m stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxReplicate m) stk2
  STKX sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2
  STKX sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` sh2) stk2
  STKX sh1 (STKProduct y z) ->
    unWindSTK $ STKProduct (STKX sh1 y) (STKX sh1 z)
  STKProduct y z | (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK y)
                 , (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK z) ->
    STKProduct (unWindSTK y) (unWindSTK z)
  stk@STKUntyped -> stk
  STKR _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"
  STKS _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"
  STKX _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"

-- This uses tunpairDup so to preserve sharing, `target` either has
-- to have a ShareTensor instance or the argument has to be duplicable.
-- Only the argument of the first call, not of recursive calls,
-- is assumed to be duplicable. In the AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
unWindTarget :: BaseTensor target
             => STensorKindType y -> target y -> RepD target (UnWind y)
unWindTarget stk t = case stk of
  STKScalar{} -> DTKScalar t
  STKR SNat STKScalar{} -> DTKR t
  STKR (SNat @n) (STKR (SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    unWindTarget (STKR (SNat @(n + m)) stk2) (runNest t)
  STKR n@SNat (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh2 $
    unWindTarget (STKX (ssxReplicate n
                       `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                (runNestS t)
  STKR n@SNat (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh2 $
    unWindTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2)
                (runNestX t)
  STKR n@SNat (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                     , Dict <- lemTensorKindOfSTK stk2 ->
    unWindTarget (STKProduct (STKR n stk1) (STKR n stk2)) (runzip t)
  STKS sh1 STKScalar{} -> withKnownShS sh1 $ DTKS t
  STKS sh1 (STKR m@(SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1)
                       `ssxAppend` ssxReplicate m) stk2) (sunNestR @_ @_ @m t)
  STKS sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh1 $ withKnownShS sh2 $
    unWindTarget (STKS (sh1 `shsAppend` sh2) stk2) (sunNest t)
  STKS sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh2 $ withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2)
                (sunNestX t)
  STKS sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh1 $
    unWindTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) (sunzip t)
  STKX sh1 STKScalar{} -> withKnownShX sh1 $ DTKX t
  STKX sh1 (STKR m@(SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh1 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2)
                      (xunNestR @_ @_ @m t)
  STKX sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh1 $ withKnownShS sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                (xunNestS t)
  STKX sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh1 $ withKnownShX sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` sh2) stk2) (xunNest t)
  STKX sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh1 $
    unWindTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) (xunzip t)
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2
                       , (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK stk1)
                       , (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK stk2) ->
    let (t1, t2) = tunpairDup t
    in DTKProduct (unWindTarget stk1 t1) (unWindTarget stk2 t2)
  STKUntyped ->
    let vt = dunHVector t
    in DTKUntyped vt
  STKR _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"
  STKS _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"
  STKX _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"

windTarget :: BaseTensor target
           => STensorKindType y -> target (UnWind y) -> target y
windTarget stk t = case stk of
  STKScalar{} -> t
  STKR _ STKScalar{} -> t
  STKR n@(SNat @n) (STKR (SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    rnest n $ windTarget (STKR (SNat @(n + m)) stk2) t
  STKR n (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh2 $
    rnestS n
    $ windTarget (STKX (ssxReplicate n
                       `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  STKR n (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh2 $
    rnestX n
    $ windTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2) t
  STKR n@SNat (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                     , Dict <- lemTensorKindOfSTK stk2 ->
    rzip $ windTarget (STKProduct (STKR n stk1) (STKR n stk2)) t
  STKS _ STKScalar{} -> t
  STKS sh1 (STKR m@SNat stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    snestR sh1
    $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                       `ssxAppend` ssxReplicate m) stk2) t
  STKS sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh2 $
    snest sh1 $ windTarget (STKS (shsAppend sh1 sh2) stk2) t
  STKS sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh2 $
    snestX sh1 $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                                  `ssxAppend` sh2) stk2) t
  STKS sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh1 $
    szip $ windTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) t
  STKX _ STKScalar{} -> t
  STKX sh1 (STKR m@SNat stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    xnestR sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2) t
  STKX sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShS sh2 $
    xnestS sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  STKX sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh2 $
    xnest sh1 $ windTarget (STKX (ssxAppend sh1 sh2) stk2) t
  STKX sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2 ->
    withKnownShX sh1 $
    xzip $ windTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2
                       , (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK stk1)
                       , (Dict, Dict) <- lemTensorKind1OfSTK (unWindSTK stk2) ->
    let (t1, t2) = tunpairDup t  -- but t is a tpair due to fromRepD
    in tpair (windTarget stk1 t1) (windTarget stk2 t2)
  STKUntyped -> t
  STKR _ STKUntyped -> error "windTarget: TKUntyped can't be nested in arrays"
  STKS _ STKUntyped -> error "windTarget: TKUntyped can't be nested in arrays"
  STKX _ STKUntyped -> error "windTarget: TKUntyped can't be nested in arrays"

addTarget :: ADReadyNoLet target
          => STensorKindType y -> target y -> target y -> target y
addTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in windTarget stk $ fromRepD $ addRepD a2 b2


-- * Dynamic

addDynamic :: forall target.
              (BaseTensor target, (forall y. TensorKind y => Show (target y)))
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
sizeHVector = let f (DynamicRanked @r t) = rsize @target @(TKScalar r) t
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
             => (IShR n -> target (TKR n r)) -> DynamicTensor target
             -> target (TKR n r)
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
             => target (TKS sh r) -> DynamicTensor target
             -> target (TKS sh r)
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
    map DynamicShaped $ sunravelToList (srepl 0 :: target (TKS sh rp))

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
      let g :: DynamicTensor target -> target (TKR p1 rp)
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
        let g :: DynamicTensor target -> target (TKS shp rp)
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
      => target (TKR q rq) -> target (TKR q rq))
  -> HVector target -> HVector target
mapHVectorRanked f = V.map (mapRanked f)

mapRanked
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR q rq) -> target (TKR q rq))
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
      => target (TKR q rq) -> target (TKR (1 + q) rq))
  -> HVector target -> HVector target
mapHVectorRanked01 f = V.map (mapRanked01 f)

mapRanked01
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR q rq) -> target (TKR (1 + q) rq))
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
      => target (TKR (1 + q) rq) -> target (TKR q rq))
  -> HVector target -> HVector target
mapHVectorRanked10 f = V.map (mapRanked10 f)

mapRanked10
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR (1 + q) rq) -> target (TKR q rq))
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
      => target (TKR (1 + q) rq) -> target (TKR (1 + q) rq))
  -> HVector target -> HVector target
mapHVectorRanked11 f = V.map (mapRanked11 f)

mapRanked11
  :: BaseTensor target
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => target (TKR (1 + q) rq) -> target (TKR (1 + q) rq))
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
      => target (TKS shq rq) -> target (TKS shq rq))
  -> HVector target -> HVector target
mapHVectorShaped f = V.map (mapShaped f)

mapShaped
  :: forall target.
     BaseTensor target
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS shq rq) -> target (TKS shq rq))
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

replicate1HVector :: BaseTensor target
                  => SNat k -> HVector target -> HVector target
replicate1HVector = replicate1HVectorF rreplicate sreplicate

repConstant :: forall y target. ADReadyNoLet target
            => (forall r. GoodScalar r => r)
            -> FullTensorKind y -> target y
repConstant r = \case
  FTKScalar -> rtoScalar $ rscalar r
  FTKR sh FTKScalar | SNat <- shrRank sh -> rrepl (toList sh) r
  FTKS sh FTKScalar -> withKnownShS sh $ srepl r
  FTKX sh FTKScalar -> withKnownShX (ssxFromShape sh) $ xrepl sh r
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfFTK ftk1
                       , Dict <- lemTensorKindOfFTK ftk2 ->
    tpair (repConstant r ftk1)
          (repConstant r ftk2)
  FTKUntyped ssh ->  -- TODO: if r is 0, this would be cheaper with Dummy
    dmkHVector
    $ mapHVectorShaped (const $ srepl @_ @_ @target r)
    $ V.map dynamicFromVoid ssh
  _ -> error "TODO"

repConstant0Old :: forall y target. ADReadyNoLet target
                => FullTensorKind y -> target y
repConstant0Old = \case
  FTKScalar -> rtoScalar $ rscalar 0
  FTKR sh FTKScalar | SNat <- shrRank sh -> rzero sh
  FTKS sh FTKScalar -> withKnownShS sh $ srepl 0
  FTKX sh FTKScalar -> withKnownShX (ssxFromShape sh) $ xzero sh
  FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfFTK ftk1
                       , Dict <- lemTensorKindOfFTK ftk2 ->
    tpair (repConstant0Old ftk1)
          (repConstant0Old ftk2)
  FTKUntyped ssh -> dmkHVector $ V.map dynamicFromVoid ssh
  _ -> error "TODO"

toADTensorKindShared
  :: forall target y. (BaseTensor target, ShareTensor target)
  => STensorKindType y -> target y
  -> target (ADTensorKind y)
toADTensorKindShared stk t = case stk of
  STKScalar @r _ -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           rtoScalar $ rscalar Z0
  STKR SNat (STKScalar @r _) -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           rrepl @_ @_ @target (toList $ rshape t) Z0
  STKS @sh sh (STKScalar @r _) -> withKnownShS sh
                      $ case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           srepl @sh @Z0 @target Z0
  STKX sh (STKScalar @r _) -> withKnownShX sh
                  $ case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           xrepl @_ @_ @target (xshape t) Z0
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2
                       , (Dict, Dict) <- lemTensorKind1OfAD stk1
                       , (Dict, Dict) <- lemTensorKind1OfAD stk2 ->
    let (t1, t2) = tunpair t
    in tpair (toADTensorKindShared stk1 t1) (toADTensorKindShared stk2 t2)
  STKUntyped -> t
  _ -> error "TODO"
