{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.HVectorOps
  ( -- * One-hots
    roneHot, soneHot, xoneHot
    -- * Winding
  , addTarget, constantTarget
    -- * Dynamic
  , sizeHVector, shapeDynamic, dynamicsMatch, voidHVectorMatches
  , voidFromDynamic, voidFromHVector, dynamicFromVoid
  , fromDynamicR, fromDynamicS, unravelHVector, ravelHVector
  , mapHVectorRanked, mapHVectorRanked01, mapHVectorRanked10, mapHVectorRanked11
  , mapHVectorShaped
  , mapRanked, mapRanked01, mapRanked10, mapRanked11
  , replicate1HVector, toADTensorKindShared
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
  (IShX, KnownShX (..), shxAppend, ssxAppend, ssxFromShape, ssxReplicate)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
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
import Data.Array.Nested.Internal.Shape
  (shCvtRX, shCvtSX, shrAppend, shrRank, shsAppend)

import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Util.ShapedList (dropIxS)
import HordeAd.Util.SizedList

-- * One-hots

-- These use constantTarget, so can't be defined in TensorClass.

roneHot :: forall r m n target.
           ( BaseTensor target, TensorKind r, KnownNat m, KnownNat n
           , BoolOf (PrimalOf target) ~ BoolOf target, IfF target
           , EqF (PrimalOf target) )
        => IShR m -> target (TKR2 n r) -> IxROf target m
        -> target (TKR2 (m + n) r)
roneHot sh v ix = case stensorKind @r of
  STKScalar{} ->
    rscatter @_ @_ @0
             (shrAppend sh (rshape v)) v (const ix)
  _ -> case tftk stensorKind v of
    FTKR _ ftk2 ->
      let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                       $ zip (toList ix) (toList ix2))
                      (rindex0 v (dropIndex ix2))
                      (constantTarget 0 (FTKR ZSR ftk2))
      in rbuild (shrAppend sh (rshape v)) f
         -- TODO: if this is used often, maybe express this as the gather that
         -- would come out of vectorization, making sure it simplifies well

soneHot :: forall r sh1 sh2 target.
           ( BaseTensor target, TensorKind r, KnownShS sh1, KnownShS sh2
           , KnownShS (sh1 ++ sh2)
           , BoolOf (PrimalOf target) ~ BoolOf target, IfF target
           , EqF (PrimalOf target) )
        => target (TKS2 sh2 r) -> IxSOf target sh1
        -> target (TKS2 (sh1 ++ sh2) r)
soneHot v ix = case stensorKind @r of
  STKScalar{} | Dict <- lemKnownNatRankS (knownShS @sh1) ->
    gcastWith (unsafeCoerce Refl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
    sscatter @_ @_ @'[] @(Rank sh1) v (const ix)
  _ -> case tftk stensorKind v of
    FTKS _ ftk2 ->
      gcastWith (unsafeCoerce Refl
                 :: Drop (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: '[]) $
      gcastWith (unsafeCoerce Refl
                 :: Take (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: (sh1 ++ sh2)) $
      gcastWith (unsafeCoerce Refl
                 :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      withListSh (Proxy @sh1) $ \(_ :: IShR rankSh1) ->
      gcastWith (unsafeCoerce Refl :: rankSh1 :~: Rank sh1) $
         let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                       $ zip (toList ix) (toList ix2))
                      (sindex0 v (dropIxS @(Rank sh1) ix2))
                      (constantTarget 0 (FTKS ZSS ftk2))
      in sbuild @_ @_ @(Rank (sh1 ++ sh2)) f

xoneHot :: forall r sh1 sh2 target.
--           ( BaseTensor target, GoodScalar r, KnownShX sh1, KnownShX sh2
--           , KnownShX (sh1 ++ sh2) )
           IShX sh1 -> target (TKX sh2 r) -> IxXOf target sh1
        -> target (TKX (sh1 ++ sh2) r)
xoneHot = error "TODO"


-- * Winding

-- This captures the normal form of type family UnWind and also
-- corresponds to the portion of ox-arrays that has Num defined.
type role RepW nominal nominal
data RepW target y where
  WTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepW target (TKScalar r)
  WTKR :: (GoodScalar r, KnownNat n)
       => target (TKR n r)
       -> RepW target (TKR n r)
  WTKS :: (GoodScalar r, KnownShS sh)
       => target (TKS sh r)
       -> RepW target (TKS sh r)
  WTKX :: (GoodScalar r, KnownShX sh)
       => target (TKX sh r)
       -> RepW target (TKX sh r)
  WTKProduct :: (TensorKind x, TensorKind z)
             => RepW target x -> RepW target z
             -> RepW target (TKProduct x z)
  WTKUntyped :: HVector target
             -> RepW target TKUntyped

-- This captures the normal form of type family UnWind for full singletons.
type role FullTensorKindW nominal
data FullTensorKindW y where
  WFTKScalar :: GoodScalar r
             => FullTensorKindW (TKScalar r)
  WFTKR :: GoodScalar r
        => IShR n -> FullTensorKindW (TKR n r)
  WFTKS :: GoodScalar r
        => ShS sh -> FullTensorKindW (TKS sh r)
  WFTKX :: GoodScalar r
        => IShX sh -> FullTensorKindW (TKX sh r)
  WFTKProduct :: FullTensorKindW y -> FullTensorKindW z
              -> FullTensorKindW (TKProduct y z)
  WFTKUntyped :: VoidHVector -> FullTensorKindW TKUntyped

fromFTKW :: FullTensorKindW y -> FullTensorKind y
fromFTKW = \case
  WFTKScalar -> FTKScalar
  WFTKR sh -> FTKR sh FTKScalar
  WFTKS sh -> FTKS sh FTKScalar
  WFTKX sh -> FTKX sh FTKScalar
  WFTKProduct ftk1 ftk2 -> FTKProduct (fromFTKW ftk1) (fromFTKW ftk2)
  WFTKUntyped ssh -> FTKUntyped ssh

addRepW :: forall y target. BaseTensor target
        => RepW target y -> RepW target y -> RepW target y
addRepW a b = case (a, b) of
  (WTKScalar ta, WTKScalar tb) ->
    WTKScalar $ rtoScalar $ rfromScalar ta + rfromScalar tb
      -- somehow this results in shorter terms than @ta + tb@
      -- TODO: re-evaluate once scalar term simplification is complete
  (WTKR ta, WTKR tb) -> WTKR $ ta + tb
  (WTKS ta, WTKS tb) -> WTKS $ ta + tb
  (WTKX ta, WTKX tb) -> WTKX $ ta + tb
  (WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    WTKProduct (addRepW ta1 tb1) (addRepW ta2 tb2)
  (WTKUntyped hv1, WTKUntyped hv2) ->
    WTKUntyped $ V.zipWith addDynamic hv1 hv2

constantRepW :: forall y target. BaseTensor target
            => (forall r. GoodScalar r => r)
            -> FullTensorKindW y -> RepW target y
constantRepW r = \case
  WFTKScalar -> WTKScalar $ rtoScalar $ rscalar r
  WFTKR sh | SNat <- shrRank sh -> WTKR $ rrepl (toList sh) r
  WFTKS sh -> withKnownShS sh $ WTKS $ srepl r
  WFTKX sh -> withKnownShX (ssxFromShape sh) $ WTKX $ xrepl sh r
  WFTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfSTK (ftkToStk $ fromFTKW ftk1)
                        , Dict <- lemTensorKindOfSTK (ftkToStk $ fromFTKW ftk2) ->
    WTKProduct (constantRepW r ftk1) (constantRepW r ftk2)
  WFTKUntyped ssh ->  -- TODO: if r is 0, this would be cheaper with Dummy
    WTKUntyped
    $ mapHVectorShaped (const $ srepl @_ @_ @target r)
    $ V.map dynamicFromVoid ssh

toADTensorKindW
  :: forall y target. BaseTensor target
  => RepW target y -> RepW target (ADTensorKind y)
toADTensorKindW t = case t of
  WTKScalar @r _ -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           WTKScalar $ rtoScalar $ rscalar Z0
  WTKR @r v -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           WTKR $ rrepl @_ @_ @target (toList $ rshape v) Z0
  WTKS @r _ -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           WTKS $ srepl @_ @_ @target Z0
  WTKX @r v -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerce Refl :: ADTensorScalar r :~: Z0) $
           WTKX $ xrepl @_ @_ @target (xshape v) Z0
  WTKProduct @y1 @y2 t1 t2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                           , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    WTKProduct (toADTensorKindW t1) (toADTensorKindW t2)
  WTKUntyped{} -> t

type family UnWind y where
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
  STKR n@SNat (STKProduct y z) ->
    unWindSTK $ STKProduct (STKR n y) (STKR n z)
  stk@(STKS _ STKScalar{}) -> stk
  STKS sh1 (STKR m stk2) ->
    unWindSTK
    $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` ssxReplicate m) stk2
  STKS sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKS (sh1 `shsAppend` sh2) stk2
  STKS sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2
  STKS sh1 (STKProduct y z)->
    withKnownShS sh1 $
    unWindSTK $ STKProduct (STKS sh1 y) (STKS sh1 z)
  stk@(STKX _ STKScalar{}) -> stk
  STKX sh1 (STKR m stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxReplicate m) stk2
  STKX sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2
  STKX sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` sh2) stk2
  STKX sh1 (STKProduct y z) ->
    withKnownShX sh1 $
    unWindSTK $ STKProduct (STKX sh1 y) (STKX sh1 z)
  STKProduct y z | Dict <- lemTensorKindOfSTK (unWindSTK y)
                 , Dict <- lemTensorKindOfSTK (unWindSTK z) ->
    STKProduct (unWindSTK y) (unWindSTK z)
  stk@STKUntyped -> stk
  STKR _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"
  STKS _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"
  STKX _ STKUntyped -> error "unWindSTK: TKUntyped can't be nested in arrays"

unWindFTK :: FullTensorKind y -> FullTensorKindW (UnWind y)
unWindFTK = \case
  FTKScalar -> WFTKScalar
  FTKR sh FTKScalar -> WFTKR sh
  FTKR sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKR (sh1 `shrAppend` sh2) ftk2
  FTKR sh1 (FTKS sh2 ftk2) ->
    unWindFTK
    $ FTKX (shCvtRX sh1 `shxAppend` shCvtSX sh2) ftk2
  FTKR sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shCvtRX sh1 `shxAppend` sh2) ftk2
  FTKR sh1 (FTKProduct y z) | SNat <- shrRank sh1 ->
    unWindFTK $ FTKProduct (FTKR sh1 y) (FTKR sh1 z)
  FTKS sh FTKScalar -> WFTKS sh
  FTKS sh1 (FTKR sh2 ftk2) ->
    unWindFTK
    $ FTKX (shCvtSX sh1 `shxAppend` shCvtRX sh2) ftk2
  FTKS sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKS (sh1 `shsAppend` sh2) ftk2
  FTKS sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shCvtSX sh1 `shxAppend` sh2) ftk2
  FTKS sh1 (FTKProduct y z) ->
    withKnownShS sh1 $
    unWindFTK $ FTKProduct (FTKS sh1 y) (FTKS sh1 z)
  FTKX sh FTKScalar -> WFTKX sh
  FTKX sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shCvtRX sh2) ftk2
  FTKX sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shCvtSX sh2) ftk2
  FTKX sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` sh2) ftk2
  FTKX sh1 (FTKProduct y z) ->
    withKnownShX (ssxFromShape sh1) $
    unWindFTK $ FTKProduct (FTKX sh1 y) (FTKX sh1 z)
  FTKProduct y z
   | Dict <- lemTensorKindOfSTK (ftkToStk $ fromFTKW $ unWindFTK y)
   , Dict <- lemTensorKindOfSTK (ftkToStk $ fromFTKW $ unWindFTK z) ->
    WFTKProduct (unWindFTK y) (unWindFTK z)
  FTKUntyped ssh -> WFTKUntyped ssh
  FTKR _ FTKUntyped{} -> error "unWindFTK: TKUntyped can't be nested in arrays"
  FTKS _ FTKUntyped{} -> error "unWindFTK: TKUntyped can't be nested in arrays"
  FTKX _ FTKUntyped{} -> error "unWindFTK: TKUntyped can't be nested in arrays"

-- This uses tunpairDup so to preserve sharing, `target` either has
-- to have a ShareTensor instance or the argument has to be duplicable.
-- Only the argument of the first call, not of recursive calls,
-- is assumed to be duplicable. In the AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
unWindTarget :: BaseTensor target
             => STensorKindType y -> target y -> RepW target (UnWind y)
unWindTarget stk t = case stk of
  STKScalar{} -> WTKScalar t
  STKR SNat STKScalar{} -> WTKR t
  STKR (SNat @n) (STKR (SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2
                                       , Dict <- eltDictRep stk2 ->
    unWindTarget (STKR (SNat @(n + m)) stk2) (runNest t)
  STKR n@SNat (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                              , Dict <- eltDictRep stk2 ->
    withKnownShS sh2 $
    unWindTarget (STKX (ssxReplicate n
                       `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                (runNestS t)
  STKR n@SNat (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                              , Dict <- eltDictRep stk2 ->
    withKnownShX sh2 $
    unWindTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2)
                (runNestX t)
  STKR n@SNat (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                     , Dict <- lemTensorKindOfSTK stk2
                                     , Dict <- eltDictRep stk1
                                     , Dict <- eltDictRep stk2 ->
    unWindTarget (STKProduct (STKR n stk1) (STKR n stk2)) (runzip t)
  STKS sh1 STKScalar{} -> withKnownShS sh1 $ WTKS t
  STKS sh1 (STKR m@(SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2
                                   , Dict <- eltDictRep stk2 ->
    withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1)
                       `ssxAppend` ssxReplicate m) stk2) (sunNestR @_ @_ @m t)
  STKS sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                           , Dict <- eltDictRep stk2 ->
    withKnownShS sh1 $ withKnownShS sh2 $
    unWindTarget (STKS (sh1 `shsAppend` sh2) stk2) (sunNest t)
  STKS sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                           , Dict <- eltDictRep stk2 ->
    withKnownShX sh2 $ withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2)
                (sunNestX t)
  STKS sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2
                                  , Dict <- eltDictRep stk1
                                  , Dict <- eltDictRep stk2 ->
    withKnownShS sh1 $
    unWindTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) (sunzip t)
  STKX sh1 STKScalar{} -> withKnownShX sh1 $ WTKX t
  STKX sh1 (STKR m@(SNat @m) stk2) | Dict <- lemTensorKindOfSTK stk2
                                   , Dict <- eltDictRep stk2 ->
    withKnownShX sh1 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2)
                      (xunNestR @_ @_ @m t)
  STKX sh1 (STKS sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                           , Dict <- eltDictRep stk2 ->
    withKnownShX sh1 $ withKnownShS sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                (xunNestS t)
  STKX sh1 (STKX sh2 stk2) | Dict <- lemTensorKindOfSTK stk2
                           , Dict <- eltDictRep stk2 ->
    withKnownShX sh1 $ withKnownShX sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` sh2) stk2) (xunNest t)
  STKX sh1 (STKProduct stk1 stk2) | Dict <- lemTensorKindOfSTK stk1
                                  , Dict <- lemTensorKindOfSTK stk2
                                  , Dict <- eltDictRep stk1
                                  , Dict <- eltDictRep stk2 ->
    withKnownShX sh1 $
    unWindTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) (xunzip t)
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfSTK stk1
                       , Dict <- lemTensorKindOfSTK stk2
                       , Dict <- eltDictRep stk1
                       , Dict <- eltDictRep stk2
                       , Dict <- lemTensorKindOfSTK (unWindSTK stk1)
                       , Dict <- lemTensorKindOfSTK (unWindSTK stk2) ->
    let (t1, t2) = tunpairDup t
    in WTKProduct (unWindTarget stk1 t1) (unWindTarget stk2 t2)
  STKUntyped ->
    let vt = dunHVector t
    in WTKUntyped vt
  STKR _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"
  STKS _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"
  STKX _ STKUntyped -> error "unWindTarget: TKUntyped can't be nested in arrays"

windTarget :: BaseTensor target
           => STensorKindType y -> RepW target (UnWind y) -> target y
windTarget stk t = case (stk, t) of
  (STKScalar{}, WTKScalar v) -> v
  (STKR _ STKScalar{}, WTKR v) -> v
  (STKR n@(SNat @n) (STKR (SNat @m) stk2), _)
   | Dict <- lemTensorKindOfSTK stk2
   , Dict <- eltDictRep stk2 ->
    rnest n $ windTarget (STKR (SNat @(n + m)) stk2) t
  (STKR n (STKS sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                              , Dict <- eltDictRep stk2 ->
    withKnownShS sh2 $
    rnestS n
    $ windTarget (STKX (ssxReplicate n
                       `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  (STKR n (STKX sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                              , Dict <- eltDictRep stk2 ->
    withKnownShX sh2 $
    rnestX n
    $ windTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2) t
  (STKR n@SNat (STKProduct stk1 stk2), _) | Dict <- lemTensorKindOfSTK stk1
                                          , Dict <- lemTensorKindOfSTK stk2
                                          , Dict <- eltDictRep stk1
                                          , Dict <- eltDictRep stk2 ->
    rzip $ windTarget (STKProduct (STKR n stk1) (STKR n stk2)) t
  (STKS _ STKScalar{}, WTKS v) -> v
  (STKS sh1 (STKR m@SNat stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                   , Dict <- eltDictRep stk2 ->
    snestR sh1
    $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                       `ssxAppend` ssxReplicate m) stk2) t
  (STKS sh1 (STKS sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                , Dict <- eltDictRep stk2 ->
    withKnownShS sh2 $
    snest sh1 $ windTarget (STKS (shsAppend sh1 sh2) stk2) t
  (STKS sh1 (STKX sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                , Dict <- eltDictRep stk2 ->
    withKnownShX sh2 $
    snestX sh1 $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                                  `ssxAppend` sh2) stk2) t
  (STKS sh1 (STKProduct stk1 stk2), _) | Dict <- lemTensorKindOfSTK stk1
                                       , Dict <- lemTensorKindOfSTK stk2
                                       , Dict <- eltDictRep stk1
                                       , Dict <- eltDictRep stk2 ->
    withKnownShS sh1 $
    szip $ windTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) t
  (STKX _ STKScalar{}, WTKX v) -> v
  (STKX sh1 (STKR m@SNat stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                   , Dict <- eltDictRep stk2 ->
    xnestR sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2) t
  (STKX sh1 (STKS sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                , Dict <- eltDictRep stk2 ->
    withKnownShS sh2 $
    xnestS sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  (STKX sh1 (STKX sh2 stk2), _) | Dict <- lemTensorKindOfSTK stk2
                                , Dict <- eltDictRep stk2 ->
    withKnownShX sh2 $
    xnest sh1 $ windTarget (STKX (ssxAppend sh1 sh2) stk2) t
  (STKX sh1 (STKProduct stk1 stk2), _) | Dict <- lemTensorKindOfSTK stk1
                                       , Dict <- lemTensorKindOfSTK stk2
                                       , Dict <- eltDictRep stk1
                                       , Dict <- eltDictRep stk2 ->
    withKnownShX sh1 $
    xzip $ windTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) t
  (STKProduct stk1 stk2, WTKProduct t1 t2)
   | Dict <- lemTensorKindOfSTK stk1
   , Dict <- lemTensorKindOfSTK stk2
   , Dict <- eltDictRep stk1
   , Dict <- eltDictRep stk2
   , Dict <- lemTensorKindOfSTK (unWindSTK stk1)
   , Dict <- lemTensorKindOfSTK (unWindSTK stk2) ->
    tpair (windTarget stk1 t1) (windTarget stk2 t2)
  (STKUntyped, WTKUntyped v) -> dmkHVector v
  (STKR _ STKUntyped, _) ->
    error "windTarget: TKUntyped can't be nested in arrays"
  (STKS _ STKUntyped, _) ->
    error "windTarget: TKUntyped can't be nested in arrays"
  (STKX _ STKUntyped, _) ->
    error "windTarget: TKUntyped can't be nested in arrays"

addTarget :: BaseTensor target
          => STensorKindType y -> target y -> target y -> target y
addTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in windTarget stk $ addRepW a2 b2

constantTarget :: forall y target. BaseTensor target
               => (forall r. GoodScalar r => r) -> FullTensorKind y -> target y
constantTarget r ftk =
  windTarget (ftkToStk ftk) $ constantRepW r (unWindFTK ftk)

toADTensorKindShared  -- TODO: does not require Shared now
  :: BaseTensor target
  => STensorKindType y -> target y
  -> target (ADTensorKind y)
toADTensorKindShared stk a | Refl <- lemUnWindOfAD stk =
  windTarget (aDSTK stk) $ toADTensorKindW $ unWindTarget stk a

lemUnWindOfAD :: STensorKindType y
              -> UnWind (ADTensorKind y) :~: ADTensorKind (UnWind y)
lemUnWindOfAD _ = unsafeCoerceRefl


-- * Dynamic

addDynamic :: BaseTensor target
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
addDynamic _ _ = error "addDynamic: wrong arguments"  -- ++ show (t, u)

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
voidFromDynamic :: BaseTensor target
                => DynamicTensor target -> DynamicTensor VoidTensor
voidFromDynamic = voidFromDynamicF (shapeToList . rshape)

voidFromHVector :: BaseTensor target
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
  :: BaseTensor target
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
  :: BaseTensor target
  => (forall rq shq. (GoodScalar rq, KnownShS shq)
      => target (TKS shq rq) -> target (TKS shq rq))
  -> HVector target -> HVector target
mapHVectorShaped f = V.map (mapShaped f)

mapShaped
  :: BaseTensor target
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
mapShaped f (DynamicShapedDummy @r @sh _ _) =
  DynamicShaped $ f @r @sh (srepl 0)

replicate1HVector :: BaseTensor target
                  => SNat k -> HVector target -> HVector target
replicate1HVector = replicate1HVectorF rreplicate sreplicate
