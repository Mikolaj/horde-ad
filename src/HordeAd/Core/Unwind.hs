{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.Unwind
  ( addTarget, multTarget, dotTarget, constantTarget, defTarget, concreteTarget
  , toADTensorKindShared, fromADTensorKindShared
  ) where

import Prelude

import Data.Default
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.TypeLits (type (+))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

-- * Winding and unwinding

-- This captures the normal form of type family UnWind and also
-- corresponds to the portion of ox-arrays that has Num defined.
type role RepW nominal nominal
data RepW target y where
  WTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepW target (TKScalar r)
  WTKR :: GoodScalar r
       => target (TKR n r)
       -> RepW target (TKR n r)
  WTKS :: GoodScalar r
       => target (TKS sh r)
       -> RepW target (TKS sh r)
  WTKX :: GoodScalar r
       => target (TKX sh r)
       -> RepW target (TKX sh r)
  WTKProduct :: RepW target x -> RepW target z
             -> RepW target (TKProduct x z)

-- This captures the normal form of type family UnWind for full singletons.
type role FullShapeTKW nominal
data FullShapeTKW y where
  WFTKScalar :: GoodScalar r
             => FullShapeTKW (TKScalar r)
  WFTKR :: GoodScalar r
        => IShR n -> FullShapeTKW (TKR n r)
  WFTKS :: GoodScalar r
        => ShS sh -> FullShapeTKW (TKS sh r)
  WFTKX :: GoodScalar r
        => IShX sh -> FullShapeTKW (TKX sh r)
  WFTKProduct :: FullShapeTKW y -> FullShapeTKW z
              -> FullShapeTKW (TKProduct y z)

addRepW :: forall y target. BaseTensor target
        => RepW target y -> RepW target y -> RepW target y
addRepW a b = case (a, b) of
  (WTKScalar ta, WTKScalar tb) -> WTKScalar $ ta + tb
  (WTKR ta, WTKR tb) -> WTKR $ ta + tb
  (WTKS ta, WTKS tb) -> WTKS $ ta + tb
  (WTKX ta, WTKX tb) -> WTKX $ ta + tb
  (WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    WTKProduct (addRepW ta1 tb1) (addRepW ta2 tb2)

multRepW :: forall y target. BaseTensor target
         => RepW target y -> RepW target y -> RepW target y
multRepW a b = case (a, b) of
  (WTKScalar ta, WTKScalar tb) -> WTKScalar $ ta * tb
  (WTKR ta, WTKR tb) -> WTKR $ ta * tb
  (WTKS ta, WTKS tb) -> WTKS $ ta * tb
  (WTKX ta, WTKX tb) -> WTKX $ ta * tb
  (WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    WTKProduct (multRepW ta1 tb1) (multRepW ta2 tb2)

-- TODO: maybe instead of ifDifferentiable perform only on ADTensorKind?
dotRepW :: forall y target. (BaseTensor target, ConvertTensor target)
        => FullShapeTKW y -> RepW target y -> RepW target y
        -> target (TKScalar Double)
dotRepW ftk a b = case (ftk, a, b) of
  (_, WTKScalar @r ta, WTKScalar tb) ->
    ifDifferentiable @r (kcast $ ta * tb) 0
  (WFTKR sh, WTKR @r ta, WTKR tb) | SNat <- shrRank sh ->
    ifDifferentiable @r (kcast $ kfromR $ rdot0 ta tb) 0
  (WFTKS sh, WTKS @r ta, WTKS tb) ->
    withKnownShS sh $
    ifDifferentiable @r (kcast $ kfromS $ sdot0 ta tb) 0
  (WFTKX sh, WTKX @r ta, WTKX tb) ->
    withKnownShX (ssxFromShape sh) $
    ifDifferentiable @r (kcast $ kfromX $ xdot0 ta tb) 0
  (WFTKProduct ftk1 ftk2, WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    dotRepW ftk1 ta1 tb1 + dotRepW ftk2 ta2 tb2

constantRepW :: forall y target. BaseTensor target
            => (forall r. GoodScalar r => r)
            -> FullShapeTKW y -> RepW target y
constantRepW r = \case
  WFTKScalar -> WTKScalar $ kconcrete r
  WFTKR sh -> WTKR $ rrepl sh r
  WFTKS sh -> WTKS $ sconcrete $ Nested.sreplicateScal sh r
  WFTKX sh -> WTKX $ xrepl sh r
  WFTKProduct ftk1 ftk2 ->
    WTKProduct (constantRepW r ftk1) (constantRepW r ftk2)

defRepW :: forall y target. BaseTensor target
        => FullShapeTKW y -> RepW target y
defRepW = \case
  WFTKScalar -> WTKScalar $ kconcrete def
  WFTKR sh -> WTKR $ rrepl sh def
  WFTKS sh -> WTKS $ sconcrete $ Nested.sreplicateScal sh def
  WFTKX sh -> WTKX $ xrepl sh def
  WFTKProduct ftk1 ftk2 ->
    WTKProduct (defRepW ftk1) (defRepW ftk2)

concreteRepW
  :: forall y target. (ConvertTensor RepN, ConvertTensor target)
  => (forall r. GoodScalar r => RepN (TKScalar r) -> target (TKScalar r))
  -> (forall r sh. GoodScalar r => RepN (TKS sh r) -> target (TKS sh r))
  -> (forall x z. SingletonTK z -> target x -> target z)
  -> RepW RepN y -> RepW target y
{-# INLINE concreteRepW #-}
concreteRepW concreteK concreteS fromS w = case w of
  WTKScalar v -> WTKScalar $ concreteK v
  WTKR v -> WTKR $
    let sh' = Nested.rshape $ unRepN v
    in withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      fromS (STKR (shrRank sh') STKScalar)
      $ concreteS (sfromR @_ @sh v)
  WTKS v -> WTKS $ concreteS v
  WTKX v -> WTKX $
    let sh' = Nested.mshape $ unRepN v
    in withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      fromS (STKX (ssxFromShape sh') STKScalar)
      $ concreteS (sfromX @_ @sh v)
  WTKProduct v1 v2 ->
    WTKProduct (concreteRepW concreteK concreteS fromS v1)
               (concreteRepW concreteK concreteS fromS v2)

toADTensorKindW
  :: forall y target. BaseTensor target
  => RepW target y -> FullShapeTKW y -> RepW target (ADTensorKind y)
toADTensorKindW t = \case
  WFTKScalar @r -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           WTKScalar $ kconcrete Z0
  WFTKR @r sh -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           WTKR $ rrepl @_ @_ @target sh Z0
  WFTKS @r sh -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           WTKS $ sconcrete $ Nested.sreplicateScal sh Z0
  WFTKX @r sh -> case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> t
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> t
      _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: Z0) $
           WTKX $ xrepl @_ @_ @target sh Z0
  WFTKProduct ftk1 ftk2 -> case t of
    WTKProduct t1 t2 ->
      WTKProduct (toADTensorKindW t1 ftk1) (toADTensorKindW t2 ftk2)

fromADTensorKindW
  :: forall y target. BaseTensor target
  => SingletonTK y -> RepW target (ADTensorKind y) -> RepW target y
fromADTensorKindW stk t = case (stk, t) of
  (STKScalar @r1, WTKScalar @r2 _) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> constantRepW 0 WFTKScalar
  (STKR _ (STKScalar @r1), WTKR @r2 v) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> constantRepW 0 (WFTKR (rshape v))
  (STKS sh (STKScalar @r1), WTKS @r2 _) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> constantRepW 0 (WFTKS sh)
  (STKX _ (STKScalar @r1), WTKX @r2 v) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> constantRepW 0 (WFTKX (xshape v))
  (STKProduct stk1 stk2, WTKProduct t1 t2) ->
    WTKProduct (fromADTensorKindW stk1 t1) (fromADTensorKindW stk2 t2)
  _ -> error "fromADTensorKindW: impossible SingletonTK"

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

unWindSTK :: SingletonTK y -> SingletonTK (UnWind y)
unWindSTK = \case
  stk@STKScalar -> stk
  stk@(STKR _ STKScalar) -> stk
  STKR (SNat @n) (STKR (SNat @m) stk2) ->
    unWindSTK $ STKR (SNat @(n + m)) stk2
  STKR n (STKS sh2 stk2) ->
    unWindSTK
    $ STKX (ssxReplicate n `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2
  STKR n (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxReplicate n `ssxAppend` sh2) stk2
  STKR n@SNat (STKProduct y z) ->
    unWindSTK $ STKProduct (STKR n y) (STKR n z)
  stk@(STKS _ STKScalar) -> stk
  STKS sh1 (STKR m stk2) ->
    unWindSTK
    $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` ssxReplicate m) stk2
  STKS sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKS (sh1 `shsAppend` sh2) stk2
  STKS sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2
  STKS sh1 (STKProduct y z)->
    unWindSTK $ STKProduct (STKS sh1 y) (STKS sh1 z)
  stk@(STKX _ STKScalar) -> stk
  STKX sh1 (STKR m stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxReplicate m) stk2
  STKX sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2
  STKX sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` sh2) stk2
  STKX sh1 (STKProduct y z) ->
    unWindSTK $ STKProduct (STKX sh1 y) (STKX sh1 z)
  STKProduct y z -> STKProduct (unWindSTK y) (unWindSTK z)

unWindFTK :: FullShapeTK y -> FullShapeTKW (UnWind y)
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
  FTKR sh1 (FTKProduct y z) ->
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
    unWindFTK $ FTKProduct (FTKS sh1 y) (FTKS sh1 z)
  FTKX sh FTKScalar -> WFTKX sh
  FTKX sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shCvtRX sh2) ftk2
  FTKX sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shCvtSX sh2) ftk2
  FTKX sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` sh2) ftk2
  FTKX sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKX sh1 y) (FTKX sh1 z)
  FTKProduct y z -> WFTKProduct (unWindFTK y) (unWindFTK z)

-- This uses tunpairConv so to preserve sharing, `target` either has
-- to have a ShareTensor instance or the argument has to be duplicable.
-- Only the argument of the first call, not of recursive calls,
-- is assumed to be duplicable. In the AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
unWindTarget :: ConvertTensor target
             => SingletonTK y -> target y -> RepW target (UnWind y)
unWindTarget stk t = case stk of
  STKScalar -> WTKScalar t
  STKR SNat STKScalar -> WTKR t
  STKR (SNat @n) (STKR (SNat @m) stk2) | Dict <- lemKnownSTK stk2 ->
    unWindTarget (STKR (SNat @(n + m)) stk2) (runNest t)
  STKR n@SNat (STKS sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    unWindTarget (STKX (ssxReplicate n
                        `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                 (runNestS t)
  STKR n@SNat (STKX sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    unWindTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2)
                 (runNestX t)
  STKR n@SNat (STKProduct stk1 stk2) ->
    unWindTarget (STKProduct (STKR n stk1) (STKR n stk2)) (runzip t)
  STKS sh1 STKScalar -> withKnownShS sh1 $ WTKS t
  STKS sh1 (STKR m@(SNat @m) stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1)
                        `ssxAppend` ssxReplicate m) stk2) (sunNestR @_ @_ @m t)
  STKS sh1 (STKS sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh1 $ withKnownShS sh2 $
    unWindTarget (STKS (sh1 `shsAppend` sh2) stk2) (sunNest t)
  STKS sh1 (STKX sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $ withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShape (shCvtSX sh1) `ssxAppend` sh2) stk2)
                 (sunNestX t)
  STKS sh1 (STKProduct stk1 stk2)->
    unWindTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) (sunzip t)
  STKX sh1 STKScalar -> withKnownShX sh1 $ WTKX t
  STKX sh1 (STKR m@(SNat @m) stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh1 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2)
                 (xunNestR @_ @_ @m t)
  STKX sh1 (STKS sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh1 $ withKnownShS sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2)
                 (xunNestS t)
  STKX sh1 (STKX sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh1 $ withKnownShX sh2 $
    unWindTarget (STKX (sh1 `ssxAppend` sh2) stk2) (xunNest t)
  STKX sh1 (STKProduct stk1 stk2) ->
    unWindTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) (xunzip t)
  STKProduct stk1 stk2 ->
    let (t1, t2) = tunpairConv t
    in WTKProduct (unWindTarget stk1 t1) (unWindTarget stk2 t2)

windTarget :: ConvertTensor target
           => SingletonTK y -> RepW target (UnWind y) -> target y
windTarget stk t = case (stk, t) of
  (STKScalar, WTKScalar v) -> v
  (STKR _ STKScalar, WTKR v) -> v
  (STKR n@(SNat @n) (STKR (SNat @m) stk2), _)
   | Dict <- lemKnownSTK stk2 ->
    rnest n $ windTarget (STKR (SNat @(n + m)) stk2) t
  (STKR n (STKS sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    rnestS n
    $ windTarget (STKX (ssxReplicate n
                        `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  (STKR n (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    rnestX n
    $ windTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2) t
  (STKR n@SNat (STKProduct stk1 stk2), _) ->
    rzip $ windTarget (STKProduct (STKR n stk1) (STKR n stk2)) t
  (STKS _ STKScalar, WTKS v) -> v
  (STKS sh1 (STKR m@SNat stk2), _) | Dict <- lemKnownSTK stk2 ->
    snestR sh1
    $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                        `ssxAppend` ssxReplicate m) stk2) t
  (STKS sh1 (STKS sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    snest sh1 $ windTarget (STKS (shsAppend sh1 sh2) stk2) t
  (STKS sh1 (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    snestX sh1 $ windTarget (STKX (ssxFromShape (shCvtSX sh1)
                                   `ssxAppend` sh2) stk2) t
  (STKS sh1 (STKProduct stk1 stk2), _) ->
    szip $ windTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) t
  (STKX _ STKScalar, WTKX v) -> v
  (STKX sh1 (STKR m@SNat stk2), _) | Dict <- lemKnownSTK stk2 ->
    xnestR sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2) t
  (STKX sh1 (STKS sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    xnestS sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxFromShape (shCvtSX sh2)) stk2) t
  (STKX sh1 (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    xnest sh1 $ windTarget (STKX (ssxAppend sh1 sh2) stk2) t
  (STKX sh1 (STKProduct stk1 stk2), _) ->
    xzip $ windTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) t
  (STKProduct stk1 stk2, WTKProduct t1 t2) ->
    tpairConv (windTarget stk1 t1) (windTarget stk2 t2)


-- * Operations defined using unwinding

-- Requires duplicable arguments or a ShareTensor instance.
addTarget :: (BaseTensor target, ConvertTensor target)
          => SingletonTK y -> target y -> target y -> target y
addTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in windTarget stk $ addRepW a2 b2

-- Requires duplicable arguments or a ShareTensor instance.
multTarget :: (BaseTensor target, ConvertTensor target)
           => SingletonTK y -> target y -> target y -> target y
multTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in windTarget stk $ multRepW a2 b2

-- Dot product each component and then sum it all.
-- Requires duplicable arguments or a ShareTensor instance.
dotTarget :: (BaseTensor target, ConvertTensor target)
          => FullShapeTK y -> target y -> target y
          -> target (TKScalar Double)
dotTarget ftk a b =
  let a2 = unWindTarget (ftkToSTK ftk) a
      b2 = unWindTarget (ftkToSTK ftk) b
  in dotRepW (unWindFTK ftk) a2 b2

constantTarget :: forall y target. (BaseTensor target, ConvertTensor target)
               => (forall r. GoodScalar r => r)
               -> FullShapeTK y -> target y
constantTarget r ftk =
  windTarget (ftkToSTK ftk) $ constantRepW r (unWindFTK ftk)

defTarget :: forall y target. (BaseTensor target, ConvertTensor target)
          => FullShapeTK y -> target y
defTarget ftk =
  windTarget (ftkToSTK ftk) $ defRepW (unWindFTK ftk)

concreteTarget
  :: forall y target. (ConvertTensor RepN, ConvertTensor target)
  => (forall r. GoodScalar r => RepN (TKScalar r) -> target (TKScalar r))
  -> (forall r sh. GoodScalar r => RepN (TKS sh r) -> target (TKS sh r))
  -> (forall x z. SingletonTK z -> target x -> target z)
  -> SingletonTK y -> RepN y
  -> target y
concreteTarget concreteK concreteS fromS stk v =
  windTarget stk
  $ concreteRepW concreteK concreteS fromS
  $ unWindTarget stk v

lemUnWindOfAD :: SingletonTK y
              -> UnWind (ADTensorKind y) :~: ADTensorKind (UnWind y)
lemUnWindOfAD _ = unsafeCoerceRefl

-- The ShareTensor constraint is needed, despite what GHC says,
-- in order not to require duplicable arguments.
toADTensorKindShared
  :: (BaseTensor target, ConvertTensor target, ShareTensor target)
  => FullShapeTK y -> target y
  -> target (ADTensorKind y)
toADTensorKindShared ftk a | Refl <- lemUnWindOfAD (ftkToSTK ftk) =
  windTarget (adSTK $ ftkToSTK ftk)
  $ toADTensorKindW (unWindTarget (ftkToSTK ftk) a) (unWindFTK ftk)

-- The ShareTensor constraint is needed, despite what GHC says,
-- in order not to require duplicable arguments.
fromADTensorKindShared
  :: (BaseTensor target, ConvertTensor target, ShareTensor target)
  => SingletonTK y -> target (ADTensorKind y)
  -> target y
fromADTensorKindShared stk a | Refl <- lemUnWindOfAD stk =
  windTarget stk
  $ fromADTensorKindW (unWindSTK stk) $ unWindTarget (adSTK stk) a
