{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Types and functions needed to define general tensor operations
-- that work for any tensor kind, including nested (product) arrays
-- and an assortment of such operations.
--
-- Large portions of this module are copied to HordeAd.Core.UnwindNum
-- in order to have more accurate typing and pattern exhaustiveness checks.
module HordeAd.Core.Unwind
  ( defTarget, concreteTarget
  , nestTarget, nestTargetK, unNestTarget, unNestTargetK
  , toADTensorKindShared, fromADTensorKindShared
  ) where

import Prelude

import Data.Default
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.TypeLits (type (+))
import Type.Reflection (typeRep)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert
  (shxFromShR, shxFromShS, withShsFromShR, withShsFromShX)
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.OpsTensor

-- * Winding and unwinding

-- | This captures the normal form of type family UnWind and also
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

-- | This captures the normal form of type family UnWind for full shape
-- singletons.
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
  :: forall y target. (ConvertTensor Concrete, ConvertTensor target)
  => (forall r. GoodScalar r => Concrete (TKScalar r) -> target (TKScalar r))
  -> (forall r sh. GoodScalar r => Concrete (TKS sh r) -> target (TKS sh r))
  -> (forall x z. FullShapeTK z -> target x -> target z)
  -> RepW Concrete y -> RepW target y
{-# INLINE concreteRepW #-}
concreteRepW concreteK concreteS fromS w = case w of
  WTKScalar v -> WTKScalar $ concreteK v
  WTKR v -> WTKR $
    let sh' = Nested.rshape $ unConcrete v
    in withShsFromShR sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      fromS (FTKR sh' FTKScalar)
      $ concreteS (sfromR @_ @sh v)
  WTKS v -> WTKS $ concreteS v
  WTKX v -> WTKX $
    let sh' = Nested.mshape $ unConcrete v
    in withShsFromShX sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      fromS (FTKX sh' FTKScalar)
      $ concreteS (sfromX @_ @sh v)
  WTKProduct v1 v2 ->
    WTKProduct (concreteRepW concreteK concreteS fromS v1)
               (concreteRepW concreteK concreteS fromS v2)

toADTensorKindW
  :: forall y target. BaseTensor target
  => RepW target y -> FullShapeTKW y -> RepW target (ADTensorKind y)
toADTensorKindW t = \case
  WFTKScalar @r -> case testEquality (typeRep @(ADTensorScalar r))
                                     (typeRep @Z1) of
    Just Refl -> WTKScalar $ kconcrete Z1
    _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: r) t
  WFTKR @r sh -> case testEquality (typeRep @(ADTensorScalar r))
                                   (typeRep @Z1) of
    Just Refl -> WTKR $ rrepl @_ @_ @target sh Z1
    _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: r) t
  WFTKS @r sh -> case testEquality (typeRep @(ADTensorScalar r))
                                   (typeRep @Z1) of
    Just Refl -> WTKS $ sconcrete $ Nested.sreplicateScal sh Z1
    _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: r) t
  WFTKX @r sh -> case testEquality (typeRep @(ADTensorScalar r))
                                   (typeRep @Z1) of
    Just Refl -> WTKX $ xrepl @_ @_ @target sh Z1
    _ -> gcastWith (unsafeCoerceRefl :: ADTensorScalar r :~: r) t
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
      _ -> defRepW WFTKScalar
  (STKR _ (STKScalar @r1), WTKR @r2 v) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> defRepW (WFTKR (rshape v))
  (STKS sh (STKScalar @r1), WTKS @r2 _) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> defRepW (WFTKS sh)
  (STKX _ (STKScalar @r1), WTKX @r2 v) ->
    case testEquality (typeRep @r1) (typeRep @r2) of
      Just Refl -> t
      _ -> defRepW (WFTKX (xshape v))
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
    $ STKX (ssxReplicate n `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2
  STKR n (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxReplicate n `ssxAppend` sh2) stk2
  STKR n@SNat (STKProduct y z) ->
    unWindSTK $ STKProduct (STKR n y) (STKR n z)
  stk@(STKS _ STKScalar) -> stk
  STKS sh1 (STKR m stk2) ->
    unWindSTK
    $ STKX (ssxFromShX (shxFromShS sh1) `ssxAppend` ssxReplicate m) stk2
  STKS sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKS (sh1 `shsAppend` sh2) stk2
  STKS sh1 (STKX sh2 stk2) ->
    unWindSTK $ STKX (ssxFromShX (shxFromShS sh1) `ssxAppend` sh2) stk2
  STKS sh1 (STKProduct y z)->
    unWindSTK $ STKProduct (STKS sh1 y) (STKS sh1 z)
  stk@(STKX _ STKScalar) -> stk
  STKX sh1 (STKR m stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxReplicate m) stk2
  STKX sh1 (STKS sh2 stk2) ->
    unWindSTK $ STKX (sh1 `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2
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
    $ FTKX (shxFromShR sh1 `shxAppend` shxFromShS sh2) ftk2
  FTKR sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shxFromShR sh1 `shxAppend` sh2) ftk2
  FTKR sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKR sh1 y) (FTKR sh1 z)
  FTKS sh FTKScalar -> WFTKS sh
  FTKS sh1 (FTKR sh2 ftk2) ->
    unWindFTK
    $ FTKX (shxFromShS sh1 `shxAppend` shxFromShR sh2) ftk2
  FTKS sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKS (sh1 `shsAppend` sh2) ftk2
  FTKS sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shxFromShS sh1 `shxAppend` sh2) ftk2
  FTKS sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKS sh1 y) (FTKS sh1 z)
  FTKX sh FTKScalar -> WFTKX sh
  FTKX sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shxFromShR sh2) ftk2
  FTKX sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shxFromShS sh2) ftk2
  FTKX sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` sh2) ftk2
  FTKX sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKX sh1 y) (FTKX sh1 z)
  FTKProduct y z -> WFTKProduct (unWindFTK y) (unWindFTK z)

-- This uses tunpairConv, so to preserve sharing, @target@ either has
-- to have a `ShareTensor` instance or the argument has to be duplicable.
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
                        `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2)
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
    unWindTarget (STKX (ssxFromShX (shxFromShS sh1)
                        `ssxAppend` ssxReplicate m) stk2) (sunNestR @_ @_ @m t)
  STKS sh1 (STKS sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh1 $ withKnownShS sh2 $
    unWindTarget (STKS (sh1 `shsAppend` sh2) stk2) (sunNest t)
  STKS sh1 (STKX sh2 stk2) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $ withKnownShS sh1 $
    unWindTarget (STKX (ssxFromShX (shxFromShS sh1) `ssxAppend` sh2) stk2)
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
    unWindTarget (STKX (sh1 `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2)
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
                        `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2) t
  (STKR n (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    rnestX n
    $ windTarget (STKX (ssxReplicate n `ssxAppend` sh2) stk2) t
  (STKR n@SNat (STKProduct stk1 stk2), _) | Dict <- lemKnownSTK stk1
                                          , Dict <- lemKnownSTK stk2 ->
    rzip $ windTarget (STKProduct (STKR n stk1) (STKR n stk2)) t
  (STKS _ STKScalar, WTKS v) -> v
  (STKS sh1 (STKR m@SNat stk2), _) | Dict <- lemKnownSTK stk2 ->
    snestR sh1
    $ windTarget (STKX (ssxFromShX (shxFromShS sh1)
                        `ssxAppend` ssxReplicate m) stk2) t
  (STKS sh1 (STKS sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    snest sh1 $ windTarget (STKS (shsAppend sh1 sh2) stk2) t
  (STKS sh1 (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    snestX sh1 $ windTarget (STKX (ssxFromShX (shxFromShS sh1)
                                   `ssxAppend` sh2) stk2) t
  (STKS sh1 (STKProduct stk1 stk2), _) | Dict <- lemKnownSTK stk1
                                       , Dict <- lemKnownSTK stk2 ->
    szip $ windTarget (STKProduct (STKS sh1 stk1) (STKS sh1 stk2)) t
  (STKX _ STKScalar, WTKX v) -> v
  (STKX sh1 (STKR m@SNat stk2), _) | Dict <- lemKnownSTK stk2 ->
    xnestR sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxReplicate m) stk2) t
  (STKX sh1 (STKS sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShS sh2 $
    xnestS sh1
    $ windTarget (STKX (sh1 `ssxAppend` ssxFromShX (shxFromShS sh2)) stk2) t
  (STKX sh1 (STKX sh2 stk2), _) | Dict <- lemKnownSTK stk2 ->
    withKnownShX sh2 $
    xnest sh1 $ windTarget (STKX (ssxAppend sh1 sh2) stk2) t
  (STKX sh1 (STKProduct stk1 stk2), _) | Dict <- lemKnownSTK stk1
                                       , Dict <- lemKnownSTK stk2 ->
    xzip $ windTarget (STKProduct (STKX sh1 stk1) (STKX sh1 stk2)) t
  (STKProduct stk1 stk2, WTKProduct t1 t2) ->
    tpairConv (windTarget stk1 t1) (windTarget stk2 t2)


-- * Operations defined using unwinding

-- | Replicate the default value along the given full shape singleton.
defTarget :: forall y target. (BaseTensor target, ConvertTensor target)
          => FullShapeTK y -> target y
defTarget ftk =
  windTarget (ftkToSTK ftk) $ defRepW (unWindFTK ftk)

concreteTarget
  :: forall y target. (ConvertTensor Concrete, ConvertTensor target)
  => (forall r. GoodScalar r => Concrete (TKScalar r) -> target (TKScalar r))
  -> (forall r sh. GoodScalar r => Concrete (TKS sh r) -> target (TKS sh r))
  -> (forall x z. FullShapeTK z -> target x -> target z)
  -> SingletonTK y -> Concrete y
  -> target y
{-# INLINE concreteTarget #-}
concreteTarget concreteK concreteS fromS stk v =
  windTarget stk
  $ concreteRepW concreteK concreteS fromS
  $ unWindTarget stk v

-- | Convert a tensor into a trivial array with the tensor as the only element.
nestTarget :: forall y target. ConvertTensor target
           => SingletonTK y -> target y -> target (TKS2 '[] y)
nestTarget stk = tconvert (convCmp ConvXS (Conv0X stk)) stk

-- | Convert similarly as in @nestTarget@.
-- The argument has to be duplicable and y can't contain @TKR@ nor @TKX@.
nestTargetK :: forall k y target. ConvertTensor target
            => SNat k -> SingletonTK y
            -> target (BuildTensorKind k y)
            -> target (BuildTensorKind k (TKS2 '[] y))
nestTargetK k stk v =
  -- This coercion is correct given the assumptions.
  gcastWith (unsafeCoerceRefl :: UnWind (BuildTensorKind k (TKS2 '[] y))
                                 :~: UnWind (BuildTensorKind k y)) $
  windTarget (buildSTK k (STKS ZSS stk)) $ unWindTarget (buildSTK k stk) v

-- | Convert a tensor from a trivial array with the tensor as the only element.
unNestTarget :: forall y target. ConvertTensor target
             => SingletonTK y -> target (TKS2 '[] y) -> target y
unNestTarget stk = tconvert (convCmp ConvX0 ConvSX) (STKS ZSS stk)

-- | Convert similarly as in @unNestTarget@.
-- The argument has to be duplicable and y can't contain @TKR@ nor @TKX@.
unNestTargetK :: forall k y target. ConvertTensor target
              => SNat k -> SingletonTK y
              -> target (BuildTensorKind k (TKS2 '[] y))
              -> target (BuildTensorKind k y)
unNestTargetK k@SNat stk v =
  -- This coercion is correct given the assumptions.
  gcastWith (unsafeCoerceRefl :: UnWind (BuildTensorKind k (TKS2 '[] y))
                                 :~: UnWind (BuildTensorKind k y)) $
  windTarget (buildSTK k stk) $ unWindTarget (buildSTK k (STKS ZSS stk)) v

lemUnWindOfAD :: SingletonTK y
              -> UnWind (ADTensorKind y) :~: ADTensorKind (UnWind y)
lemUnWindOfAD _ = unsafeCoerceRefl

-- | Convert a tensor into a tensor with only trivial non-differentiable
-- scalars. The `ShareTensor` constraint is needed, despite what GHC says,
-- in order not to require duplicable arguments.
toADTensorKindShared
  :: (BaseTensor target, ConvertTensor target, ShareTensor target)
  => FullShapeTK y -> target y
  -> target (ADTensorKind y)
toADTensorKindShared ftk a | Refl <- lemUnWindOfAD (ftkToSTK ftk) =
  windTarget (adSTK $ ftkToSTK ftk)
  $ toADTensorKindW (unWindTarget (ftkToSTK ftk) a) (unWindFTK ftk)

-- | Convert a tensor with only trivial non-differentiable scalars
-- into a tensor with the non-differentiable scalars given by the singleton
-- and with zero values at the non-differentiable types. The `ShareTensor`
-- constraint is needed, despite what GHC says, in order not to require
-- duplicable arguments.
fromADTensorKindShared
  :: (BaseTensor target, ConvertTensor target, ShareTensor target)
  => SingletonTK y -> target (ADTensorKind y)
  -> target y
fromADTensorKindShared stk a | Refl <- lemUnWindOfAD stk =
  windTarget stk
  $ fromADTensorKindW (unWindSTK stk) $ unWindTarget (adSTK stk) a
