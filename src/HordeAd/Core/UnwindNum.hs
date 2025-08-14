{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Types and functions needed to define general tensor operations
-- that work for any tensor kind, including nested (product) arrays
-- and an assortment of such operations.
--
-- Large portions of this module are a copy of HordeAd.Core.Unwind
-- with the addition of the @Num@ constraint on the underlying scalars.
module HordeAd.Core.UnwindNum
  ( addTarget, multTarget, sum0Target, dot0Target
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (type (+))

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested.Convert
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

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
  WTKScalar :: NumScalar r
            => target (TKScalar r)
            -> RepW target (TKScalar r)
  WTKR :: NumScalar r
       => target (TKR n r)
       -> RepW target (TKR n r)
  WTKS :: NumScalar r
       => target (TKS sh r)
       -> RepW target (TKS sh r)
  WTKX :: NumScalar r
       => target (TKX sh r)
       -> RepW target (TKX sh r)
  WTKProduct :: RepW target x -> RepW target z
             -> RepW target (TKProduct x z)

-- | This captures the normal form of type family UnWind for full shape
-- singletons.
type role FullShapeTKW nominal
data FullShapeTKW y where
  WFTKScalar :: NumScalar r
             => FullShapeTKW (TKScalar r)
  WFTKR :: NumScalar r
        => IShR n -> FullShapeTKW (TKR n r)
  WFTKS :: NumScalar r
        => ShS sh -> FullShapeTKW (TKS sh r)
  WFTKX :: NumScalar r
        => IShX sh -> FullShapeTKW (TKX sh r)
  WFTKProduct :: FullShapeTKW y -> FullShapeTKW z
              -> FullShapeTKW (TKProduct y z)

addRepW :: forall y target. (TKAllNum y, BaseTensor target)
        => RepW target y -> RepW target y -> RepW target y
addRepW a b = case (a, b) of
  (WTKScalar ta, WTKScalar tb) -> WTKScalar $ ta + tb
  (WTKR ta, WTKR tb) -> WTKR $ ta + tb
  (WTKS ta, WTKS tb) -> WTKS $ ta + tb
  (WTKX ta, WTKX tb) -> WTKX $ ta + tb
  (WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    WTKProduct (addRepW ta1 tb1) (addRepW ta2 tb2)

multRepW :: forall y target. (TKAllNum y, BaseTensor target)
         => RepW target y -> RepW target y -> RepW target y
multRepW a b = case (a, b) of
  (WTKScalar ta, WTKScalar tb) -> WTKScalar $ ta * tb
  (WTKR ta, WTKR tb) -> WTKR $ ta * tb
  (WTKS ta, WTKS tb) -> WTKS $ ta * tb
  (WTKX ta, WTKX tb) -> WTKX $ ta * tb
  (WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    WTKProduct (multRepW ta1 tb1) (multRepW ta2 tb2)

sum0RepW :: forall y target.
            (TKAllNum y, BaseTensor target, ConvertTensor target)
         => FullShapeTKW y -> RepW target y
         -> target (TKScalar Double)
sum0RepW ftk a = case (ftk, a) of
  (_, WTKScalar @r ta) ->
    ifDifferentiable @r (kcast ta) 0
  (WFTKR sh, WTKR @r ta) | SNat <- shrRank sh ->
    ifDifferentiable @r (kcast $ kfromR $ rsum0 ta) 0
  (WFTKS sh, WTKS @r ta) ->
    withKnownShS sh $
    ifDifferentiable @r (kcast $ kfromS $ ssum0 ta) 0
  (WFTKX sh, WTKX @r ta) ->
    withKnownShX (ssxFromShX sh) $
    ifDifferentiable @r (kcast $ kfromX $ xsum0 ta) 0
  (WFTKProduct ftk1 ftk2, WTKProduct ta1 ta2) ->
    sum0RepW ftk1 ta1 + sum0RepW ftk2 ta2

dot0RepW :: forall y target.
            (TKAllNum y, BaseTensor target, ConvertTensor target)
         => FullShapeTKW y -> RepW target y -> RepW target y
         -> target (TKScalar Double)
dot0RepW ftk a b = case (ftk, a, b) of
  (_, WTKScalar @r ta, WTKScalar tb) ->
    ifDifferentiable @r (kcast $ ta * tb) 0
  (WFTKR sh, WTKR @r ta, WTKR tb) | SNat <- shrRank sh ->
    ifDifferentiable @r (kcast $ kfromR $ rdot0 ta tb) 0
  (WFTKS sh, WTKS @r ta, WTKS tb) ->
    withKnownShS sh $
    ifDifferentiable @r (kcast $ kfromS $ sdot0 ta tb) 0
  (WFTKX sh, WTKX @r ta, WTKX tb) ->
    withKnownShX (ssxFromShX sh) $
    ifDifferentiable @r (kcast $ kfromX $ xdot0 ta tb) 0
  (WFTKProduct ftk1 ftk2, WTKProduct ta1 ta2, WTKProduct tb1 tb2) ->
    dot0RepW ftk1 ta1 tb1 + dot0RepW ftk2 ta2 tb2

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

unWindFTK :: TKAllNum y
          => FullShapeTK y -> FullShapeTKW (UnWind y)
unWindFTK = \case
  FTKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) -> WFTKScalar
  FTKR sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) -> WFTKR sh
  FTKR sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKR (sh1 `shrAppend` sh2) ftk2
  FTKR sh1 (FTKS sh2 ftk2) ->
    unWindFTK
    $ FTKX (shxFromShR sh1 `shxAppend` shxFromShS sh2) ftk2
  FTKR sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shxFromShR sh1 `shxAppend` sh2) ftk2
  FTKR sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKR sh1 y) (FTKR sh1 z)
  FTKS sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) -> WFTKS sh
  FTKS sh1 (FTKR sh2 ftk2) ->
    unWindFTK
    $ FTKX (shxFromShS sh1 `shxAppend` shxFromShR sh2) ftk2
  FTKS sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKS (sh1 `shsAppend` sh2) ftk2
  FTKS sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (shxFromShS sh1 `shxAppend` sh2) ftk2
  FTKS sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKS sh1 y) (FTKS sh1 z)
  FTKX sh (FTKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) -> WFTKX sh
  FTKX sh1 (FTKR sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shxFromShR sh2) ftk2
  FTKX sh1 (FTKS sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` shxFromShS sh2) ftk2
  FTKX sh1 (FTKX sh2 ftk2) ->
    unWindFTK $ FTKX (sh1 `shxAppend` sh2) ftk2
  FTKX sh1 (FTKProduct y z) ->
    unWindFTK $ FTKProduct (FTKX sh1 y) (FTKX sh1 z)
  FTKProduct y z -> WFTKProduct (unWindFTK y) (unWindFTK z)

-- This uses tunpairConv so to preserve sharing, @target@ either has
-- to have a `ShareTensor` instance or the argument has to be duplicable.
-- Only the argument of the first call, not of recursive calls,
-- is assumed to be duplicable. In the AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
unWindTarget :: (TKAllNum y, ConvertTensor target)
             => SingletonTK y -> target y -> RepW target (UnWind y)
unWindTarget stk t = case stk of
  STKScalar @r | Dict0 <- numFromTKAllNum (Proxy @r) ->
    WTKScalar t
  STKR SNat (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
    WTKR t
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
  STKS sh1 (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
    withKnownShS sh1 $ WTKS t
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
  STKX sh1 (STKScalar @r) | Dict0 <- numFromTKAllNum (Proxy @r) ->
    withKnownShX sh1 $ WTKX t
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

-- | Add two (nested pairs of) tensors. Requires duplicable arguments
-- or a `ShareTensor` instance.
addTarget :: forall y target.
             (TKAllNum y, BaseTensor target, ConvertTensor target)
          => SingletonTK y -> target y -> target y -> target y
addTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in gcastWith (unsafeCoerceRefl :: TKAllNum (UnWind y) :~: TKAllNum y)
     $ windTarget stk $ addRepW a2 b2

-- | Multiply two (nested pairs of) tensors. Requires duplicable arguments
-- or a `ShareTensor` instance.
multTarget :: forall y target.
              (TKAllNum y, BaseTensor target, ConvertTensor target)
           => SingletonTK y -> target y -> target y -> target y
multTarget stk a b =
  let a2 = unWindTarget stk a
      b2 = unWindTarget stk b
  in gcastWith (unsafeCoerceRefl :: TKAllNum (UnWind y) :~: TKAllNum y)
     $ windTarget stk $ multRepW a2 b2

-- | Sum all dimensions of each component and then sum it all.
-- Requires duplicable arguments or a `ShareTensor` instance.
sum0Target :: forall y target.
              (TKAllNum y, BaseTensor target, ConvertTensor target)
           => FullShapeTK y -> target y
           -> target (TKScalar Double)
sum0Target ftk a =
  let a2 = unWindTarget (ftkToSTK ftk) a
  in gcastWith (unsafeCoerceRefl :: TKAllNum (UnWind y) :~: TKAllNum y)
     $ sum0RepW (unWindFTK ftk) a2

-- | Dot product each component and then sum it all.
-- Requires duplicable arguments or a `ShareTensor` instance.
dot0Target :: forall y target.
              (TKAllNum y, BaseTensor target, ConvertTensor target)
           => FullShapeTK y -> target y -> target y
           -> target (TKScalar Double)
dot0Target ftk a b =
  let a2 = unWindTarget (ftkToSTK ftk) a
      b2 = unWindTarget (ftkToSTK ftk) b
  in gcastWith (unsafeCoerceRefl :: TKAllNum (UnWind y) :~: TKAllNum y)
     $ dot0RepW (unWindFTK ftk) a2 b2
