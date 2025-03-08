{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class for converting tensors to other forms that contain the same
-- data but have different types.
module HordeAd.Core.ConvertTensor
  ( ConvertTensor(..)
  ) where

import Prelude

import Data.Type.Equality (gcastWith, (:~:))
import GHC.TypeLits (KnownNat, Nat, type (+))

import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested.Internal.Lemmas
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

class ConvertTensor (target :: Target) where
  -- The semantics for products is element-wise and for others it's either
  -- identity or the domain is shaped and tfromS type-casts to the codomain
  -- by hiding some (or none) type information (so the codomain has to be
  -- a "subtype" of the domain) or error.
  -- A corollary is that tfromS behaves uniformly vs BuildTensorKind.
  tfromS :: SingletonTK y -> SingletonTK z -> target y -> target z

  kfromR :: GoodScalar r => target (TKR 0 r) -> target (TKScalar r)
  kfromR = kfromS . sfromR
  kfromS :: GoodScalar r => target (TKS '[] r) -> target (TKScalar r)
  kfromS = tfromS knownSTK knownSTK
  kfromX :: GoodScalar r => target (TKX '[] r) -> target (TKScalar r)
  kfromX = kfromS . sfromX
  rfromK :: GoodScalar r => target (TKScalar r) -> target (TKR 0 r)
  rfromK = rfromS . sfromK
  rfromS :: (KnownShS sh, KnownSTK x)
         => target (TKS2 sh x) -> target (TKR2 (Rank sh) x)
  rfromS @sh @x = tfromS knownSTK (STKR (shsRank (knownShS @sh)) (knownSTK @x))
  rfromX :: forall sh x. KnownSTK x
         => target (TKX2 sh x) -> target (TKR2 (Rank sh) x)
  sfromK :: GoodScalar r => target (TKScalar r) -> target (TKS '[] r)
  sfromR :: (KnownShS sh, KnownSTK x)
         => target (TKR2 (Rank sh) x) -> target (TKS2 sh x)
  sfromX :: (KnownShS sh, Rank sh ~ Rank sh', KnownSTK x)
         => target (TKX2 sh' x) -> target (TKS2 sh x)
  xfromK :: GoodScalar r => target (TKScalar r) -> target (TKX '[] r)
  xfromK = xfromS . sfromK
  xfromR :: (KnownShX sh', KnownSTK x)
         => target (TKR2 (Rank sh') x) -> target (TKX2 sh' x)
  xfromS :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK x)
         => target (TKS2 sh x) -> target (TKX2 sh' x)
  xfromS = tfromS knownSTK knownSTK

  rzip :: forall y z n.
          target (TKProduct (TKR2 n y) (TKR2 n z))
       -> target (TKR2 n (TKProduct y z))
  runzip :: forall y z n.
            target (TKR2 n (TKProduct y z))
         -> target (TKProduct (TKR2 n y) (TKR2 n z))
  szip :: forall y z sh.
          target (TKProduct (TKS2 sh y) (TKS2 sh z))
       -> target (TKS2 sh (TKProduct y z))
  sunzip :: forall y z sh.
            target (TKS2 sh (TKProduct y z))
         -> target (TKProduct (TKS2 sh y) (TKS2 sh z))
  xzip :: forall y z sh.
          target (TKProduct (TKX2 sh y) (TKX2 sh z))
       -> target (TKX2 sh (TKProduct y z))
  xunzip :: forall y z sh.
            target (TKX2 sh (TKProduct y z))
         -> target (TKProduct (TKX2 sh y) (TKX2 sh z))

  rnest :: forall n m x.
           (KnownNat m, KnownSTK x)
        => SNat n -> target (TKR2 (n + m) x)
        -> target (TKR2 n (TKR2 m x))
  rnest n@SNat =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)
                                         ++ Replicate m Nothing) :~: n + m) $
    gcastWith (unsafeCoerceRefl :: Replicate (n + m) (Nothing @Nat)
                                    :~: Replicate n (Nothing @Nat)
                                        ++ Replicate m Nothing) $
    withKnownShX (ssxReplicate n) $
    withKnownShX (ssxReplicate (SNat @(n + m))) $
    rfromX . xnestR (ssxReplicate n) . xfromR @_ @(Replicate (n + m) Nothing)
  -- Some of these operations have akward type signatures, but these
  -- are the most type-safe or the strongest versions of the typing possible.
  rnestS :: forall n sh2 x.
            (KnownShS sh2, KnownSTK x)
         => SNat n -> target (TKX2 (Replicate n Nothing ++ MapJust sh2) x)
         -> target (TKR2 n (TKS2 sh2 x))
  rnestS n@SNat =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate n) $
    rfromX . xnestS (ssxReplicate n)
  rnestX :: forall n sh2 x.
            (KnownShX sh2, KnownSTK x)
         => SNat n -> target (TKX2 (Replicate n Nothing ++ sh2) x)
         -> target (TKR2 n (TKX2 sh2 x))
  rnestX n@SNat =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate n) $
    rfromX . xnest (ssxReplicate n)
  snestR :: forall sh1 m x.
            (KnownNat m, KnownSTK x)
         => ShS sh1 -> target (TKX2 (MapJust sh1 ++ Replicate m Nothing) x)
         -> target (TKS2 sh1 (TKR2 m x))
  snestR sh1 =
    gcastWith (lemRankMapJust sh1) $
    withKnownShS sh1 $
    withKnownShX (ssxFromShape (shCvtSX sh1)) $
    sfromX . xnestR (ssxFromShape (shCvtSX sh1))
  snest :: forall sh1 sh2 x.
           (KnownShS sh2, KnownSTK x)
        => ShS sh1 -> target (TKS2 (sh1 ++ sh2) x)
        -> target (TKS2 sh1 (TKS2 sh2 x))
  snest sh1 =
    gcastWith (lemRankMapJust sh1) $
    gcastWith (unsafeCoerceRefl :: Rank (MapJust sh1 ++ MapJust sh2)
                                    :~: Rank (sh1 ++ sh2)) $
    withKnownShS sh1 $
    withKnownShX (ssxFromShape (shCvtSX sh1)) $
    withKnownShS (sh1 `shsAppend` knownShS @sh2) $
    withKnownShX (ssxFromShape (shCvtSX sh1)
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    sfromX . xnestS (ssxFromShape (shCvtSX sh1)) . xfromS
  snestX :: forall sh1 sh2 x.
            (KnownShX sh2, KnownSTK x)
         => ShS sh1 -> target (TKX2 (MapJust sh1 ++ sh2) x)
         -> target (TKS2 sh1 (TKX2 sh2 x))
  snestX sh1 =
    gcastWith (lemRankMapJust sh1) $
    withKnownShS sh1 $
    withKnownShX (ssxFromShape (shCvtSX sh1)) $
    sfromX . xnest (ssxFromShape (shCvtSX sh1))
  -- These three are primitives; the others are defined from them.
  xnestR :: forall sh1 m x.
            (KnownNat m, KnownSTK x)
         => StaticShX sh1 -> target (TKX2 (sh1 ++ Replicate m Nothing) x)
         -> target (TKX2 sh1 (TKR2 m x))
  xnestS :: forall sh1 sh2 x.
            (KnownShS sh2, KnownSTK x)
         => StaticShX sh1 -> target (TKX2 (sh1 ++ MapJust sh2) x)
         -> target (TKX2 sh1 (TKS2 sh2 x))
  xnest :: forall sh1 sh2 x.
           (KnownShX sh2, KnownSTK x)
        => StaticShX sh1 -> target (TKX2 (sh1 ++ sh2) x)
        -> target (TKX2 sh1 (TKX2 sh2 x))

  runNest :: (KnownNat n, KnownNat m, KnownSTK x)
          => target (TKR2 n (TKR2 m x)) -> target (TKR2 (n + m) x)
  runNest @n @m =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)
                                          ++ Replicate m Nothing) :~: n + m) $
    withKnownShX (ssxReplicate (SNat @n)) $
    withKnownShX (ssxReplicate (SNat @n) `ssxAppend` ssxReplicate (SNat @m)) $
    rfromX . xunNestR . xfromR @_ @(Replicate n Nothing)
  runNestS :: (KnownNat n, KnownShS sh2, KnownSTK x)
           => target (TKR2 n (TKS2 sh2 x))
           -> target (TKX2 (Replicate n Nothing ++ MapJust sh2) x)
  runNestS @n =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate (SNat @n)) $
    xunNestS . xfromR @_ @(Replicate n Nothing)
  runNestX :: (KnownNat n, KnownShX sh2, KnownSTK x)
           => target (TKR2 n (TKX2 sh2 x))
           -> target (TKX2 (Replicate n Nothing ++ sh2) x)
  runNestX @n @sh2=
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate (SNat @n)) $
    withKnownShX (ssxReplicate (SNat @n) `ssxAppend` knownShX @sh2) $
    xunNest . xfromR @_ @(Replicate n Nothing)
  sunNestR :: (KnownShS sh1, KnownNat m, KnownSTK x)
           => target (TKS2 sh1 (TKR2 m x))
           -> target (TKX2 (MapJust sh1 ++ Replicate m Nothing) x)
  sunNestR @sh1 =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    xunNestR . xfromS @_ @_ @(MapJust sh1)
  sunNest :: (KnownShS sh1, KnownShS sh2, KnownSTK x)
          => target (TKS2 sh1 (TKS2 sh2 x)) -> target (TKS2 (sh1 ++ sh2) x)
  sunNest @sh1 @sh2 =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    gcastWith (unsafeCoerceRefl
               :: Rank (MapJust sh1 ++ MapJust sh2) :~: Rank (sh1 ++ sh2)) $
    withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    sfromX . xunNestS . xfromS @_ @_ @(MapJust sh1)
  sunNestX :: (KnownShS sh1, KnownShX sh2, KnownSTK x)
           => target (TKS2 sh1 (TKX2 sh2 x))
           -> target (TKX2 (MapJust sh1 ++ sh2) x)
  sunNestX @sh1 @sh2 =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))
                  `ssxAppend` knownShX @sh2) $
    xunNest . xfromS @_ @_ @(MapJust sh1)
  -- These three are primitives; the others are defined from them.
  xunNestR :: (KnownShX sh1, KnownNat m, KnownSTK x)
           => target (TKX2 sh1 (TKR2 m x))
           -> target (TKX2 (sh1 ++ Replicate m Nothing) x)
  xunNestS :: (KnownShX sh1, KnownShS sh2, KnownSTK x)
           => target (TKX2 sh1 (TKS2 sh2 x))
           -> target (TKX2 (sh1 ++ MapJust sh2) x)
  xunNest :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
          => target (TKX2 sh1 (TKX2 sh2 x)) -> target (TKX2 (sh1 ++ sh2) x)

  -- Two aliases to make the class sufficient for Unwind.
  -- | A clone of tpair, to make this class independent of @BaseTensor@
  -- but sufficient for "Unwind".
  tpairConv :: target x -> target z -> target (TKProduct x z)
  -- | A clone of tunpair, if @ShareTensor@ is available, or an implementation
  -- that duplicates the argument, otherwise.
  tunpairConv :: target (TKProduct x z) -> (target x, target z)
