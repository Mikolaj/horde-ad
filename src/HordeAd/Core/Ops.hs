{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library and it's relatively orthogonal to the
-- differentiation interface in "HordeAd.Core.Engine".
module HordeAd.Core.Ops
  ( -- * The tensor classes
    LetTensor(..), ShareTensor(..), BaseTensor(..)
  , HFun(..)
  , tunit
  , rscalar, rrepl, ringestData
  , sscalar, srepl, singestData
  , xscalar, xrepl, xingestData
    -- * The giga-constraint
  , ADReady, ADReadyNoLet, AllTargetShow
  ) where

import Prelude

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Foldable qualified as Foldable
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.Exts (IsList (..))
import GHC.TypeLits
  (KnownNat, Nat, OrderingI (..), cmpNat, type (+), type (-), type (<=))
import Numeric.LinearAlgebra (Numeric)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  ( IShX
  , fromSMayNat
  , fromSMayNat'
  , shxAppend
  , shxDropSSX
  , shxSize
  , shxTakeSSX
  , ssxAppend
  , ssxFromShape
  , ssxReplicate
  , withKnownShX
  )
import Data.Array.Mixed.Types (Init)
import Data.Array.Nested
  ( IShR
  , IxR (..)
  , IxS (..)
  , IxX (..)
  , KnownShS (..)
  , KnownShX (..)
  , ListR (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , StaticShX (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Lemmas
import Data.Array.Nested.Internal.Shape
  ( listrRank
  , shCvtSX
  , shrAppend
  , shrRank
  , shrSize
  , shsAppend
  , shsProduct
  , shsRank
  , shsSize
  , withKnownShS
  )

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- Note that no Ast* module except AstInterpret and AstEnv
-- depends on any Tensor*, Carriers* and Ops* modules
-- and vice versa except CarriersAst and OpsAst.
-- Syntax is separated from semantics and they meet in the interpreter
-- and in the semantic model constructed from syntax (TensorAst).

type TensorSupports :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupports c1 c2 f =
  forall r. GoodScalar r
            => c1 r => c2 (f (TKScalar r))

type TensorSupportsR :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsR c1 c2 f =
  forall r n. (GoodScalar r, KnownNat n)
              => c1 r => c2 (f (TKR n r))

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsS c1 c2 f =
  forall r sh. (GoodScalar r, KnownShS sh)
               => c1 r => c2 (f (TKS sh r))

type TensorSupportsX :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsX c1 c2 f =
  forall r sh. (GoodScalar r, KnownShX sh)
               => c1 r => c2 (f (TKX sh r))

class (RealFloatF r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloatF r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class LetTensor (target :: Target) where
  twidth :: STensorKind y -> Int
  twidth stk = case stk of
    STKScalar{} -> 1
    STKR{} -> 1
    STKS{} -> 1
    STKX{} -> 1
    STKProduct stk1 stk2 -> twidth @target stk1 + twidth @target stk2
  tsize :: BaseTensor target => STensorKind y -> target y -> Int
  tsize stk a = case stk of
    STKScalar{} -> 1
    STKR SNat x | Dict <- lemKnownSTK x -> rsize a
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ ssize a
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xsize a
    STKProduct stk1 stk2 | Dict <- lemKnownSTK stk1
                         , Dict <- lemKnownSTK stk2 ->
      tsize stk1 (tproject1 a) + tsize stk2 (tproject2 a)
  tlet :: (KnownSTK x, KnownSTK z)
       => target x
       -> (target x -> target z)
       -> target z
  toShare :: KnownSTK y
          => target y
          -> ShareOf target y
  tunshare :: KnownSTK y
           => ShareOf target y
           -> target y
  tunshare = error "tunshare: this instance should never be used"
  tfromVector :: forall y k. BaseTensor target
              => SNat k -> STensorKind y -> Data.Vector.Vector (target y)
              -> target (BuildTensorKind k y)
  tfromVector snat@SNat stk v = case stk of
    STKScalar{} -> sfromVector $ V.map sfromK v
    STKR SNat x | Dict <- lemKnownSTK x ->
      rfromVector v
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ sfromVector v
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xfromVector v
    STKProduct @y1 @y2 stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let f :: ([target y1] -> [target y2] -> target (BuildTensorKind k y))
              -> target y
              -> ([target y1] -> [target y2] -> target (BuildTensorKind k y))
            f acc u = \l1 l2 ->
              tlet u $ \ u3 ->
                acc (tproject1 u3 : l1) (tproject2 u3 : l2)
            res :: [target y1] -> [target y2] -> target (BuildTensorKind k y)
            res l1 l2 =
              tpair (tfromVector snat stk1 (V.fromList l1))
                    (tfromVector snat stk2 (V.fromList l2))
        in V.foldl' f res v [] []  -- TODO: verify via tests this is not reversed
  tfromListR :: forall y k. BaseTensor target
             => STensorKind y -> ListR k (target y)
             -> target (BuildTensorKind k y)
  tfromListR stk l =
    tfromVector (listrRank l) stk . V.fromList . Foldable.toList $ l
  tsum :: forall z k. BaseTensor target
       => SNat k -> STensorKind z
       -> target (BuildTensorKind k z)
       -> target z
  tsum snat@SNat stk u = case stk of
    STKScalar{} -> kfromS $ ssum u
    STKR SNat x | Dict <- lemKnownSTK x ->
      rsum u
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ ssum u
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xsum u
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        tlet u $ \ !u3 ->
          tpair (tsum snat stk1 (tproject1 u3))
                (tsum snat stk2 (tproject2 u3))
  treplicate :: forall z k. BaseTensor target
             => SNat k -> STensorKind z
             -> target z
             -> target (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar{} -> sreplicate $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> rreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ sreplicate u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xreplicate u
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        tlet u $ \ !u3 ->
          tpair (treplicate snat stk1 (tproject1 u3))
                (treplicate snat stk2 (tproject2 u3))
  -- The semantics for products is element-wise and for others it's either
  -- identity or the domain is shaped and tfromS type-casts to the codomain
  -- by hiding some (or none) type information (so the codomain has to be
  -- a "subtype" of the domain) or error.
  -- A corollary is that tfromS behaves uniformly vs BuildTensorKind.
  tfromS :: forall y z. (BaseTensor target, KnownSTK y, KnownSTK z)
         => target y -> target z
  tfromS v = case (knownSTK @y, knownSTK @z) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> v
    (STKS ZSS (STKScalar try), STKScalar trz) -> case testEquality try trz of
      Just Refl -> kfromS v
      Nothing -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKR zn zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) zn) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          rfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKX shz zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shz)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shz $
          xfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKProduct stky1 stky2, STKProduct stkz1 stkz2)
      | Dict <- lemKnownSTK stky1
      , Dict <- lemKnownSTK stky2
      , Dict <- lemKnownSTK stkz1
      , Dict <- lemKnownSTK stkz2 ->
        tlet v $ \ !u3 ->
          tpair (tfromS (tproject1 u3)) (tfromS (tproject2 u3))
    _ -> error "tfromS: wrong tensor kinds"
  tD :: BaseTensor target
     => STensorKind y -> PrimalOf target y -> DualOf target y
     -> target y
  tD stk p d | Dict <- lemKnownSTK stk =
    -- Lets needed, because raddTarget requires duplicable arguments.
    tlet (tfromPrimal stk p) $ \pShared ->
    tlet (tfromDual stk d) $ \dShared ->
      taddTarget stk pShared dShared

class ShareTensor (target :: Target) where
  tshare :: KnownSTK y
         => target y -> target y
  tunpair :: (KnownSTK x, KnownSTK z)
          => target (TKProduct x z) -> (target x, target z)
  tfromVectorShare :: forall y k. BaseTensor target
                   => SNat k -> STensorKind y
                   -> Data.Vector.Vector (target y)
                   -> target (BuildTensorKind k y)
  tfromVectorShare snat@SNat stk v = case stk of
    STKScalar{} -> sfromVector $ V.map sfromK v
    STKR SNat x | Dict <- lemKnownSTK x ->
      rfromVector v
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ sfromVector v
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xfromVector v
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let (v1, v2) = V.unzip $ V.map tunpair v
        in tpair (tfromVectorShare snat stk1 v1)
                 (tfromVectorShare snat stk2 v2)
  tunravelToListShare :: forall y k. BaseTensor target
                      => SNat k -> STensorKind y
                      -> target (BuildTensorKind k y)
                      -> [target y]
  tunravelToListShare snat@SNat stk u = case stk of
    STKScalar{} -> map kfromS $ sunravelToList u
    STKR SNat x | Dict <- lemKnownSTK x ->
      runravelToList u
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ sunravelToList u
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xunravelToList u
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let (u1, u2) = tunpair u
        in zipWith tpair (tunravelToListShare snat stk1 u1)
                         (tunravelToListShare snat stk2 u2)
  tsumShare :: forall z k. BaseTensor target
            => SNat k -> STensorKind z
            -> target (BuildTensorKind k z)
            -> target z
  tsumShare snat@SNat stk u = case stk of
    STKScalar{} -> kfromS $ ssum u
    STKR SNat x | Dict <- lemKnownSTK x ->
      rsum u
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ ssum u
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xsum u
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let (u1, u2) = tunpair u
        in tpair (tsumShare snat stk1 u1)
                 (tsumShare snat stk2 u2)
  treplicateShare :: BaseTensor target
                  => SNat k -> STensorKind z
                  -> target z
                  -> target (BuildTensorKind k z)
  treplicateShare snat@SNat stk u = case stk of
    STKScalar{} -> sreplicate $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> rreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ sreplicate u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xreplicate u
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let (u1, u2) = tunpair u
        in tpair (treplicateShare snat stk1 u1)
                 (treplicateShare snat stk2 u2)
  tindexBuildShare :: forall z k. BaseTensor target
                   => SNat k -> STensorKind z
                   -> target (BuildTensorKind k z) -> IntOf target
                   -> target z
  tindexBuildShare snat@SNat stk u i = case stk of
    STKScalar{} -> kfromS $ sindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x ->
      rindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ sindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xindex u (i :.% ZIX)
    STKProduct stk1 stk2
      | Dict <- lemKnownSTK stk1
      , Dict <- lemKnownSTK stk2
      , Dict <- lemKnownSTKOfBuild snat stk1
      , Dict <- lemKnownSTKOfBuild snat stk2 ->
        let (u1, u2) = tunpair u
        in tpair (tindexBuildShare snat stk1 u1 i)
                 (tindexBuildShare snat stk2 u2 i)
  tfromSShare :: forall y z. (BaseTensor target, KnownSTK y, KnownSTK z)
              => target y -> target z
  tfromSShare v = case (knownSTK @y, knownSTK @z) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> v
    (STKS ZSS (STKScalar try), STKScalar trz) -> case testEquality try trz of
      Just Refl -> kfromS v
      Nothing -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKR nx zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          rfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemKnownSTK yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shx $
          xfromS v
        _ -> error "tfromS: tensor kinds don't match"
    (STKProduct stky1 stky2, STKProduct stkz1 stkz2)
      | Dict <- lemKnownSTK stky1
      , Dict <- lemKnownSTK stky2
      , Dict <- lemKnownSTK stkz1
      , Dict <- lemKnownSTK stkz2 ->
        let (u1, u2) = tunpair v
        in tpair (tfromSShare u1) (tfromSShare u2)
    _ -> error "tfromS: wrong tensor kinds"

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Num (IntOf target)
      , IntegralF (IntOf target)
      , TensorSupports Num Num target
      , TensorSupports RealFloatAndFloatElt Floating target
      , TensorSupports RealFloatAndFloatElt RealFloatF target
      , TensorSupports IntegralF IntegralF target
      , TensorSupportsR Num Num target
      , TensorSupportsR RealFloatAndFloatElt Floating target
      , TensorSupportsR RealFloatAndFloatElt RealFloatF target
      , TensorSupportsR IntegralF IntegralF target
      , TensorSupportsS Num Num target
      , TensorSupportsS RealFloatAndFloatElt Floating target
      , TensorSupportsS RealFloatAndFloatElt RealFloatF target
      , TensorSupportsS IntegralF IntegralF target
      , TensorSupportsX Num Num target
      , TensorSupportsX RealFloatAndFloatElt Floating target
      , TensorSupportsX RealFloatAndFloatElt RealFloatF target
      , TensorSupportsX IntegralF IntegralF target )
      => BaseTensor (target :: Target) where

  -- Methods needed only to split off the module that defines them
  tconstantTarget
    :: (forall r. GoodScalar r => r) -> FullTensorKind y -> target y
  -- The arguments need to be duplicable
  taddTarget :: STensorKind y -> target y -> target y -> target y

  -- Ranked ops
  -- A number suffix in the name may indicate the rank of the codomain,
  -- if bounded. Suffix 1 may also mean the operations builds up codomain
  -- by 1 dimension.
  rshape :: KnownSTK r => target (TKR2 n r) -> IShR n
  rrank :: forall r n. (KnownSTK r, KnownNat n) => target (TKR2 n r) -> Int
  rrank _ = valueOf @n
  rsize :: KnownSTK r => target (TKR2 n r) -> Int
  rsize = shrSize . rshape
  rlength :: KnownSTK r => target (TKR2 (1 + n) r) -> Int
  rlength v = case rshape v of
    k :$: _ -> k

  rconcrete :: (KnownSTK r, KnownNat n)
            => Nested.Ranked n (RepORArray r) -> target (TKR2 n r)
  rconcrete a = tconcrete (tftkG (STKR SNat knownSTK) a) (RepN a)
  rfromList :: (KnownSTK r, KnownNat n)
            => NonEmpty (target (TKR2 n r)) -> target (TKR2 (1 + n) r)
  rfromList = rfromVector . V.fromList . NonEmpty.toList
    -- going through strict vectors, because laziness is risky with impurity
  rfromListLinear :: (KnownSTK r, KnownNat n)
                  => IShR n -> [target (TKR2 0 r)] -> target (TKR2 n r)
  rfromListLinear sh = rfromVectorLinear sh . V.fromList
  -- This is morally non-empty strict vectors:
  rfromVector :: (KnownSTK r, KnownNat n)
              => Data.Vector.Vector (target (TKR2 n r))
              -> target (TKR2 (1 + n) r)
  rfromVectorLinear :: forall r n. (KnownSTK r, KnownNat n)
                    => IShR n -> Data.Vector.Vector (target (TKR2 0 r))
                    -> target (TKR2 n r)
  rfromVectorLinear sh v | Dict <- eltDictRep (knownSTK @r) =
    if V.null v
    then rreshape sh $ rconcrete Nested.remptyArray
    else rreshape sh $ rfromVector v
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  runravelToList :: forall r n. (KnownSTK r, KnownNat n)
                 => target (TKR2 (1 + n) r) -> [target (TKR2 n r)]
  runravelToList t =
    let f :: Int -> target (TKR2 n r)
        f i = rindex t (fromIntegral i :.: ZIR)
    in map f [0 .. rlength t - 1]
  rsum :: (KnownSTK r, KnownNat n)
       => target (TKR2 (1 + n) r) -> target (TKR2 n r)
  -- This op (and it's Delta constructor) is worthwhile, because flattening
  -- is O(n) sometimes, unlike transpose, etc.
  rsum0 :: (KnownSTK r, KnownNat n)
        => target (TKR2 n r) -> target (TKR2 0 r)
  rsum0 = rsum . rflatten
  rdot0 :: (GoodScalar r, KnownNat n)
        => target (TKR n r) -> target (TKR n r) -> target (TKR 0 r)
  rdot0 t u = rsum (rflatten (t * u))
  rdot1In :: GoodScalar r
          => target (TKR 2 r) -> target (TKR 2 r)
          -> target (TKR 1 r)  -- TODO: generalize
  rdot1In t u = rsum $ rtr (t * u)
  rmatvecmul :: GoodScalar r
             => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
-- rmatvecmul m v = rbuild1 (rlength m) (\i -> rdot0 v (m ! [i]))
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  rmatvecmul m v = rsum (rtranspose [1,0] (rreplicate (rlength m) v * m))
  rmatmul2 :: (GoodScalar r, Numeric r)
           => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
-- rmatmul2 m1 m2 = rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR ->
      rsum (rtranspose [2,1,0] (rreplicate width2 m1)
            * rtranspose [1,0] (rreplicate (rlength m1) m2))
  rscaleByScalar :: (GoodScalar r, KnownNat n)
                 => target (TKR 0 r) -> target (TKR n r) -> target (TKR n r)
  rscaleByScalar s v = v * rreplicate0N (rshape v) s
  rreplicate :: (KnownSTK r, KnownNat n)
             => Int -> target (TKR2 n r) -> target (TKR2 (1 + n) r)
  rreplicate0N :: (KnownSTK r, KnownNat n)
               => IShR n -> target (TKR2 0 r) -> target (TKR2 n r)
  rreplicate0N sh = rreshape sh . rreplicate (shrSize sh)
  -- First index is for outermost dimension; empty index means identity,
  -- if index is out of bounds, the result is defined and is 0,
  -- but vectorization is permitted to change the value.
  rindex, (!) :: (KnownSTK r, KnownNat m, KnownNat n)
              => target (TKR2 (m + n) r) -> IxROf target m -> target (TKR2 n r)
  infixl 9 !
  (!) = rindex  -- prefix form better when type applications are necessary
  rindex0 :: (KnownSTK r, KnownNat m)
          => target (TKR2 m r) -> IxROf target m -> target (TKR2 0 r)
  rindex0 = rindex
  roneHot :: forall r m n.
             ( KnownSTK r, KnownNat m, KnownNat n
             , BoolOf (PrimalOf target) ~ BoolOf target
             , EqF (PrimalOf target) )
          => IShR m -> target (TKR2 n r) -> IxROf target m
          -> target (TKR2 (m + n) r)
  roneHot sh v ix = case knownSTK @r of
    STKScalar{} ->
      rscatter @_ @_ @0
               (shrAppend sh (rshape v)) v (const ix)
    _ -> case tftk knownSTK v of
      FTKR _ ftk2 ->
        -- TODO: def at out of bounds
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (toList ix) (toList ix2))
                        (rindex0 v (dropIndex ix2))
                        (tconstantTarget 0 (FTKR ZSR ftk2))
        in rbuild (shrAppend sh (rshape v)) f
           -- TODO: if this is used often, maybe express this as the gather that
           -- would come out of vectorization, making sure it simplifies well
  rscatter :: (KnownSTK r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> target (TKR2 (m + n) r)
           -> (IxROf target m -> IxROf target p)
           -> target (TKR2 (p + n) r)
  rscatter1 :: forall r n p. (KnownSTK r, KnownNat n, KnownNat p)
            => IShR (p + n) -> target (TKR2 (1 + n) r)
            -> (IntOf target -> IxROf target p)
            -> target (TKR2 (p + n) r)
  rscatter1 sh v f = rscatter @target @r @1 sh v
                              (\(i :.: ZIR) -> f i)
  rgather :: (KnownSTK r, KnownNat m, KnownNat n, KnownNat p)
          => IShR (m + n) -> target (TKR2 (p + n) r)
          -> (IxROf target m -> IxROf target p)
          -> target (TKR2 (m + n) r)
  rgather1 :: forall r n p. (KnownSTK r, KnownNat n, KnownNat p)
           => Int -> target (TKR2 (p + n) r)
           -> (IntOf target -> IxROf target p)
           -> target (TKR2 (1 + n) r)
  rgather1 k v f = rgather @target @r @1
                           (k :$: dropShape (rshape v)) v
                           (\(i :.: ZIR) -> f i)
  rfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => target (TKR n r) -> target (TKR n r2)
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => target (TKR n r1) -> target (TKR n r2)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => target (TKR n r1) -> target (TKR n r2)
  rminIndex, rmaxIndex  -- partial
    :: (GoodScalar r, GoodScalar r2, KnownNat n)
    => target (TKR (1 + n) r) -> target (TKR n r2)
  riota :: GoodScalar r => Int -> target (TKR 1 r)  -- from 0 to n - 1
  rappend :: (KnownSTK r, KnownNat n)
          => target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
          -> target (TKR2 (1 + n) r)
  rconcat :: (KnownSTK r, KnownNat n)
          => NonEmpty (target (TKR2 (1 + n) r)) -> target (TKR2 (1 + n) r)
  rconcat = foldr1 rappend
  rslice :: (KnownSTK r, KnownNat n)
         => Int -> Int -> target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
  runcons :: (KnownSTK r, KnownNat n)
          => target (TKR2 (1 + n) r)
          -> Maybe (target (TKR2 n r), target (TKR2 (1 + n) r))
  runcons v = case rshape v of
                len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
  rreverse :: (KnownSTK r, KnownNat n)
           => target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r)
  rtr :: (KnownSTK r, KnownNat n)
      => target (TKR2 (2 + n) r) -> target (TKR2 (2 + n) r)
  rtr = rtranspose [1, 0]
  rtranspose :: (KnownSTK r, KnownNat n)
             => Permutation.PermR -> target (TKR2 n r) -> target (TKR2 n r)
  rflatten :: (KnownSTK r, KnownNat n) => target (TKR2 n r) -> target (TKR2 1 r)
  rflatten u = rreshape (rsize u :$: ZSR) u
  rreshape :: (KnownSTK r, KnownNat n, KnownNat m)
           => IShR m -> target (TKR2 n r) -> target (TKR2 m r)
  rzip :: (KnownSTK y, KnownSTK z, KnownNat n)
       => target (TKProduct (TKR2 n y) (TKR2 n z))
       -> target (TKR2 n (TKProduct y z))
  runzip :: (KnownSTK y, KnownSTK z, KnownNat n)
         => target (TKR2 n (TKProduct y z))
         -> target (TKProduct (TKR2 n y) (TKR2 n z))

  rbuild :: forall r m n. (KnownSTK r, KnownNat m, KnownNat n)
         => IShR (m + n) -> (IxROf target m -> target (TKR2 n r))
         -> target (TKR2 (m + n) r)
  rbuild sh0 f0 =
    let buildSh :: IShR m1 -> (IxROf target m1 -> target (TKR2 n r))
                -> target (TKR2 (m1 + n) r)
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | SNat <- shrRank sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in rbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  rbuild1 :: (KnownSTK r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf target -> target (TKR2 n r))
          -> target (TKR2 (1 + n) r)
  rmap :: (KnownSTK r, KnownSTK r2, KnownNat m, KnownNat n)
       => (target (TKR2 n r) -> target (TKR2 n r2))
       -> target (TKR2 (m + n) r) -> target (TKR2 (m + n) r2)
  rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
  rmap1 :: (KnownSTK r, KnownSTK r2, KnownNat n)
        => (target (TKR2 n r) -> target (TKR2 n r2))
        -> target (TKR2 (1 + n) r) -> target (TKR2 (1 + n) r2)
  rmap1 f u = rbuild1 (rlength u) (\i -> f (u ! [i]))
  rmap0N :: (KnownSTK r, KnownSTK r1, KnownNat n)
         => (target (TKR2 0 r1) -> target (TKR2 0 r)) -> target (TKR2 n r1)
         -> target (TKR2 n r)
  rmap0N f v = rbuild (rshape v) (f . rindex0 v)
  rzipWith :: ( KnownSTK r1, KnownSTK r2, KnownSTK r
              , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n )
           => IShR (m + n)
           -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
           -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2)
           -> target (TKR2 (m + n) r)
  rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
  rzipWith1 :: ( KnownSTK r1, KnownSTK r2, KnownSTK r
               , KnownNat n1, KnownNat n2, KnownNat n )
            => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
            -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n) r)
  rzipWith1 f u v = rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]))
  rzipWith0N :: (KnownSTK r1, KnownSTK r2, KnownSTK r, KnownNat n)
             => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r))
             -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r)
  rzipWith0N f u v = rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))
  rzipWith3 :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
               , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
            => IShR (m + n)
            -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
            -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
            -> target (TKR2 (m + n) r)
  rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
  rzipWith31 :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
             => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
             -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
             -> target (TKR2 (1 + n) r)
  rzipWith31 f u v w =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
  rzipWith30N :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
                 , KnownNat n )
              => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r))
              -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r)
  rzipWith30N f u v w =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
  rzipWith4 :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
               , KnownSTK r, KnownNat m
               , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
               , KnownNat n )
            => IShR (m + n)
            -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
                -> target (TKR2 n r))
            -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
            -> target (TKR2 (m + n4) r4)
            -> target (TKR2 (m + n) r)
  rzipWith4 sh f u v w x =
    rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
  rzipWith41 :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
                , KnownSTK r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
                , KnownNat n )
             => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
                 -> target (TKR2 n r))
             -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
             -> target (TKR2 (1 + n4) r4)
             -> target (TKR2 (1 + n) r)
  rzipWith41 f u v w x =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
  rzipWith40N :: ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
                 , KnownSTK r
                 , KnownNat n )
              => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r4)
                  -> target (TKR2 0 r))
              -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r4)
              -> target (TKR2 n r)
  rzipWith40N f u v w x =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                                (rindex0 x ix))

  rprimalPart :: (KnownSTK r, KnownNat n)
              => target (TKR2 n r) -> PrimalOf target (TKR2 n r)
  rprimalPart = tprimalPart knownSTK
  rdualPart :: (KnownSTK r, KnownNat n)
            => target (TKR2 n r) -> DualOf target (TKR2 n r)
  rdualPart = tdualPart knownSTK
  rfromPrimal :: (KnownSTK r, KnownNat n)
              => PrimalOf target (TKR2 n r) -> target (TKR2 n r)
  rfromPrimal = tfromPrimal knownSTK
  rfromDual :: (KnownSTK r, KnownNat n)
            => DualOf target (TKR2 n r) -> target (TKR2 n r)
  rfromDual = tfromDual knownSTK
  rScale :: ( GoodScalar r, KnownNat n
            , Num (target (TKR n r)), Num (PrimalOf target (TKR n r)) )
         => PrimalOf target (TKR n r) -> DualOf target (TKR n r)
         -> DualOf target (TKR n r)
  rScale = tScale @target knownSTK

  -- Shaped ops
  sshape :: forall sh r. (KnownSTK r, KnownShS sh)
         => target (TKS2 sh r) -> ShS sh
  sshape _ = knownShS @sh
  srank :: forall sh r. (KnownSTK r, KnownNat (Rank sh))
        => target (TKS2 sh r) -> Int
  srank _ = valueOf @(Rank sh)
  ssize :: forall sh r. (KnownSTK r, KnownShS sh) => target (TKS2 sh r) -> Int
  ssize _ = shsSize (knownShS @sh)
  slength :: forall r n sh. (KnownSTK r, KnownNat n)
          => target (TKS2 (n ': sh) r) -> Int
  slength _ = valueOf @n

  sconcrete :: (KnownSTK r, KnownShS sh)
            => Nested.Shaped sh (RepORArray r) -> target (TKS2 sh r)
  sconcrete a = tconcrete (tftkG (STKS knownShS knownSTK) a) (RepN a)
  sfromList :: (KnownSTK r, KnownNat n, KnownShS sh)
            => NonEmpty (target (TKS2 sh r)) -> target (TKS2 (n ': sh) r)
  sfromList = sfromVector . V.fromList . NonEmpty.toList
  sfromListLinear :: (KnownSTK r, KnownShS sh, KnownNat (Nested.Product sh))
                  => [target (TKS2 '[] r)] -> target (TKS2 sh r)
  sfromListLinear = sfromVectorLinear . V.fromList
  -- This is morally non-empty strict vectors:
  sfromVector :: (KnownSTK r, KnownNat n, KnownShS sh)
              => Data.Vector.Vector (target (TKS2 sh r))
              -> target (TKS2 (n ': sh) r)
  sfromVectorLinear :: forall r sh.
                       (KnownSTK r, KnownShS sh, KnownNat (Nested.Product sh))
                    => Data.Vector.Vector (target (TKS2 '[] r))
                    -> target (TKS2 sh r)
  sfromVectorLinear v | Dict <- eltDictRep (knownSTK @r) =
    if V.null v
    then gcastWith (unsafeCoerceRefl :: Nested.Product sh :~: 0) $
         sreshape $ sconcrete $ Nested.semptyArray ZSS
    else sreshape @_ @r @'[Nested.Product sh] @sh $ sfromVector v
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  sunravelToList :: forall r n sh. (KnownSTK r, KnownNat n, KnownShS sh)
                 => target (TKS2 (n ': sh) r) -> [target (TKS2 sh r)]
  sunravelToList t =
    let f :: Int -> target (TKS2 sh r)
        f i = sindex t (fromIntegral i :.$ ZIS)
    in map f [0 .. slength t - 1]
  ssum :: (KnownSTK r, KnownNat n, KnownShS sh)
       => target (TKS2 (n ': sh) r) -> target (TKS2 sh r)
  ssum0 :: forall r sh. (KnownSTK r, KnownShS sh)
        => target (TKS2 sh r) -> target (TKS2 '[] r)
  ssum0 | SNat <- shsProduct (knownShS @sh) = ssum . sflatten
  sdot0 :: forall r sh. (GoodScalar r, KnownShS sh)
        => target (TKS sh r) -> target (TKS sh r) -> target (TKS '[] r)
  sdot0 t u | SNat <- shsProduct (knownShS @sh) = ssum (sflatten (t * u))
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => SNat n
          -> target (TKS '[m, n] r) -> target (TKS '[m, n] r)
          -> target (TKS '[m] r)  -- TODO: generalize
  sdot1In _ t u = ssum $ str (t * u)
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => target (TKS '[m, n] r) -> target (TKS '[n] r)
             -> target (TKS '[m] r)
  smatvecmul m v =
    ssum (stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @_ @m v * m))
  smatmul2 :: forall r n m p.
              (GoodScalar r, Numeric r, KnownNat n, KnownNat m, KnownNat p)
           => target (TKS '[m, n] r) -> target (TKS '[n, p] r)
           -> target (TKS '[m, p] r)
  smatmul2 m1 m2 =
    ssum (stranspose (Permutation.makePerm @'[2, 1, 0]) (sreplicate @target @p m1)
          * stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @target @m m2))
  sscaleByScalar
    :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
    => target (TKS '[] r) -> target (TKS sh r) -> target (TKS sh r)
  sscaleByScalar s v = v * sreplicate0N s
  sreplicate :: (KnownNat k, KnownShS sh, KnownSTK r)
             => target (TKS2 sh r) -> target (TKS2 (k ': sh) r)
  sreplicate0N :: forall r sh.
                  (KnownSTK r, KnownShS sh, KnownNat (Nested.Product sh))
               => target (TKS2 '[] r) -> target (TKS2 sh r)
  sreplicate0N = sreshape @target @r @'[Nested.Product sh] @sh
                 . sreplicate @target @(Nested.Product sh)
  sindex, (!$) :: ( KnownSTK r, KnownShS shm, KnownShS shn
                  , KnownShS (shm ++ shn) )
               => target (TKS2 (shm ++ shn) r) -> IxSOf target shm
               -> target (TKS2 shn r)
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall sh1 r. (KnownShS sh1, KnownSTK r)
          => target (TKS2 sh1 r) -> IxSOf target sh1
          -> target (TKS2 '[] r)
  sindex0 | Refl <- lemAppNil @sh1 = sindex
  soneHot :: forall r sh1 sh2.
             ( KnownSTK r, KnownShS sh1, KnownShS sh2
             , KnownShS (sh1 ++ sh2)
             , BoolOf (PrimalOf target) ~ BoolOf target
             , EqF (PrimalOf target) )
          => target (TKS2 sh2 r) -> IxSOf target sh1
          -> target (TKS2 (sh1 ++ sh2) r)
  soneHot v ix | SNat <- shsRank (knownShS @sh1) = case knownSTK @r of
    STKScalar{} ->
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      sscatter @_ @_ @'[] @_ @sh1 v (const ix)
    _ -> case tftk knownSTK v of
      FTKS _ ftk2 ->
        -- TODO: def at out of bounds
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: '[]) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: (sh1 ++ sh2)) $
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (toList ix) (toList ix2))
                        (sindex0 v (dropIxS @(Rank sh1) ix2))
                        (tconstantTarget 0 (FTKS ZSS ftk2))
        in sbuild @_ @_ @(Rank (sh1 ++ sh2)) f
  sscatter
    :: (KnownSTK r, KnownShS shm, KnownShS shn, KnownShS shp)
    => target (TKS2 (shm ++ shn) r)
    -> (IxSOf target shm -> IxSOf target shp)
    -> target (TKS2 (shp ++ shn) r)
  sscatter1
    :: forall r n2 shn shp.
       (KnownSTK r, KnownNat n2, KnownShS shn, KnownShS shp)
    => target (TKS2 (n2 ': shn) r)
    -> (IntOf target -> IxSOf target shp)
    -> target (TKS2 (shp ++ shn) r)
  sscatter1 v f = sscatter @_ @r @'[n2] v (\(i :.$ _) -> f i)
  sgather
    :: (KnownSTK r, KnownShS shm, KnownShS shn, KnownShS shp)
    => target (TKS2 (shp ++ shn) r)
    -> (IxSOf target shm -> IxSOf target shp)
    -> target (TKS2 (shm ++ shn) r)
  sgather1
    :: forall r n2 shn shp.
       (KnownSTK r, KnownNat n2, KnownShS shn, KnownShS shp)
    => target (TKS2 (shp ++ shn) r)
    -> (IntOf target -> IxSOf target shp)
    -> target (TKS2 (n2 ': shn) r)
  sgather1 v f = sgather @target @r @'[n2] v (\(i :.$ _) -> f i)
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShS sh)
         => target (TKS sh r) -> target (TKS sh r2)
    -- the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                => target (TKS sh r1) -> target (TKS sh r2)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownShS sh)
        => target (TKS sh r1) -> target (TKS sh r2)
  sminIndex, smaxIndex  -- partial
    :: (GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n)
    => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
  siota :: (KnownNat n, GoodScalar r)
        => target (TKS '[n] r)  -- from 0 to n - 1
  sappend :: (KnownSTK r, KnownNat m, KnownNat n, KnownShS sh)
          => target (TKS2 (m ': sh) r) -> target (TKS2 (n ': sh) r)
          -> target (TKS2 ((m + n) ': sh) r)
  sslice :: (KnownSTK r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Proxy i -> Proxy n
         -> target (TKS2 (i + n + k ': sh) r) -> target (TKS2 (n ': sh) r)
  suncons :: forall r n sh. (KnownSTK r, KnownNat n, KnownShS sh)
          => target (TKS2 (n ': sh) r)
          -> Maybe (target (TKS2 sh r), target (TKS2 (n - 1 ': sh) r))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @_ @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @_ @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (KnownSTK r, KnownNat n, KnownShS sh)
           => target (TKS2 (n ': sh) r) -> target (TKS2 (n ': sh) r)
  str :: ( KnownSTK r, KnownNat n, KnownNat m, KnownShS sh
         , KnownNat (Rank sh) )
      => target (TKS2 (n ': m ': sh) r) -> target (TKS2 (m ': n ': sh) r)
  str = stranspose (Permutation.makePerm @'[1, 0])
  stranspose :: ( PermC perm, KnownSTK r, KnownShS sh
                , Rank perm <= Rank sh  )
             => Permutation.Perm perm -> target (TKS2 sh r)
             -> target (TKS2 (Permutation.PermutePrefix perm sh) r)
  sflatten :: (KnownSTK r, KnownShS sh, KnownNat (Nested.Product sh))
           => target (TKS2 sh r) -> target (TKS2 '[Nested.Product sh] r)
  sflatten = sreshape
  sreshape :: ( KnownSTK r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2 )
           => target (TKS2 sh r) -> target (TKS2 sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  szip :: (KnownSTK y, KnownSTK z, KnownShS sh)
       => target (TKProduct (TKS2 sh y) (TKS2 sh z))
       -> target (TKS2 sh (TKProduct y z))
  sunzip :: (KnownSTK y, KnownSTK z, KnownShS sh)
         => target (TKS2 sh (TKProduct y z))
         -> target (TKProduct (TKS2 sh y) (TKS2 sh z))

  sbuild :: forall r m sh. (KnownSTK r, KnownShS sh, KnownShS (Take m sh))
         => (IxSOf target (Take m sh) -> target (TKS2 (Drop m sh) r))
         -> target (TKS2 sh r)
  sbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IxSOf target sh1 -> target (TKS2 (Drop m sh) r))
          -> target (TKS2 (sh1 ++ Drop m sh) r)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          (SNat :$$ sh2, _ :$$ sh2m) ->
            withKnownShS sh2m $
            let g i = buildSh sh2 sh2m (f . (i :.$))
            in sbuild1 g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (knownShS @(Take m sh)) (knownShS @sh)
  sbuild1 :: (KnownNat k, KnownShS sh, KnownSTK r)
          => (IntOf target -> target (TKS2 sh r))
          -> target (TKS2 (k ': sh) r)
  smap :: forall r r2 m sh.
          ( KnownSTK r, KnownSTK r2, KnownNat m
          , KnownShS sh, KnownShS (Take m sh), KnownShS (Drop m sh) )
       => (target (TKS2 (Drop m sh) r) -> target (TKS2 (Drop m sh) r2))
       -> target (TKS2 sh r) -> target (TKS2 sh r2)
  smap f v = gcastWith (unsafeCoerceRefl
                        :: sh :~: Take m sh ++ Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r sh n r2.
           (KnownSTK r, KnownSTK r2, KnownNat n, KnownShS sh)
        => (target (TKS2 sh r) -> target (TKS2 sh r2))
        -> target (TKS2 (n ': sh) r) -> target (TKS2 (n ': sh) r2)
  smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
  smap0N :: forall r1 r sh.
            (KnownSTK r1, KnownSTK r, KnownShS sh)
         => (target (TKS2 '[] r1) -> target (TKS2 '[] r)) -> target (TKS2 sh r1)
         -> target (TKS2 sh r)
  smap0N f v =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @r @(Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( KnownSTK r1, KnownSTK r2, KnownSTK r
              , KnownNat m, KnownShS sh1, KnownShS sh2, KnownShS sh
              , KnownShS (Take m sh), KnownShS (Drop m sh1)
              , KnownShS (Drop m sh2), KnownShS (Drop m sh)
              , sh1 ~ Take m sh ++ Drop m sh1
              , sh2 ~ Take m sh ++ Drop m sh2 )
           => (target (TKS2 (Drop m sh1) r1)
               -> target (TKS2 (Drop m sh2) r2)
               -> target (TKS2 (Drop m sh) r))
           -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r)
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( KnownSTK r1, KnownSTK r2, KnownSTK r
               , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh )
            => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r))
            -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
            -> target (TKS2 (n ': sh) r)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                     (v !$ (i :.$ ZIS)))
  szipWith0N :: forall r1 r2 r sh.
                (KnownSTK r1, KnownSTK r2, KnownSTK r, KnownShS sh)
             => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r))
             -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r)
  szipWith0N f u v =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  szipWith3 :: forall r1 r2 r3 r m sh1 sh2 sh3 sh.
               ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
               , KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3 )
            => (target (TKS2 (Drop m sh1) r1)
                -> target (TKS2 (Drop m sh2) r2)
                -> target (TKS2 (Drop m sh3) r3)
                -> target (TKS2 (Drop m sh) r))
            -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r)
  szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
  szipWith31 :: forall r1 r2 r3 r n sh1 sh2 sh3 sh.
                ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
                , KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh )
             => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r))
             -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
             -> target (TKS2 (n ': sh3) r3)
             -> target (TKS2 (n ': sh) r)
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS)))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
                 , KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                  -> target (TKS2 '[] r))
              -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r)
  szipWith30N f u v w =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix))
  szipWith4 :: forall r1 r2 r3 r4 r m sh1 sh2 sh3 sh4 sh.
               ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
               , KnownSTK r, KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
               , KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh4), KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3
               , sh4 ~ Take m sh ++ Drop m sh4 )
            => (target (TKS2 (Drop m sh1) r1)
                -> target (TKS2 (Drop m sh2) r2)
                -> target (TKS2 (Drop m sh3) r3)
                -> target (TKS2 (Drop m sh4) r4)
                -> target (TKS2 (Drop m sh) r))
            -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh4 r4)
            -> target (TKS2 sh r)
  szipWith4 f u v w x =
    sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
  szipWith41 :: forall r1 r2 r3 r4 r n sh1 sh2 sh3 sh4 sh.
                ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
                , KnownSTK r, KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
                , KnownShS sh )
             => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3)
                 -> target (TKS2 sh4 r4) -> target (TKS2 sh r))
             -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
             -> target (TKS2 (n ': sh3) r3) -> target (TKS2 (n ': sh4) r4)
             -> target (TKS2 (n ': sh) r)
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                          (v !$ (i :.$ ZIS))
                                          (w !$ (i :.$ ZIS))
                                          (x !$ (i :.$ ZIS)))
  szipWith40N :: forall r1 r2 r3 sh r4 r.
                 ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
                 , KnownSTK r, KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                  -> target (TKS2 '[] r4) -> target (TKS2 '[] r))
              -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r4)
              -> target (TKS2 sh r)
  szipWith40N f u v w x =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix)
                                                (sindex0 x ix))

  sprimalPart :: (KnownSTK r, KnownShS sh)
              => target (TKS2 sh r) -> PrimalOf target (TKS2 sh r)
  sprimalPart = tprimalPart knownSTK
  sdualPart :: (KnownSTK r, KnownShS sh)
            => target (TKS2 sh r) -> DualOf target (TKS2 sh r)
  sdualPart = tdualPart knownSTK
  sfromPrimal :: (KnownSTK r, KnownShS sh)
              => PrimalOf target (TKS2 sh r) -> target (TKS2 sh r)
  sfromPrimal = tfromPrimal knownSTK
  sfromDual :: (KnownSTK r, KnownShS sh)
            => DualOf target (TKS2 sh r) -> target (TKS2 sh r)
  sfromDual = tfromDual knownSTK
  sScale :: (GoodScalar r, KnownShS sh, Num (target (TKS sh r)), Num (PrimalOf target (TKS sh r)))
         => PrimalOf target (TKS sh r) -> DualOf target (TKS sh r)
         -> DualOf target (TKS sh r)
  sScale = tScale @target knownSTK

  -- Mixed ops
  xshape :: KnownSTK r => target (TKX2 sh r) -> IShX sh
  xrank :: forall r sh. (KnownSTK r, KnownNat (Rank sh))
        => target (TKX2 sh r) -> Int
  xrank _ = valueOf @(Rank sh)
  xsize :: KnownSTK r => target (TKX2 sh r) -> Int
  xsize = shxSize . xshape
  xlength :: KnownSTK r => target (TKX2 (mn ': sh) r) -> Int
  xlength v = case xshape v of
    mn :$% _ -> fromSMayNat' mn

  xmcast :: (KnownSTK x, KnownShX sh, Rank sh ~ Rank sh2)
         => StaticShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)
  xmcast sh2 a = case tftk knownSTK a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShX sh2 $
        withKnownShS sh $
        xfromS $ sfromX @_ @sh a
  xconcrete :: (KnownSTK r, KnownShX sh)
            => Nested.Mixed sh (RepORArray r) -> target (TKX2 sh r)
  xconcrete a = tconcrete (tftkG (STKX knownShX knownSTK) a) (RepN a)
  xfromList :: forall r n sh. (KnownSTK r, KnownNat n, KnownShX sh)
            => NonEmpty (target (TKX2 sh r)) -> target (TKX2 (Just n ': sh) r)
  xfromList = xfromVector
              . V.fromList . NonEmpty.toList
    -- going through strict vectors, because laziness is risky with impurity
  xfromListLinear :: (KnownSTK r, KnownShX sh)
                  => IShX sh -> [target (TKX2 '[] r)] -> target (TKX2 sh r)
  xfromListLinear sh = xfromVectorLinear sh . V.fromList
  xfromVector :: (KnownSTK r, KnownNat n, KnownShX sh)
              => Data.Vector.Vector (target (TKX2 sh r))
              -> target (TKX2 (Just n ': sh) r)
  xfromVectorLinear :: forall r sh. (KnownSTK r, KnownShX sh)
                    => IShX sh -> Data.Vector.Vector (target (TKX2 '[] r))
                    -> target (TKX2 sh r)
  xfromVectorLinear sh v | Dict <- eltDictRep (knownSTK @r) =
    if V.null v
    then xreshape sh $ xconcrete $ Nested.memptyArray ZSX
    else withSNat (shxSize sh) $ \(SNat @n) ->
           xreshape @_ @_ @'[Just n] sh $ xfromVector v
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  xunravelToList :: forall r n sh. (KnownSTK r, KnownNat n, KnownShX sh)
                 => target (TKX2 (Just n ': sh) r) -> [target (TKX2 sh r)]
  xunravelToList t =
    let f :: Int -> target (TKX2 sh r)
        f i = xindex t (fromIntegral i :.% ZIX)
    in map f [0 .. xlength t - 1]
  -- The choice in BuildTensorKind makes it hard to support this one,
  -- due to DeltaSum and AstSum being typed with BuildTensorKind:
  -- xsum :: (KnownSTK r, KnownShX sh, KnownShX (mn ': sh))
  --     => target (TKX2 (mn ': sh) r) -> target (TKX2 sh r)
  xsum :: (KnownSTK r, KnownNat n, KnownShX sh)
       => target (TKX2 (Just n ': sh) r) -> target (TKX2 sh r)
  xsum0 :: (KnownSTK r, KnownShX sh)
        => target (TKX2 sh r) -> target (TKX2 '[] r)
  xsum0 t = withSNat (shxSize $ xshape t) $ \snat ->
    xsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  xdot0 :: (GoodScalar r, KnownShX sh)
        => target (TKX sh r) -> target (TKX sh r) -> target (TKX '[] r)
  xdot0 t u = withSNat (shxSize $ xshape t) $ \snat ->
    xsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten (t * u))
  xdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => target (TKX '[Just m, Just n] r)
          -> target (TKX '[Just m, Just n] r)
          -> target (TKX '[Just m] r)  -- TODO: generalize
  xdot1In t u = xsum $ xtr (t * u)
  xmatvecmul :: forall r mm mn. GoodScalar r
             => Nested.SMayNat Int SNat mm -> Nested.SMayNat () SNat mn
             -> target (TKX '[mm, mn] r) -> target (TKX '[mn] r)
             -> target (TKX '[mm] r)
  -- This variant is not vectorized, so will be slow without vectorization.
  xmatvecmul mm mn u v =
    let mu :: Nested.SMayNat () SNat mm
        mu = fromSMayNat (const $ Nested.SUnknown ()) Nested.SKnown mm
    in withKnownShX (mu :!% ZKX) $
       withKnownShX (mu :!% mn :!% ZKX) $
       withKnownShX (mn :!% ZKX) $
       withSNat (fromSMayNat' mm) $ \(SNat @n) ->
         xmcast (mu :!% ZKX)
         $ xbuild1 @_ @n @'[] (\i -> xdot0 v (u `xindex` (i :.% ZIX)))
  -- TODO: when we switch to singletons, generalize this to non-Just types
  -- or split into ranked-style and shaped-style variants or provide
  -- convenient ways to lift ranked and shaped operations into mixed.
  xmatmul2 :: forall r n m p.
              (GoodScalar r, Numeric r, KnownNat n, KnownNat m, KnownNat p)
           => target (TKX '[Just m, Just n] r)
           -> target (TKX '[Just n, Just p] r)
           -> target (TKX '[Just m, Just p] r)
  xmatmul2 m1 m2 =
    xsum (xtranspose (Permutation.makePerm @'[2, 1, 0]) (xreplicate @target @p m1)
          * xtranspose (Permutation.makePerm @'[1, 0]) (xreplicate @target @m m2))
  xscaleByScalar
    :: (GoodScalar r, KnownShX sh)
    => target (TKX '[] r) -> target (TKX sh r) -> target (TKX sh r)
  xscaleByScalar s v = v * xreplicate0N (xshape v) s
  xreplicate :: (KnownNat k, KnownShX sh, KnownSTK r)
             => target (TKX2 sh r) -> target (TKX2 (Just k ': sh) r)
  xreplicate0N :: (KnownSTK r, KnownShX sh)
               => IShX sh -> target (TKX2 '[] r) -> target (TKX2 sh r)
  xreplicate0N sh = withSNat (shxSize sh) $ \ (SNat @k) ->
    xreshape sh . xreplicate @_ @k
  xindex :: ( KnownSTK r, KnownShX sh1, KnownShX sh2
            , KnownShX (sh1 ++ sh2) )
         => target (TKX2 (sh1 ++ sh2) r) -> IxXOf target sh1
         -> target (TKX2 sh2 r)
  xindex0 :: forall r sh1. (KnownSTK r, KnownShX sh1)
          => target (TKX2 sh1 r) -> IxXOf target sh1
          -> target (TKX2 '[] r)
  xindex0 | Refl <- lemAppNil @sh1 = xindex
  xoneHot :: forall r sh1 sh2.
             ( KnownSTK r, KnownShX sh1, KnownShX sh2
             , KnownShX (sh1 ++ sh2)
             , BoolOf (PrimalOf target) ~ BoolOf target
             , EqF (PrimalOf target) )
          => IShX sh1 -> target (TKX2 sh2 r) -> IxXOf target sh1
          -> target (TKX2 (sh1 ++ sh2) r)
  xoneHot sh1 v ix | SNat <- ssxRank (knownShX @sh1) = case knownSTK @r of
    STKScalar{} ->
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      xscatter @_ @_ @'[] @_ @sh1 (shxAppend sh1 (xshape v)) v (const ix)
    _ -> case tftk knownSTK v of
      FTKX _ ftk2 ->
        -- TODO: def at out of bounds
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: '[]) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: (sh1 ++ sh2)) $
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (toList ix) (toList ix2))
                        (xindex0 v (dropIxX @(Rank sh1) ix2))
                        (tconstantTarget 0 (FTKX ZSX ftk2))
        in xbuild @_ @_ @(Rank (sh1 ++ sh2)) (shxAppend sh1 (xshape v)) f
  xscatter :: (KnownSTK r, KnownShX shm, KnownShX shn, KnownShX shp)
           => IShX (shp ++ shn) -> target (TKX2 (shm ++ shn) r)
           -> (IxXOf target shm -> IxXOf target shp)
           -> target (TKX2 (shp ++ shn) r)
  -- TODO: when we switch to singletons, generalize this to non-Just types.
  xscatter1 :: forall r n2 shn shp.
               (KnownSTK r, KnownNat n2, KnownShX shn, KnownShX shp)
            => IShX (shp ++ shn) -> target (TKX2 (Just n2 ': shn) r)
            -> (IntOf target -> IxXOf target shp)
            -> target (TKX2 (shp ++ shn) r)
  xscatter1 sh v f = xscatter @_ @r @'[Just n2] @_ @shp sh v
                              (\(i :.% _) -> f i)
  xgather :: (KnownSTK r, KnownShX shm, KnownShX shn, KnownShX shp)
          => IShX (shm ++ shn)
          -> target (TKX2 (shp ++ shn) r)
          -> (IxXOf target shm -> IxXOf target shp)
          -> target (TKX2 (shm ++ shn) r)
  xgather1 :: forall r n2 shn shp.
              (KnownSTK r, KnownNat n2, KnownShX shn, KnownShX shp)
           => SNat n2 -> target (TKX2 (shp ++ shn) r)
           -> (IntOf target -> IxXOf target shp)
           -> target (TKX2 (Just n2 ': shn) r)
  xgather1 k v f =
    xgather @target @r @'[Just n2]
            (Nested.SKnown k :$% shxDropSSX (xshape v) (knownShX @shp)) v
            (\(i :.% ZIX) -> f i)
  xfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShX sh)
         => target (TKX sh r) -> target (TKX sh r2)
  xfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShX sh)
                => target (TKX sh r1) -> target (TKX sh r2)
  xcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownShX sh)
        => target (TKX sh r1) -> target (TKX sh r2)
  xminIndex, xmaxIndex  -- partial
    :: (GoodScalar r, GoodScalar r2, KnownShX sh, KnownShX (Init (mn ': sh)))
    => target (TKX (mn ': sh) r) -> target (TKX (Init (mn ': sh)) r2)
  xiota :: (KnownNat n, GoodScalar r)
        => target (TKX '[Just n] r)  -- from 0 to n - 1
  xappend :: (KnownSTK r, KnownShX sh)
          => target (TKX2 (Nothing ': sh) r) -> target (TKX2 (Nothing ': sh) r)
          -> target (TKX2 (Nothing ': sh) r)
  xconcat :: (KnownSTK r, KnownShX sh)
          => NonEmpty (target (TKX2 (Nothing ': sh) r))
          -> target (TKX2 (Nothing ': sh) r)
  xconcat = foldr1 xappend
  xslice :: (KnownSTK r, KnownNat i, KnownNat n, KnownNat k, KnownShX sh)
         => Proxy i -> Proxy n
         -> target (TKX2 (Just (i + n + k) ': sh) r)
         -> target (TKX2 (Just n ': sh) r)
  xuncons :: forall r n sh. (KnownSTK r, KnownNat n, KnownShX sh)
          => target (TKX2 (Just n ': sh) r)
          -> Maybe (target (TKX2 sh r), target (TKX2 (Just (n - 1) ': sh) r))
  xuncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v `xindex` (0 :.% ZIX)
                , xslice @_ @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v `xindex` (0 :.% ZIX)
                , xslice @_ @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  xreverse :: (KnownSTK r, KnownShX sh)
           => target (TKX2 (mn ': sh) r) -> target (TKX2 (mn ': sh) r)
  xtr :: ( KnownSTK r, KnownNat n, KnownNat m, KnownShX sh
         , KnownNat (Rank sh) )
      => target (TKX2 (Just n ': Just m ': sh) r)
      -> target (TKX2 (Just m ': Just n ': sh) r)
  xtr = xtranspose (Permutation.makePerm @'[1, 0])
  xtranspose :: ( PermC perm, KnownSTK r, KnownShX sh
                , Rank perm <= Rank sh  )
             => Permutation.Perm perm -> target (TKX2 sh r)
             -> target (TKX2 (Permutation.PermutePrefix perm sh) r)
  xflatten :: (KnownSTK r, KnownShX sh)
           => target (TKX2 sh r) -> target (TKX2 '[Nothing] r)
  xflatten u = xreshape (Nested.SUnknown (xsize u) :$% ZSX) u
  xreshape :: (KnownSTK r, KnownShX sh, KnownShX sh2)
           => IShX sh2 -> target (TKX2 sh r) -> target (TKX2 sh2 r)
  xzip :: (KnownSTK y, KnownSTK z, KnownShX sh)
       => target (TKProduct (TKX2 sh y) (TKX2 sh z))
       -> target (TKX2 sh (TKProduct y z))
  xunzip :: (KnownSTK y, KnownSTK z, KnownShX sh)
         => target (TKX2 sh (TKProduct y z))
         -> target (TKProduct (TKX2 sh y) (TKX2 sh z))

  xbuild :: forall r m sh.
            (KnownSTK r, KnownShX sh, KnownShX (Take m sh))
         => IShX sh
         -> (IxXOf target (Take m sh) -> target (TKX2 (Drop m sh) r))
         -> target (TKX2 sh r)
  xbuild sh0 f0 =
    let buildSh :: IShX sh1 -> IShX (sh1 ++ Drop m sh)
                -> (IxXOf target sh1 -> target (TKX2 (Drop m sh) r))
                -> target (TKX2 (sh1 ++ Drop m sh) r)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSX, _) -> f ZIX
          (k :$% sh2, _ :$% sh2m) ->
            withKnownShX (ssxFromShape sh2m) $
            let g i = buildSh sh2 sh2m (f . (i :.%))
            in withSNat (fromSMayNat' k) $ \(SNat @n) ->
                 xmcast (ssxFromShape sh1m) $ xbuild1 @_ @n g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (shxTakeSSX (Proxy @(Drop m sh)) sh0
                             (knownShX @(Take m sh))) sh0 f0
  xbuild1 :: (KnownNat k, KnownShX sh, KnownSTK r)
          => (IntOf target -> target (TKX2 sh r))
          -> target (TKX2 (Just k ': sh) r)
  -- xmap and other special cases of build can be defined by the user.

  xprimalPart :: (KnownSTK r, KnownShX sh)
              => target (TKX2 sh r) -> PrimalOf target (TKX2 sh r)
  xprimalPart = tprimalPart knownSTK
  xdualPart :: (KnownSTK r, KnownShX sh)
            => target (TKX2 sh r) -> DualOf target (TKX2 sh r)
  xdualPart = tdualPart knownSTK
  xfromPrimal :: (KnownSTK r, KnownShX sh)
              => PrimalOf target (TKX2 sh r) -> target (TKX2 sh r)
  xfromPrimal = tfromPrimal knownSTK
  xfromDual :: (KnownSTK r, KnownShX sh)
            => DualOf target (TKX2 sh r) -> target (TKX2 sh r)
  xfromDual = tfromDual knownSTK
  xScale :: (GoodScalar r, KnownShX sh, Num (target (TKX sh r)), Num (PrimalOf target (TKX sh r)))
         => PrimalOf target (TKX sh r) -> DualOf target (TKX sh r)
         -> DualOf target (TKX sh r)
  xScale = tScale @target knownSTK

  -- Scalar ops
  kconcrete :: GoodScalar r => r -> target (TKScalar r)
  kconcrete = tconcrete FTKScalar . RepN
  kfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
         => target (TKScalar r) -> target (TKScalar r2)
  kfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                => target (TKScalar r1) -> target (TKScalar r2)
  kcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2)
        => target (TKScalar r1) -> target (TKScalar r2)

  -- Conversions
  kfromR :: GoodScalar r => target (TKR 0 r) -> target (TKScalar r)
  kfromR = kfromS . sfromR
  kfromS :: GoodScalar r => target (TKS '[] r) -> target (TKScalar r)
  default kfromS :: forall r. (LetTensor target, GoodScalar r)
                 => target (TKS '[] r) -> target (TKScalar r)
  kfromS = tfromS
  kfromX :: GoodScalar r => target (TKX '[] r) -> target (TKScalar r)
  kfromX = kfromS . sfromX
  rfromK :: GoodScalar r => target (TKScalar r) -> target (TKR 0 r)
  rfromK = rfromS . sfromK
  rfromS :: (KnownSTK r, KnownShS sh)
         => target (TKS2 sh r) -> target (TKR2 (Rank sh) r)
  default rfromS :: forall r sh. (LetTensor target, KnownSTK r, KnownShS sh)
                 => target (TKS2 sh r) -> target (TKR2 (Rank sh) r)
  rfromS | SNat <- shsRank (knownShS @sh) = tfromS
  rfromX :: (KnownShX sh, KnownSTK r)
         => target (TKX2 sh r) -> target (TKR2 (Rank sh) r)
  rfromX a = case tftk knownSTK a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  sfromK :: GoodScalar r => target (TKScalar r) -> target (TKS '[] r)
  sfromR :: (KnownShS sh, KnownNat (Rank sh), KnownSTK r)
         => target (TKR2 (Rank sh) r) -> target (TKS2 sh r)
  sfromX :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK r)
         => target (TKX2 sh' r) -> target (TKS2 sh r)
  xfromK :: GoodScalar r => target (TKScalar r) -> target (TKX '[] r)
  xfromK = xfromS . sfromK
  xfromR :: (KnownShX sh, KnownNat (Rank sh), KnownSTK r)
         => target (TKR2 (Rank sh) r) -> target (TKX2 sh r)
  xfromR a = case tftk knownSTK a of
    FTKR shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a
  xfromS :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK r)
         => target (TKS2 sh r) -> target (TKX2 sh' r)
  default xfromS :: (LetTensor target, KnownShS sh, KnownShX sh', KnownSTK r)
                 => target (TKS2 sh r) -> target (TKX2 sh' r)
  xfromS = tfromS

  -- Nesting/unnesting
  rnest :: forall n m x.
           (KnownSTK x, KnownNat m)
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
            (KnownSTK x, KnownShS sh2)
         => SNat n -> target (TKX2 (Replicate n Nothing ++ MapJust sh2) x)
         -> target (TKR2 n (TKS2 sh2 x))
  rnestS n@SNat =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate n) $
    rfromX . xnestS (ssxReplicate n)
  rnestX :: forall n sh2 x.
            (KnownSTK x, KnownShX sh2)
         => SNat n -> target (TKX2 (Replicate n Nothing ++ sh2) x)
         -> target (TKR2 n (TKX2 sh2 x))
  rnestX n@SNat =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate n) $
    rfromX . xnest (ssxReplicate n)
  snestR :: forall sh1 m x.
            (KnownSTK x, KnownNat m)
         => ShS sh1 -> target (TKX2 (MapJust sh1 ++ Replicate m Nothing) x)
         -> target (TKS2 sh1 (TKR2 m x))
  snestR sh1 =
    gcastWith (lemRankMapJust sh1) $
    withKnownShS sh1 $
    withKnownShX (ssxFromShape (shCvtSX sh1)) $
    sfromX . xnestR (ssxFromShape (shCvtSX sh1))
  snest :: forall sh1 sh2 x.
           (KnownSTK x, KnownShS sh2)
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
            (KnownSTK x, KnownShX sh2)
         => ShS sh1 -> target (TKX2 (MapJust sh1 ++ sh2) x)
         -> target (TKS2 sh1 (TKX2 sh2 x))
  snestX sh1 =
    gcastWith (lemRankMapJust sh1) $
    withKnownShS sh1 $
    withKnownShX (ssxFromShape (shCvtSX sh1)) $
    sfromX . xnest (ssxFromShape (shCvtSX sh1))
  -- These three are primitives; the others are defined from them.
  xnestR :: forall sh1 m x.
            (KnownSTK x, KnownNat m)
         => StaticShX sh1 -> target (TKX2 (sh1 ++ Replicate m Nothing) x)
         -> target (TKX2 sh1 (TKR2 m x))
  xnestS :: forall sh1 sh2 x.
            (KnownSTK x, KnownShS sh2)
         => StaticShX sh1 -> target (TKX2 (sh1 ++ MapJust sh2) x)
         -> target (TKX2 sh1 (TKS2 sh2 x))
  xnest :: forall sh1 sh2 x.
           (KnownSTK x, KnownShX sh2)
        => StaticShX sh1 -> target (TKX2 (sh1 ++ sh2) x)
        -> target (TKX2 sh1 (TKX2 sh2 x))

  runNest :: forall n m x.
             (KnownSTK x, KnownNat n, KnownNat m)
          => target (TKR2 n (TKR2 m x)) -> target (TKR2 (n + m) x)
  runNest =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)
                                          ++ Replicate m Nothing) :~: n + m) $
    withKnownShX (ssxReplicate (SNat @n)) $
    withKnownShX (ssxReplicate (SNat @n) `ssxAppend` ssxReplicate (SNat @m)) $
    rfromX . xunNestR . xfromR @_ @(Replicate n Nothing)
  runNestS :: forall n sh2 x.
              (KnownSTK x, KnownNat n, KnownShS sh2)
           => target (TKR2 n (TKS2 sh2 x))
           -> target (TKX2 (Replicate n Nothing ++ MapJust sh2) x)
  runNestS =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate (SNat @n)) $
    xunNestS . xfromR @_ @(Replicate n Nothing)
  runNestX :: forall n sh2 x.
              (KnownSTK x, KnownNat n, KnownShX sh2)
           => target (TKR2 n (TKX2 sh2 x))
           -> target (TKX2 (Replicate n Nothing ++ sh2) x)
  runNestX =
    gcastWith (unsafeCoerceRefl :: Rank (Replicate n (Nothing @Nat)) :~: n) $
    withKnownShX (ssxReplicate (SNat @n)) $
    withKnownShX (ssxReplicate (SNat @n) `ssxAppend` knownShX @sh2) $
    xunNest . xfromR @_ @(Replicate n Nothing)
  sunNestR :: forall sh1 m x.
              (KnownSTK x, KnownShS sh1, KnownNat m)
           => target (TKS2 sh1 (TKR2 m x))
           -> target (TKX2 (MapJust sh1 ++ Replicate m Nothing) x)
  sunNestR =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    xunNestR . xfromS @_ @_ @(MapJust sh1)
  sunNest :: forall sh1 sh2 x.
             (KnownSTK x, KnownShS sh1, KnownShS sh2)
          => target (TKS2 sh1 (TKS2 sh2 x)) -> target (TKS2 (sh1 ++ sh2) x)
  sunNest =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    gcastWith (unsafeCoerceRefl
               :: Rank (MapJust sh1 ++ MapJust sh2) :~: Rank (sh1 ++ sh2)) $
    withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))
                  `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2))) $
    sfromX . xunNestS . xfromS @_ @_ @(MapJust sh1)
  sunNestX :: forall sh1 sh2 x.
              (KnownSTK x, KnownShS sh1, KnownShX sh2)
           => target (TKS2 sh1 (TKX2 sh2 x))
           -> target (TKX2 (MapJust sh1 ++ sh2) x)
  sunNestX =
    gcastWith (lemRankMapJust (knownShS @sh1)) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))) $
    withKnownShX (ssxFromShape (shCvtSX (knownShS @sh1))
                  `ssxAppend` knownShX @sh2) $
    xunNest . xfromS @_ @_ @(MapJust sh1)
  -- These three are primitives; the others are defined from them.
  xunNestR :: forall sh1 m x.
              (KnownShX sh1, KnownNat m, KnownSTK x)
           => target (TKX2 sh1 (TKR2 m x))
           -> target (TKX2 (sh1 ++ Replicate m Nothing) x)
  xunNestS :: forall sh1 sh2 x.
              (KnownShX sh1, KnownShS sh2, KnownSTK x)
           => target (TKX2 sh1 (TKS2 sh2 x))
           -> target (TKX2 (sh1 ++ MapJust sh2) x)
  xunNest :: forall sh1 sh2 x.
             (KnownShX sh1, KnownShX sh2, KnownSTK x)
          => target (TKX2 sh1 (TKX2 sh2 x)) -> target (TKX2 (sh1 ++ sh2) x)

  -- General operations that don't require LetTensor nor ShareTensor
  tftk :: STensorKind y -> target y -> FullTensorKind y
  tconcrete :: FullTensorKind y -> RepN y -> target y
  tpair :: (KnownSTK x, KnownSTK z)
         => target x -> target z
         -> target (TKProduct x z)
  tproject1 :: (KnownSTK x, KnownSTK z)
            => target (TKProduct x z)
            -> target x
  tproject2 :: (KnownSTK x, KnownSTK z)
            => target (TKProduct x z)
            -> target z
  tunpairDup :: (KnownSTK x, KnownSTK z)
             => target (TKProduct x z) -> (target x, target z)
  default tunpairDup :: (ShareTensor target, KnownSTK x, KnownSTK z)
                     => target (TKProduct x z) -> (target x, target z)
  tunpairDup = tunpair
  -- | A strict left fold.
  rfold
    :: forall rn rm n m.
       (KnownSTK rn, KnownSTK rm, KnownNat n, KnownNat m)
    => (forall f. ADReady f => f (TKR2 n rn) -> f (TKR2 m rm) -> f (TKR2 n rn))
    -> target (TKR2 n rn)  -- ^ initial value
    -> target (TKR2 (1 + m) rm)  -- ^ iteration is over the outermost dimension
    -> target (TKR2 n rn)
  rfold f acc0 es =
    let shm :: IShR m
        (width, shm, xm) = case tftk knownSTK es of
          FTKR (width2 :$: shm2) x2 -> (width2, shm2, x2)
          FTKR ZSR _ -> error "rfold: impossible pattern needlessly required"
        (sh, x) = case tftk knownSTK acc0 of
          FTKR sh2 x2 -> (sh2, x2)
    in withSNat width $ \snat ->
      tproject1
        (tmapAccumL (Proxy @target)
           snat
           (FTKR @_ sh x)
           (FTKScalar @Z0)
           (FTKR @_ shm xm)
           (let g :: forall f. ADReady f
                  => f (TKR2 n rn) -> f (TKR2 m rm)
                  -> f (TKProduct (TKR2 n rn) TKUnit)
                g !acc !e = tpair (f acc e) tunit
            in g)
           acc0
           es)
  -- | A strict left scan.
  rscan
    :: forall rn rm n m.
       (KnownSTK rn, KnownSTK rm, KnownNat n, KnownNat m)
    => (forall f. ADReady f => f (TKR2 n rn) -> f (TKR2 m rm) -> f (TKR2 n rn))
    -> target (TKR2 n rn)
    -> target (TKR2 (1 + m) rm)
    -> target (TKR2 (1 + n) rn)
  rscan f acc0 es =
    let shm :: IShR m
        (width, shm, xm) = case tftk knownSTK es of
          FTKR (width2 :$: shm2) x2 -> (width2, shm2, x2)
          FTKR ZSR _ -> error "rfold: impossible pattern needlessly required"
        (sh, x) = case tftk knownSTK acc0 of
          FTKR sh2 x2 -> (sh2, x2)
    in withSNat width $ \snat ->
      let bs =
            tproject2
            $ tmapAccumL (Proxy @target)
                snat
                (FTKR @_ sh x)
                (FTKR @_ sh x)
                (FTKR @_ shm xm)
                (let g :: forall f. ADReady f
                       => f (TKR2 n rn) -> f (TKR2 m rm)
                       -> f (TKProduct (TKR2 n rn) (TKR2 n rn))
                     g !acc !e = tlet (f acc e) $ \ !res -> tpair res res
                 in g)
                acc0
                es
      in rappend (rfromList [acc0]) bs
  -- | A strict left fold.
  sfold
    :: forall rn rm sh shm k.
       (KnownSTK rn, KnownSTK rm, KnownShS sh, KnownShS shm, KnownNat k)
    => (forall f. ADReady f
        => f (TKS2 sh rn) -> f (TKS2 shm rm) -> f (TKS2 sh rn))
    -> target (TKS2 sh rn)
    -> target (TKS2 (k ': shm) rm)
    -> target (TKS2 sh rn)
  sfold f acc0 es =
    let xm = case tftk knownSTK es of
          FTKS _ x2 -> x2
        x = case tftk knownSTK acc0 of
          FTKS _ x2 -> x2
    in tproject1
      (tmapAccumL (Proxy @target)
         (SNat @k)
         (FTKS @sh knownShS x)
         (FTKScalar @Z0)
         (FTKS @shm knownShS xm)
         (let g :: forall f. ADReady f
                => f (TKS2 sh rn) -> f (TKS2 shm rm)
                -> f (TKProduct (TKS2 sh rn) TKUnit)
              g !acc !e = tpair (f acc e) tunit
          in g)
         acc0
         es)
  sscan
    :: forall rn rm sh shm k.
       (KnownSTK rn, KnownSTK rm, KnownShS sh, KnownShS shm, KnownNat k)
    => (forall f.
        ADReady f => f (TKS2 sh rn) -> f (TKS2 shm rm) -> f (TKS2 sh rn))
    -> target (TKS2 sh rn)
    -> target (TKS2 (k ': shm) rm)
    -> target (TKS2 (1 + k ': sh) rn)
  sscan f acc0 es =
    let xm = case tftk knownSTK es of
          FTKS _ x2 -> x2
        x = case tftk knownSTK acc0 of
          FTKS _ x2 -> x2
        bs =
          tproject2
          $ tmapAccumL (Proxy @target)
             (SNat @k)
             (FTKS @sh knownShS x)
             (FTKS @sh knownShS x)
             (FTKS @shm knownShS xm)
             (let g :: forall f. ADReady f
                    => f (TKS2 sh rn) -> f (TKS2 shm rm)
                    -> f (TKProduct (TKS2 sh rn) (TKS2 sh rn))
                  g !acc !e = tlet (f acc e) $ \ !res -> tpair res res
              in g)
             acc0
             es
    in sappend (sfromList [acc0]) bs
  -- | A strict right mapAccum.
  --
  -- The applications of 'tfwd' and 'trevDt' performed already at this point
  -- ensure that the computation of a derivative is not repeated
  -- and that its result is shared. However, most of the time
  -- the computation is unnneeded, so the AST instance uses a non-strict
  -- constructor 'AstLambda' for it's instance of 'HFunOf'.
  --
  -- If the same argument functions are passed to many dmapAccum calls, as in
  -- > let f = ... in ... (tmapAccumR ... f ...) ... (tmapAccumL ... f ...)
  -- extra care is needed to prevent double derivative computation.
  -- One needs to use tmapAccumRDer manually as in (simplified)
  -- > let f = ...; df = tfwd f; rf = trev f
  -- > in ... (tmapAccumRDer f df rf ...) ... (tmapAccumLDer f df rf ...)
  tmapAccumR
    :: forall k accShs bShs eShs.
       (KnownSTK accShs, KnownSTK bShs, KnownSTK eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> (forall f. ADReady f
        => f accShs -> f eShs
        -> f (TKProduct accShs bShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  tmapAccumR proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => f (TKProduct accShs eShs)
           -> f (TKProduct accShs bShs)
        fl !args = tlet args $ \ !args1 ->
                     f (tproject1 args1) (tproject2 args1)
    in tmapAccumRDer proxy k accShs bShs eShs
                     (tlambda @target shs (HFun fl))
                     (tfwd @target shs $ HFun fl)
                     (trevDt @target shs $ HFun fl)
                     acc0 es
  tmapAccumRDer
    :: (KnownSTK accShs, KnownSTK bShs, KnownSTK eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs  -- ^ shapes of acc, the accumulator
    -> FullTensorKind bShs -- ^ shapes of b
    -> FullTensorKind eShs -- ^ shapes of e
    -> HFunOf target (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> target accShs  -- ^ acc0 :: accShs
    -> target (BuildTensorKind k eShs)
         -- ^ es :: k ': eShs
    -> target (TKProduct accShs (BuildTensorKind k bShs))
         -- ^ (x, bs) :: (accShs, k ': bShs)
  -- | A strict left mapAccum.
  tmapAccumL
    :: forall k accShs bShs eShs.
       (KnownSTK accShs, KnownSTK bShs, KnownSTK eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> (forall f. ADReady f
        => f accShs -> f eShs
        -> f (TKProduct accShs bShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  tmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => f (TKProduct accShs eShs)
           -> f (TKProduct accShs bShs)
        fl !args = tlet args $ \ !args1 ->
                     f (tproject1 args1) (tproject2 args1)
    in tmapAccumLDer proxy k accShs bShs eShs
                     (tlambda @target shs (HFun fl))
                     (tfwd @target shs $ HFun fl)
                     (trevDt @target shs $ HFun fl)
                     acc0 es
  tmapAccumLDer
    :: (KnownSTK accShs, KnownSTK bShs, KnownSTK eShs)
    => Proxy target
    -> SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> HFunOf target (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf target (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  tApply :: (KnownSTK x, KnownSTK z)
         => HFunOf target x z -> target x
         -> target z
  tlambda :: (KnownSTK x, KnownSTK z)
          => FullTensorKind x -> HFun x z -> HFunOf target x z
  tcond :: Boolean (BoolOf target)
        => STensorKind y
        -> BoolOf target -> target y -> target y -> target y
  ifF :: (Boolean (BoolOf target), KnownSTK y)
      => BoolOf target -> target y -> target y -> target y
  ifF = tcond knownSTK
  minF :: (Boolean (BoolOf target), OrdF target, KnownSTK y)
       => target y -> target y -> target y
  minF u v = ifF (u <=. v) u v
  maxF :: (Boolean (BoolOf target), OrdF target, KnownSTK y)
       => target y -> target y -> target y
  maxF u v = ifF (u >=. v) u v
  tbuild1 :: forall y k. KnownSTK y
               -- y comes first, because k easy to set via SNat
          => SNat k -> (IntOf target -> target y)
          -> target (BuildTensorKind k y)
  tbuild1 snat@SNat f =
    let replSTK :: STensorKind z -> (IntOf target -> target z)
                -> target (BuildTensorKind k z)
        replSTK stk g = case stk of
          STKScalar{} -> sbuild1 (sfromK . g)
          STKR SNat x | Dict <- lemKnownSTK x ->
            rbuild1 (sNatValue snat) g
          STKS sh x | Dict <- lemKnownSTK x ->
            withKnownShS sh $ sbuild1 g
          STKX sh x | Dict <- lemKnownSTK x ->
            withKnownShX sh $ xbuild1 g
          STKProduct @z1 @z2 stk1 stk2
            | Dict <- lemKnownSTK stk1
            , Dict <- lemKnownSTK stk2
            , Dict <- lemKnownSTKOfBuild snat stk1
            , Dict <- lemKnownSTKOfBuild snat stk2 ->
              let f1 i = tproject1 @_ @z1 @z2 $ g i
                  f2 i = tproject2 @_ @z1 @z2 $ g i
                    -- TODO: looks expensive, but hard to do better,
                    -- so let's hope g is full of variables
              in tpair (replSTK stk1 f1) (replSTK stk2 f2)
    in replSTK (knownSTK @y) f

  tprimalPart :: STensorKind y
              -> target y
              -> PrimalOf target y
  tdualPart :: STensorKind y
            -> target y
            -> DualOf target y
  tfromPrimal :: STensorKind y
              -> PrimalOf target y
              -> target y
  tfromDual :: STensorKind y
            -> DualOf target y
            -> target y
  tScale :: (Num (target y), Num (PrimalOf target y))
         => STensorKind y
         -> PrimalOf target y -> DualOf target y
         -> DualOf target y
  tScale stk s t =
    tdualPart stk $ tfromPrimal @target stk s * tfromDual stk t

  -- If the result of the argument function is not a scalar,
  -- the result of this operation is the gradient of a function that additionally
  -- sums all elements of the result. If all elements are equally important
  -- for optimization, this may be exactly what is needed for gradient descent.
  --
  -- The second argument is only used to determine tensor shapes
  -- and the third has to have the same shapes as the second.
  --
  -- The function argument needs to be quantified,
  -- because otherwise in the ADVal instance one could put an illegal
  -- InputR there, confusing the two levels of contangents.
  --
  -- These methods are in this class, because their implementations
  -- use the let operations and also their signatures mention @ADReady@,
  -- so it's awkward to put the methods into @BaseTensor@,
  -- which shouldn't know about lets, etc.
  rrev :: forall x r n.
          (KnownSTK x, KnownSTK r, KnownNat n)
       => (forall f. ADReady f => f x -> f (TKR2 n r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind x)
  rrev f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x) =
    \ !es -> tApply (trev @target ftk $ HFun f) es
  -- We can't get sh from anywhere, so this is not possible:
  -- rrev f shs es = rrevDt f shs es (rreplicate0N sh 1)
  rrevDt :: forall x r n.
            (KnownSTK x, KnownSTK r, KnownNat n)
         => (forall f. ADReady f => f x -> f (TKR2 n r))
         -> FullTensorKind x
         -> target x
         -> target (ADTensorKind (TKR2 n r))  -- ^ incoming cotangent (dt)
         -> target (ADTensorKind x)
  rrevDt f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x)
               , Dict <- lemKnownSTKOfAD (knownSTK @(TKR2 n r)) =
    \ !es !dt -> tApply (trevDt @target ftk $ HFun f)
                        (tpair dt es)
  rfwd :: forall x r n.
          (KnownSTK x, KnownSTK r, KnownNat n)
       => (forall f. ADReady f => f x -> f (TKR2 n r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> target (ADTensorKind (TKR2 n r))
  rfwd f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x)
             , Dict <- lemKnownSTKOfAD (knownSTK @(TKR2 n r)) =
    \ !es !ds -> tApply (tfwd @target ftk $ HFun f)
                        (tpair ds es)
  srev :: forall x r sh.
          ( KnownSTK x, KnownSTK r, KnownShS sh
          , ADTensorKind (TKS2 sh r) ~ TKS2 sh r )
       => (forall f. ADReady f => f x -> f (TKS2 sh r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind x)
  srev f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x) =
    \ !es -> tApply (trev @target ftk $ HFun f) es
  srevDt :: forall x r sh.
            (KnownSTK x, KnownSTK r, KnownShS sh)
         => (forall f. ADReady f => f x -> f (TKS2 sh r))
         -> FullTensorKind x
         -> target x
         -> target (ADTensorKind (TKS2 sh r))  -- ^ incoming cotangent (dt)
         -> target (ADTensorKind x)
  srevDt f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x)
               , Dict <- lemKnownSTKOfAD (knownSTK @(TKS2 sh r)) =
    \ !es !dt -> tApply (trevDt @target ftk $ HFun f)
                        (tpair dt es)
  sfwd :: forall x r sh.
          (KnownSTK x, KnownSTK r, KnownShS sh)
       => (forall f. ADReady f => f x -> f (TKS2 sh r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> target (ADTensorKind (TKS2 sh r))
  sfwd f ftk | Dict <- lemKnownSTKOfAD (knownSTK @x)
             , Dict <- lemKnownSTKOfAD (knownSTK @(TKS2 sh r)) =
    \ !es !ds -> tApply (tfwd @target ftk $ HFun f)
                        (tpair ds es)
  -- If the result of the argument function is not a scalar,
  -- the result of this operation is the gradient of a function that additionally
  -- sums all elements of the result. If all elements are equally important
  -- for optimization, this may be exactly what is needed for gradient descent,
  -- unless there are floats of different resolution among the elements and,
  -- e.g., one wants to compensate for that.
  --
  -- These methods (and tlambda) are exactly what is needed as arguments
  -- of tmapAccumRDer.
  trev
    :: (KnownSTK x, KnownSTK z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target x (ADTensorKind x)  -- a |-> da
  trevDt
    :: (KnownSTK x, KnownSTK z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind z) x) (ADTensorKind x)
                 -- [db, a] |-> da
  tfwd
    :: (KnownSTK x, KnownSTK z)
    => FullTensorKind x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind x) x) (ADTensorKind z)
                 -- [da, a] |-> db

tunit :: BaseTensor target
      => target TKUnit
tunit = kconcrete Z0

rscalar :: forall r target. (KnownSTK r, BaseTensor target)
        => RepORArray r -> target (TKR2 0 r)
rscalar r | Dict <- eltDictRep (knownSTK @r) =
  let a = Nested.rscalar r
  in tconcrete (tftkG (STKR (SNat @0) (knownSTK @r)) a) (RepN a)

rrepl :: (GoodScalar r, KnownNat n, BaseTensor target)
      => IShR n -> r -> target (TKR n r)
rrepl sh = rconcrete . Nested.rreplicateScal sh

ringestData :: (GoodScalar r, KnownNat n, BaseTensor target)
            => IShR n -> [r] -> target (TKR n r)
ringestData sh l = rconcrete $ Nested.rfromListPrimLinear sh l

sscalar :: forall r target. (KnownSTK r, BaseTensor target)
        => RepORArray r -> target (TKS2 '[] r)
sscalar r | Dict <- eltDictRep (knownSTK @r) =
  let a = Nested.sscalar r
  in tconcrete (tftkG (STKS ZSS (knownSTK @r)) a) (RepN a)

srepl :: (KnownShS sh, GoodScalar r, BaseTensor target)
      => r -> target (TKS sh r)
srepl = sconcrete . Nested.sreplicateScal knownShS
  -- TODO: the following simplifies better, because the replication is not
  -- hidden at low level:
  -- Dict <- lemKnownNatSize (knownShS @sh) =
  --   sreplicate0N . sscalar
  -- though we could also look at the low level in @isSmall@ and mark
  -- replicated fromPrimals as small

singestData :: (GoodScalar r, KnownShS sh, BaseTensor target)
            => [r] -> target (TKS sh r)
singestData l = sconcrete $ Nested.sfromListPrimLinear knownShS l

xscalar :: forall r target. (KnownSTK r, BaseTensor target)
        => RepORArray r -> target (TKX2 '[] r)
xscalar r | Dict <- eltDictRep (knownSTK @r) =
  let a = Nested.mscalar r
  in tconcrete (tftkG (STKX ZKX (knownSTK @r)) a) (RepN a)

xrepl :: (KnownShX sh, GoodScalar r, BaseTensor target)
      => IShX sh -> r -> target (TKX sh r)
xrepl sh = xconcrete . Nested.mreplicateScal sh

xingestData :: (GoodScalar r, KnownShX sh, BaseTensor target)
            => IShX sh -> [r] -> target (TKX sh r)
xingestData sh l = xconcrete $ Nested.mfromListPrimLinear sh l

-- These are user-accessible, so the constraint is `ADReady`, which means
-- lets, but no shares.
type role HFun nominal nominal
newtype HFun (x :: TensorKindType) (z :: TensorKindType) =
  HFun {unHFun :: forall f. ADReady f
               => f x -> f z}

instance Show (HFun x y) where
  show _ = "<lambda>"


-- * The mega-constraint

type ADReady target =
  ( ADReadyNoLet target
  , LetTensor target
-- The following can't be added, because we have instances like ADVal (AstRaw),
-- so AstRaw would need to have a LetTensor instance:
--  , LetTensor (PrimalOf target)
  )

type ADReadyNoLet target =
  ( ADReadyEqsClasses target
  , ADReadyEqsClasses (ShareOf target)
  , ShareTensor (ShareOf target)
  , ShareTensor (PrimalOf (ShareOf target))
  , ShareOf (ShareOf target) ~ ShareOf target
  )

type ADReadyEqsClasses target =
  ( ADReadyEqs target
  , ADReadyClasses target
  , ADReadyClasses (PrimalOf target)
  )

type ADReadyEqs target =
  ( BoolOf (PrimalOf target) ~ BoolOf target
  )

type ADReadyClasses target =
  ( Boolean (BoolOf target)
  , EqF target
  , OrdF target
  , BaseTensor target
  , AllTargetShow target
  )

-- This is illegal:
-- type AllTargetShow target = forall y. KnownSTK y => Show (target y)

type AllTargetShow :: Target -> Constraint
class (forall y. KnownSTK y => Show (target y))
      => AllTargetShow target where
instance
      (forall y. KnownSTK y => Show (target y))
      => AllTargetShow target where
