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
  ( -- * The tensor classes and derived operations
    LetTensor(..), ShareTensor(..), BaseTensor(..), ConvertTensor(..)
  , HFun(..)
  , tunit, tlet
  , rconcrete, rscalar, rrepl, ringestData
  , sconcrete, sscalar, srepl, singestData
  , xconcrete, xscalar, xrepl, xingestData
  , kconcrete
  , rfromList, rfromVector, rfromListLinear, rfromVectorLinear, runravelToList
  , sfromList, sfromVector, sfromListLinear, sfromVectorLinear, sunravelToList
  , xfromList, xfromVector, xfromListLinear, xfromVectorLinear, xunravelToList
  , rsum, rsum0, rdot0, rdot1In, rmatvecmul, rmatmul2, rreplicate, rreplicate0N
  , ssum, ssum0, sdot0, sdot1In, smatvecmul, smatmul2, sreplicate, sreplicate0N
  , xsum, xsum0, xdot0, xdot1In, xmatvecmul, xmatmul2, xreplicate, xreplicate0N
  , rindex, (!), rindex0, roneHot, rscatter, rscatter1, rgather, rgather1
  , sindex, (!$), sindex0, soneHot, sscatter, sscatter1, sgather, sgather1
  , xindex, xindex0, xoneHot, xscatter, xscatter1, xgather, xgather1
  , rfloor, rfromIntegral, rcast, rminIndex, rmaxIndex, riota
  , sfloor, sfromIntegral, scast, sminIndex, smaxIndex, siota
  , xfloor, xfromIntegral, xcast, xminIndex, xmaxIndex, xiota
  , kfloor, kfromIntegral, kcast
  , rappend, rconcat, rslice, runcons, rreverse
  , rtr, rtranspose, rflatten, rreshape
  , sappend, sslice, suncons, sreverse
  , str, stranspose, sflatten, sreshape
  , xappend, xappend0, xconcat, xslice, xuncons, xreverse
  , xtr, xtranspose, xflatten, xreshape
  , rbuild, rbuild1, rmap, rmap1, rmap0N, rzipWith, rzipWith1, rzipWith0N
  , rzipWith3, rzipWith31, rzipWith30N, rzipWith4, rzipWith41, rzipWith40N
  , sbuild, sbuild1, smap, smap1, smap0N, szipWith, szipWith1, szipWith0N
  , szipWith3, szipWith31, szipWith30N, szipWith4, szipWith41, szipWith40N
  , xbuild, xbuild1
  , rfold, rscan, sfold, sscan, xfold, xscan, tmapAccumR, tmapAccumL
  , rrev, rrevDt, rfwd, srev, srevDt, sfwd
  , rprimalPart, rdualPart, rfromPrimal, rfromDual, rScale
  , sprimalPart, sdualPart, sfromPrimal, sfromDual, sScale
  , xprimalPart, xdualPart, xfromPrimal, xfromDual, xScale
    -- * The giga-constraint
  , ADReady, ADReadyNoLet, AllTargetShow, CommonTargetEqOrd
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.Int (Int64)
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.Exts (IsList (..))
import GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , cmpNat
  , type (+)
  , type (-)
  , type (<=)
  , type (<=?)
  )
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (typeRep)

import Data.Array.Mixed.Lemmas
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  ( IShX
  , fromSMayNat'
  , shxAppend
  , shxDropSSX
  , shxLength
  , shxSize
  , shxTakeSSX
  , ssxAppend
  , ssxFromShape
  , ssxReplicate
  , withKnownShX
  )
import Data.Array.Mixed.Types (Init, unsafeCoerceRefl)
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
  forall r n. GoodScalar r
              => c1 r => c2 (f (TKR n r))

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsS c1 c2 f =
  forall r sh. GoodScalar r
               => c1 r => c2 (f (TKS sh r))

type TensorSupportsX :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsX c1 c2 f =
  forall r sh. GoodScalar r
               => c1 r => c2 (f (TKX sh r))

class (RealFloatF r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloatF r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class LetTensor (target :: Target) where
  ttlet :: target x -> (target x -> target z) -> target z
  toShare :: target y -> ShareOf target y
  tunshare :: ShareOf target y -> target y
  tunshare = error "tunshare: this instance should never be used"
  tappend :: forall y m n. BaseTensor target
          => SNat m -> SNat n -> STensorKind y
          -> target (BuildTensorKind m y) -> target (BuildTensorKind n y)
          -> target (BuildTensorKind (m + n) y)
  tappend msnat@SNat nsnat@SNat stk a b = case stk of
    STKScalar -> sappend a b
    STKR _ x | Dict <- lemKnownSTK x -> rappend a b
    STKS _ x | Dict <- lemKnownSTK x -> sappend a b
    STKX _ x | Dict <- lemKnownSTK x -> xappend a b
    STKProduct stk1 stk2 ->
      ttlet a $ \ !aShared -> ttlet b $ \ !bShared ->
        tpair (tappend msnat nsnat stk1 (tproject1 aShared) (tproject1 bShared))
              (tappend msnat nsnat stk2 (tproject2 aShared) (tproject2 bShared))
  tD :: BaseTensor target
     => STensorKind y -> PrimalOf target y -> DualOf target y
     -> target y
  tD stk p d =
    -- Lets needed, because taddTarget requires duplicable arguments.
    ttlet (tfromPrimal stk p) $ \pShared ->
    ttlet (tfromDual d) $ \dShared ->
      taddTarget stk pShared dShared
  -- | A strict left fold.
  tfold
    :: forall yn ym k. BaseTensor target
    => SNat k -> STensorKind yn -> STensorKind ym
    -> (forall f. ADReady f => f yn -> f ym -> f yn)
    -> target yn  -- ^ initial value
    -> target (BuildTensorKind k ym)
         -- ^ iteration is over the outermost dimension of this tensor
    -> target yn
  {-# INLINE tfold #-}  -- this doesn't want to specialize
  tfold k nstk mstk f acc0 es =
    tproject1
    $ tmapAccumL (Proxy @target)
       k
       (tftk nstk acc0)
       (FTKScalar @Z0)
       (razeFTK k mstk (tftk (buildSTK k mstk) es))
       (let g :: forall f. ADReady f
              => f yn -> f ym -> f (TKProduct yn TKUnit)
            g !acc !e = tpair (f acc e) tunit
        in g)
       acc0
       es
  -- | A strict left scan.
  tscan
    :: forall yn ym k. BaseTensor target
    => SNat k -> STensorKind yn -> STensorKind ym
    -> (forall f. ADReady f => f yn -> f ym -> f yn)
    -> target yn
    -> target (BuildTensorKind k ym)
    -> target (BuildTensorKind (1 + k) yn)
  {-# INLINE tscan #-}  -- this doesn't want to specialize
  tscan k nstk mstk f acc0 es =
    let bs :: target (BuildTensorKind k yn)
        bs = tproject2
             $ tmapAccumL (Proxy @target)
                k
                (tftk nstk acc0)
                (tftk nstk acc0)
                (razeFTK k mstk (tftk (buildSTK k mstk) es))
              (let g :: forall f. ADReady f
                     => f yn -> f ym -> f (TKProduct yn yn)
                   g !acc !e = ttlet (f acc e) $ \ !res -> tpair res res
               in g)
              acc0
              es
    in tappend (SNat @1) k nstk
               (tfromVector (SNat @1) nstk (V.fromList [acc0])) bs

class ShareTensor (target :: Target) where
  tshare :: target y -> target y
  tunpair :: target (TKProduct x z) -> (target x, target z)
  -- This would suffers from lack of sharing with LetTensor, because
  -- ttlet doesn't work over a list. With sharing it's fine.
  tunravelToListShare :: forall y k. (BaseTensor target, ConvertTensor target)
                      => SNat k -> STensorKind y
                      -> target (BuildTensorKind k y)
                      -> [target y]
  tunravelToListShare snat@SNat stk u = case stk of
    STKScalar -> map kfromS $ sunravelToList u
    STKR SNat x | Dict <- lemKnownSTK x ->
      runravelToList u
    STKS sh x | Dict <- lemKnownSTK x ->
      withKnownShS sh $ sunravelToList u
    STKX sh x | Dict <- lemKnownSTK x ->
      withKnownShX sh $ xunravelToList u
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in zipWith tpair (tunravelToListShare snat stk1 u1)
                       (tunravelToListShare snat stk2 u2)

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

  -- First type argument being @target@ is acceptable here, since these
  -- operations are mostly used when the shape is not known at the type level.
  rshape :: forall n x. KnownSTK x
         => target (TKR2 n x) -> IShR n
  rlength :: forall n x. KnownSTK x
          => target (TKR2 n x) -> Int
  rsize :: forall n x. KnownSTK x
        => target (TKR2 n x) -> Int
  rsize = shrSize . rshape
  rwidth :: forall n x. KnownSTK x
          => target (TKR2 (1 + n) x) -> Int
  rwidth a = case rshape a of
    k :$: _ -> k

  sshape :: forall sh x. KnownSTK x
         => target (TKS2 sh x) -> ShS sh
  slength :: forall sh x. KnownSTK x
          => target (TKS2 sh x) -> Int
  ssize :: forall sh x. KnownSTK x
        => target (TKS2 sh x) -> Int
  ssize = shsSize . sshape
  swidth :: forall sh n x. KnownSTK x
          => target (TKS2 (n ': sh) x) -> Int
  swidth a = case sshape a of
    n :$$ _ -> sNatValue n

  xshape :: forall sh x. KnownSTK x
         => target (TKX2 sh x) -> IShX sh
  xlength :: forall sh x. KnownSTK x
          => target (TKX2 sh x) -> Int
  xsize :: forall sh x. KnownSTK x
        => target (TKX2 sh x) -> Int
  xsize = shxSize . xshape
  xwidth :: forall sh mn x. KnownSTK x
          => target (TKX2 (mn ': sh) x) -> Int
  xwidth a = case xshape a of
    mn :$% _ -> fromSMayNat' mn

  trconcrete :: GoodScalar r
             => Nested.Ranked n r -> target (TKR n r)
  tsconcrete :: GoodScalar r
             => Nested.Shaped sh r -> target (TKS sh r)
  txconcrete :: GoodScalar r
             => Nested.Mixed sh r -> target (TKX sh r)
  tkconcrete :: GoodScalar r => r -> target (TKScalar r)
  tconcrete :: FullTensorKind y -> RepN y -> target y

  -- These nine methods can't be replaced by tfromVector, because the concrete
  -- instance has much faster implementations.
  --
  -- This is morally non-empty strict vectors:
  trfromVector :: (KnownNat n, KnownSTK x)
               => Data.Vector.Vector (target (TKR2 n x))
               -> target (TKR2 (1 + n) x)
  trfromVector v = withSNat (V.length v) $ \k ->
    tfromVector k (STKR SNat knownSTK) v
  trfromVectorLinear :: forall n x. KnownSTK x
                     => IShR n -> Data.Vector.Vector (target (TKR2 0 x))
                     -> target (TKR2 n x)
  trfromVectorLinear sh v | Dict <- eltDictRep (knownSTK @x) =
    if V.null v
    then let arr = Nested.remptyArray
         in rreshape sh $ tconcrete (tftkG knownSTK arr) (RepN arr)
    else rreshape sh $ trfromVector v
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'ttlet'.
  trunravelToList :: forall n x. (KnownSTK x, KnownNat n)
                  => target (TKR2 (1 + n) x) -> [target (TKR2 n x)]
  trunravelToList t =
    let f :: Int -> target (TKR2 n x)
        f i = rindex t (fromIntegral i :.: ZIR)
    in map f [0 .. rwidth t - 1]

  tsfromVector :: (KnownNat n, KnownShS sh, KnownSTK x)
               => Data.Vector.Vector (target (TKS2 sh x))
               -> target (TKS2 (n ': sh) x)
  tsfromVector v = tfromVector SNat (STKS knownShS knownSTK) v
  tsfromVectorLinear :: forall sh x. (KnownSTK x, KnownShS sh)
                     => Data.Vector.Vector (target (TKS2 '[] x))
                     -> target (TKS2 sh x)
  tsfromVectorLinear v | Dict <- eltDictRep (knownSTK @x)
                       , SNat <- shsProduct (knownShS @sh) =
    if V.null v
    then gcastWith (unsafeCoerceRefl :: Nested.Product sh :~: 0) $
         let arr = Nested.semptyArray ZSS
         in tsreshape knownShS $ tconcrete (tftkG knownSTK arr) (RepN arr)
    else tsreshape (knownShS @sh) $ tsfromVector v
  tsunravelToList :: forall n sh x. (KnownSTK x, KnownNat n, KnownShS sh)
                  => target (TKS2 (n ': sh) x) -> [target (TKS2 sh x)]
  tsunravelToList t =
    let f :: Int -> target (TKS2 sh x)
        f i = sindex t (fromIntegral i :.$ ZIS)
    in map f [0 .. swidth t - 1]

  txfromVector :: (KnownNat n, KnownShX sh, KnownSTK x)
               => Data.Vector.Vector (target (TKX2 sh x))
               -> target (TKX2 (Just n ': sh) x)
  txfromVector v = tfromVector SNat (STKX knownShX knownSTK) v
  txfromVectorLinear :: forall sh x. KnownSTK x
                     => IShX sh -> Data.Vector.Vector (target (TKX2 '[] x))
                     -> target (TKX2 sh x)
  txfromVectorLinear sh v | Dict <- eltDictRep (knownSTK @x) =
    if V.null v
    then let arr = Nested.memptyArray ZSX
         in xreshape sh $ tconcrete (tftkG knownSTK arr) (RepN arr)
    else withSNat (shxSize sh) $ \(SNat @n) ->
           txreshape @_ @'[Just n] sh $ txfromVector v
  txunravelToList :: forall n sh x. (KnownSTK x, KnownNat n, KnownShX sh)
                  => target (TKX2 (Just n ': sh) x) -> [target (TKX2 sh x)]
  txunravelToList t =
    let f :: Int -> target (TKX2 sh x)
        f i = xindex t (fromIntegral i :.% ZIX)
    in map f [0 .. xwidth t - 1]

  tfromVector
    :: forall y k.
       SNat k -> STensorKind y -> Data.Vector.Vector (target y)
    -> target (BuildTensorKind k y)
  tfromListR :: STensorKind y -> ListR k (target y)
             -> target (BuildTensorKind k y)
  tfromListR stk l =
    tfromVector (listrRank l) stk . V.fromList . Foldable.toList $ l

  -- A number suffix in the name may indicate the rank of the codomain,
  -- if bounded. Suffix 1 may also mean the operations builds up codomain
  -- by 1 dimension.
  trsum :: (KnownNat n, KnownSTK x)
        => target (TKR2 (1 + n) x) -> target (TKR2 n x)
  -- This op (and it's Delta constructor) is worthwhile, because flattening
  -- is O(n) sometimes, unlike transpose, etc.
  trsum0 :: (KnownNat n, KnownSTK x)
         => target (TKR2 n x) -> target (TKR2 0 x)
  trsum0 = rsum . rflatten
  trdot0 :: (KnownNat n, GoodScalar r)
         => target (TKR n r) -> target (TKR n r) -> target (TKR 0 r)
  trdot0 t u = rsum (rflatten (t * u))
  trdot1In :: GoodScalar r
           => target (TKR 2 r) -> target (TKR 2 r)
           -> target (TKR 1 r)  -- TODO: generalize
  trdot1In t u = rsum $ rtr (t * u)
  trmatvecmul :: GoodScalar r
              => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  trmatvecmul m v = rbuild1 (rwidth m) (\i -> rdot0 v (m ! [i]))
  trmatmul2 :: (GoodScalar r, Numeric r)
            => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
  trmatmul2 m1 m2 = rbuild1 (rwidth m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  trreplicate :: (KnownNat n, KnownSTK x)
              => Int -> target (TKR2 n x) -> target (TKR2 (1 + n) x)
  trreplicate0N :: (KnownNat n, KnownSTK x)
                => IShR n -> target (TKR2 0 x) -> target (TKR2 n x)
  trreplicate0N sh = rreshape sh . trreplicate (shrSize sh)

  tssum :: (KnownNat n, KnownShS sh, KnownSTK x)
        => target (TKS2 (n ': sh) x) -> target (TKS2 sh x)
  tssum0 :: forall sh x. (KnownSTK x, KnownShS sh)
         => target (TKS2 sh x) -> target (TKS2 '[] x)
  tssum0 | SNat <- shsProduct (knownShS @sh) = ssum . sflatten
  tsdot0 :: forall sh r. (GoodScalar r, KnownShS sh)
         => target (TKS sh r) -> target (TKS sh r) -> target (TKS '[] r)
  tsdot0 t u | SNat <- shsProduct (knownShS @sh) = ssum (sflatten (t * u))
  tsdot1In :: (KnownNat n, KnownNat m, GoodScalar r)
           => SNat n
           -> target (TKS '[m, n] r) -> target (TKS '[m, n] r)
           -> target (TKS '[m] r)  -- TODO: generalize
  tsdot1In _ t u = ssum $ str (t * u)
  tsmatvecmul :: forall m n r. (GoodScalar r, KnownNat m, KnownNat n)
              => target (TKS '[m, n] r) -> target (TKS '[n] r)
              -> target (TKS '[m] r)
  tsmatvecmul m v = tsbuild1 @_ @m (\i -> sdot0 v (m `sindex` (i :.$ ZIS)))
  tsmatmul2 :: forall n m p r.
               (KnownNat n, KnownNat m, KnownNat p, GoodScalar r, Numeric r)
            => target (TKS '[m, n] r) -> target (TKS '[n, p] r)
            -> target (TKS '[m, p] r)
  tsmatmul2 m1 m2 =
    tsbuild1 @_ @m (\i -> smatvecmul (str m2) (m1 `sindex` (i :.$ ZIS)))
  tsreplicate :: forall k sh x. (KnownNat k, KnownSTK x)
              => ShS sh -> target (TKS2 sh x) -> target (TKS2 (k ': sh) x)
  tsreplicate0N :: forall sh x. KnownSTK x
                => ShS sh -> target (TKS2 '[] x)
                -> target (TKS2 sh x)
  tsreplicate0N sh | SNat <- shsProduct sh =
    tsreshape sh . tsreplicate @target @(Nested.Product sh) ZSS

  -- The choice in BuildTensorKind makes it hard to support this one,
  -- due to DeltaSum and AstSum being typed with BuildTensorKind:
  -- xsum :: (KnownShX sh, KnownShX (mn ': sh), KnownSTK x)
  --     => target (TKX2 (mn ': sh) x) -> target (TKX2 sh x)
  txsum :: (KnownNat n, KnownShX sh, KnownSTK x)
        => target (TKX2 (Just n ': sh) x) -> target (TKX2 sh x)
  txsum0 :: (KnownShX sh, KnownSTK x, ConvertTensor target)
         => target (TKX2 sh x) -> target (TKX2 '[] x)
  txsum0 t = withSNat (shxSize $ xshape t) $ \snat ->
    xsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten t)
  txdot0 :: (KnownShX sh, GoodScalar r, ConvertTensor target)
         => target (TKX sh r) -> target (TKX sh r) -> target (TKX '[] r)
  txdot0 t u = withSNat (shxSize $ xshape t) $ \snat ->
    xsum (xmcast (Nested.SKnown snat :!% ZKX) $ xflatten (t * u))
  txdot1In :: (KnownNat n, KnownNat m, GoodScalar r)
           => target (TKX '[Just m, Just n] r)
           -> target (TKX '[Just m, Just n] r)
           -> target (TKX '[Just m] r)  -- TODO: generalize
  txdot1In t u = xsum $ xtr (t * u)
  txmatvecmul :: forall mm mn r. (GoodScalar r, ConvertTensor target)
              => Nested.SMayNat Int SNat mm -> Nested.SMayNat Int SNat mn
              -> target (TKX '[mm, mn] r) -> target (TKX '[mn] r)
              -> target (TKX '[mm] r)
  txmatvecmul mm mn m v =
    withKnownShX (ssxFromShape $ mm :$% ZSX) $
    withKnownShX (ssxFromShape $ mn :$% ZSX) $
    withSNat (fromSMayNat' mm) $ \(SNat @k) ->
      xmcast (ssxFromShape $ mm :$% ZSX)
      $ txbuild1 @_ @k (\i -> xdot0 v (m `xindex` (i :.% ZIX)))
  txmatmul2 :: forall n m p r.
               ( GoodScalar r, ConvertTensor target
               , Numeric r, KnownNat n, KnownNat m, KnownNat p )
            => target (TKX '[Just m, Just n] r)
            -> target (TKX '[Just n, Just p] r)
            -> target (TKX '[Just m, Just p] r)
  txmatmul2 m1 m2 =
    txbuild1 @_ @m (\i ->
      xmatvecmul (Nested.SKnown (SNat @p)) (Nested.SKnown (SNat @n))
                 (xtr m2) (m1 `xindex` (i :.% ZIX)))
  txreplicate :: (KnownNat k, KnownShX sh, KnownSTK x)
              => target (TKX2 sh x) -> target (TKX2 (Just k ': sh) x)
  txreplicate0N :: (KnownShX sh, KnownSTK x)
                => IShX sh -> target (TKX2 '[] x) -> target (TKX2 sh x)
  txreplicate0N sh = withSNat (shxSize sh) $ \ (SNat @k) ->
    xreshape sh . txreplicate @_ @k

  -- First index is for outermost dimension; empty index means identity,
  -- if index is out of bounds, the result is defined and is 0,
  -- but vectorization is permitted to change the value.
  trindex :: (KnownNat m, KnownNat n, KnownSTK x)
          => target (TKR2 (m + n) x) -> IxROf target m -> target (TKR2 n x)
  trindex0 :: (KnownNat m, KnownSTK x)
           => target (TKR2 m x) -> IxROf target m -> target (TKR2 0 x)
  trindex0 = trindex
  troneHot :: forall m n x.
              ( KnownSTK x, KnownNat m, KnownNat n
              , BoolOf (PrimalOf target) ~ BoolOf target
              , EqF (PrimalOf target) (TKScalar Int64))
           => IShR m -> target (TKR2 n x) -> IxROf target m
           -> target (TKR2 (m + n) x)
  troneHot sh v ix = case knownSTK @x of
    STKScalar ->
      trscatter @_ @0 (shrAppend sh (rshape v)) v (const ix)
    _ -> case tftk knownSTK v of
      FTKR _ ftk2 ->
        -- TODO: def at out of bounds
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (toList ix) (toList ix2))
                        (trindex0 v (dropIndex ix2))
                        (tconstantTarget 0 (FTKR ZSR ftk2))
        in rbuild (shrAppend sh (rshape v)) f
           -- TODO: if this is used often, maybe express this as the gather that
           -- would come out of vectorization, making sure it simplifies well
  trscatter :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
            => IShR (p + n) -> target (TKR2 (m + n) x)
            -> (IxROf target m -> IxROf target p)
            -> target (TKR2 (p + n) x)
  trscatter1 :: forall n p x. (KnownSTK x, KnownNat n, KnownNat p)
             => IShR (p + n) -> target (TKR2 (1 + n) x)
             -> (IntOf target -> IxROf target p)
             -> target (TKR2 (p + n) x)
  trscatter1 sh v f = trscatter @target @1 sh v (\(i :.: ZIR) -> f i)
  trgather :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x)
           => IShR (m + n) -> target (TKR2 (p + n) x)
           -> (IxROf target m -> IxROf target p)
           -> target (TKR2 (m + n) x)
  trgather1 :: forall n p x. (KnownSTK x, KnownNat n, KnownNat p)
            => Int -> target (TKR2 (p + n) x)
            -> (IntOf target -> IxROf target p)
            -> target (TKR2 (1 + n) x)
  trgather1 k v f = trgather @target @1
                             (k :$: dropShape (rshape v)) v
                             (\(i :.: ZIR) -> f i)

  tsindex :: (KnownShS shm, KnownShS shn, KnownSTK x)
          => target (TKS2 (shm ++ shn) x) -> IxSOf target shm
          -> target (TKS2 shn x)
  tsindex0 :: forall sh1 x. (KnownShS sh1, KnownSTK x)
           => target (TKS2 sh1 x) -> IxSOf target sh1
           -> target (TKS2 '[] x)
  tsindex0 | Refl <- lemAppNil @sh1 = sindex
  tsoneHot :: forall sh1 sh2 x.
              ( KnownShS sh1, KnownShS sh2, KnownSTK x
              , BoolOf (PrimalOf target) ~ BoolOf target
              , EqF (PrimalOf target) (TKScalar Int64) )
           => target (TKS2 sh2 x) -> IxSOf target sh1
           -> target (TKS2 (sh1 ++ sh2) x)
  tsoneHot v ix | SNat <- shsRank (knownShS @sh1) = case knownSTK @x of
    STKScalar ->
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      tsscatter @_ @'[] @_ @sh1 v (const ix)
    _ -> case tftk knownSTK v of
      FTKS _ ftk2 ->
        -- TODO: def at out of bounds
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: '[]) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: (sh1 ++ sh2)) $
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
        withKnownShS (knownShS @sh1 `shsAppend` knownShS @sh2) $
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (Foldable.toList ix) (Foldable.toList ix2))
                        (sindex0 v (dropIxS @(Rank sh1) ix2))
                        (tconstantTarget 0 (FTKS ZSS ftk2))
        in sbuild @(Rank (sh1 ++ sh2)) f
  tsscatter
     :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (shm ++ shn) x)
     -> (IxSOf target shm -> IxSOf target shp)
     -> target (TKS2 (shp ++ shn) x)
  tsscatter1
     :: forall n2 shn shp x.
        (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (n2 ': shn) x)
     -> (IntOf target -> IxSOf target shp)
     -> target (TKS2 (shp ++ shn) x)
  tsscatter1 v f = tsscatter @_ @'[n2] v (\(i :.$ _) -> f i)
  tsgather
     :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (shp ++ shn) x)
     -> (IxSOf target shm -> IxSOf target shp)
     -> target (TKS2 (shm ++ shn) x)
  tsgather1
     :: forall n2 shn shp x.
        (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x)
     => target (TKS2 (shp ++ shn) x)
     -> (IntOf target -> IxSOf target shp)
     -> target (TKS2 (n2 ': shn) x)
  tsgather1 v f = tsgather @target @'[n2] v (\(i :.$ _) -> f i)

  txindex :: (KnownShX sh1, KnownShX sh2, KnownSTK x)
          => target (TKX2 (sh1 ++ sh2) x) -> IxXOf target sh1
          -> target (TKX2 sh2 x)
  txindex0 :: forall sh1 x. (KnownShX sh1, KnownSTK x)
           => target (TKX2 sh1 x) -> IxXOf target sh1
           -> target (TKX2 '[] x)
  txindex0 | Refl <- lemAppNil @sh1 = xindex
  txoneHot :: forall sh1 sh2 x.
              ( KnownShX sh1, KnownShX sh2, KnownSTK x
              , BoolOf (PrimalOf target) ~ BoolOf target
              , EqF (PrimalOf target) (TKScalar Int64), ConvertTensor target )
           => IShX sh1 -> target (TKX2 sh2 x) -> IxXOf target sh1
           -> target (TKX2 (sh1 ++ sh2) x)
  txoneHot sh1 v ix | SNat <- ssxRank (knownShX @sh1) = case knownSTK @x of
    STKScalar ->
      gcastWith (unsafeCoerceRefl :: Take (Rank sh1) (sh1 ++ sh2) :~: sh1) $
      gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
      txscatter @_ @'[] @_ @sh1 (shxAppend sh1 (xshape v)) v (const ix)
    _ -> case tftk knownSTK v of
      FTKX _ ftk2 ->
        -- TODO: def at out of bounds
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: '[]) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank (sh1 ++ sh2)) (sh1 ++ sh2) :~: (sh1 ++ sh2)) $
        gcastWith (unsafeCoerceRefl
                   :: Drop (Rank sh1) (sh1 ++ sh2) :~: sh2) $
        withKnownShX (knownShX @sh1 `ssxAppend` knownShX @sh2) $
        let f ix2 = ifF (foldl' (\ !acc (!i, !i2) -> acc &&* i ==. i2) true
                         $ zip (Foldable.toList ix) (Foldable.toList ix2))
                        (xindex0 v (dropIxX @(Rank sh1) ix2))
                        (tconstantTarget 0 (FTKX ZSX ftk2))
        in xbuild @(Rank (sh1 ++ sh2)) (shxAppend sh1 (xshape v)) f
  txscatter :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
            => IShX (shp ++ shn) -> target (TKX2 (shm ++ shn) x)
            -> (IxXOf target shm -> IxXOf target shp)
            -> target (TKX2 (shp ++ shn) x)
  -- TODO: when we switch to singletons, generalize this to non-Just types.
  txscatter1 :: forall n2 shn shp x.
                (KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x)
             => IShX (shp ++ shn) -> target (TKX2 (Just n2 ': shn) x)
             -> (IntOf target -> IxXOf target shp)
             -> target (TKX2 (shp ++ shn) x)
  txscatter1 sh v f = txscatter @_ @'[Just n2] @_ @shp @x sh v
                                (\(i :.% _) -> f i)
  txgather :: (KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x)
           => IShX (shm ++ shn)
           -> target (TKX2 (shp ++ shn) x)
           -> (IxXOf target shm -> IxXOf target shp)
           -> target (TKX2 (shm ++ shn) x)
  txgather1 :: forall n2 shn shp x.
               (KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x)
            => SNat n2 -> target (TKX2 (shp ++ shn) x)
            -> (IntOf target -> IxXOf target shp)
            -> target (TKX2 (Just n2 ': shn) x)
  txgather1 k v f =
    txgather @target @'[Just n2]
             (Nested.SKnown k :$% shxDropSSX (xshape v) (knownShX @shp)) v
             (\(i :.% ZIX) -> f i)

  trfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
          => target (TKR n r) -> target (TKR n r2)
  trfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                 => target (TKR n r1) -> target (TKR n r2)
  trcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2)
         => target (TKR n r1) -> target (TKR n r2)
  trminIndex, trmaxIndex  -- partial
    :: forall n r r2. (GoodScalar r, GoodScalar r2)
    => target (TKR (1 + n) r) -> target (TKR n r2)
  triota :: GoodScalar r => Int -> target (TKR 1 r)  -- from 0 to n - 1

  tsfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
          => target (TKS sh r) -> target (TKS sh r2)
    -- the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  tsfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                 => target (TKS sh r1) -> target (TKS sh r2)
  tscast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2)
         => target (TKS sh r1) -> target (TKS sh r2)
  tsminIndex, tsmaxIndex  -- partial
    :: forall sh n r r2. (GoodScalar r, GoodScalar r2)
    => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
  tsiota :: (KnownNat n, GoodScalar r)
         => target (TKS '[n] r)  -- from 0 to n - 1

  txfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
          => target (TKX sh r) -> target (TKX sh r2)
  txfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                 => target (TKX sh r1) -> target (TKX sh r2)
  txcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2)
         => target (TKX sh r1) -> target (TKX sh r2)
  txminIndex, txmaxIndex  -- partial
    :: forall sh mn r r2. (GoodScalar r, GoodScalar r2)
    => target (TKX (mn ': sh) r) -> target (TKX (Init (mn ': sh)) r2)
  txiota :: (KnownNat n, GoodScalar r)
         => target (TKX '[Just n] r)  -- from 0 to n - 1

  tkfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
          => target (TKScalar r) -> target (TKScalar r2)
  tkfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                 => target (TKScalar r1) -> target (TKScalar r2)
  tkcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2)
         => target (TKScalar r1) -> target (TKScalar r2)

  trappend :: forall n x. KnownSTK x
           => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
           -> target (TKR2 (1 + n) x)
  trslice :: forall n x. KnownSTK x
          => Int -> Int -> target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
  trreverse :: forall n x. KnownSTK x
            => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
  trtranspose :: forall n x. KnownSTK x
              => Permutation.PermR -> target (TKR2 n x) -> target (TKR2 n x)
  trreshape :: forall n m x. KnownSTK x
            => IShR m -> target (TKR2 n x) -> target (TKR2 m x)

  tsappend :: forall m n sh x. KnownSTK x
           => target (TKS2 (m ': sh) x) -> target (TKS2 (n ': sh) x)
           -> target (TKS2 ((m + n) ': sh) x)
  tsslice :: forall i n k sh x. KnownSTK x
          => SNat i -> SNat n -> SNat k
          -> target (TKS2 (i + n + k ': sh) x) -> target (TKS2 (n ': sh) x)
  tsreverse :: forall n sh x. KnownSTK x
            => target (TKS2 (n ': sh) x) -> target (TKS2 (n ': sh) x)
  tstranspose :: forall perm sh x.
                 ( Permutation.IsPermutation perm
                 , Rank perm <= Rank sh, KnownSTK x )
              => Permutation.Perm perm -> target (TKS2 sh x)
              -> target (TKS2 (Permutation.PermutePrefix perm sh) x)
  tsreshape :: forall sh sh2 x.
               (KnownSTK x, Nested.Product sh ~ Nested.Product sh2)
            => ShS sh2 -> target (TKS2 sh x) -> target (TKS2 sh2 x)

  txappend :: forall m n sh x. KnownSTK x
           => target (TKX2 (Just m ': sh) x) -> target (TKX2 (Just n ': sh) x)
           -> target (TKX2 (Just (m + n) ': sh) x)
  txslice :: forall i n k sh x. KnownSTK x
          => SNat i -> SNat n -> SNat k
          -> target (TKX2 (Just (i + n + k) ': sh) x)
          -> target (TKX2 (Just n ': sh) x)
  txreverse :: forall mn sh x. KnownSTK x
            => target (TKX2 (mn ': sh) x) -> target (TKX2 (mn ': sh) x)
  txtranspose :: forall perm sh x.
                 ( Permutation.KnownPerm perm, Permutation.IsPermutation perm
                 , Rank perm <= Rank sh, KnownSTK x )
              => target (TKX2 sh x)
              -> target (TKX2 (Permutation.PermutePrefix perm sh) x)
  txreshape :: forall sh sh2 x. KnownSTK x
            => IShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)

  -- This is a method mainly so that roneHot can be defined with it.
  trbuild :: forall m n x. (KnownNat m, KnownNat n, KnownSTK x)
          => IShR (m + n) -> (IxROf target m -> target (TKR2 n x))
          -> target (TKR2 (m + n) x)
  trbuild sh0 f0 =
    let buildSh :: IShR m1 -> (IxROf target m1 -> target (TKR2 n x))
                -> target (TKR2 (m1 + n) x)
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | SNat <- shrRank sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in trbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  trbuild1 :: (KnownNat n, KnownSTK x)
           => Int -> (IntOf target -> target (TKR2 n x))
           -> target (TKR2 (1 + n) x)
  trmap0N :: (KnownNat n, KnownSTK x, KnownSTK x1)
          => (target (TKR2 0 x1) -> target (TKR2 0 x)) -> target (TKR2 n x1)
          -> target (TKR2 n x)
  trmap0N f v = rbuild (rshape v) (f . rindex0 v)
  trzipWith0N :: (KnownNat n, KnownSTK x, KnownSTK x1, KnownSTK x2)
              => (target (TKR2 0 x1) -> target (TKR2 0 x2) -> target (TKR2 0 x))
              -> target (TKR2 n x1) -> target (TKR2 n x2) -> target (TKR2 n x)
  trzipWith0N f u v =
    trbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))

  tsbuild :: forall m sh x. (KnownShS sh, KnownShS (Take m sh), KnownSTK x)
          => (IxSOf target (Take m sh) -> target (TKS2 (Drop m sh) x))
          -> target (TKS2 sh x)
  tsbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IxSOf target sh1 -> target (TKS2 (Drop m sh) x))
          -> target (TKS2 (sh1 ++ Drop m sh) x)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          (SNat :$$ sh2, _ :$$ sh2m) ->
            withKnownShS sh2m $
            let g i = buildSh sh2 sh2m (f . (i :.$))
            in tsbuild1 g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (knownShS @(Take m sh)) (knownShS @sh)
  tsbuild1 :: (KnownNat k, KnownShS sh, KnownSTK x)
           => (IntOf target -> target (TKS2 sh x))
           -> target (TKS2 (k ': sh) x)
  tsmap0N :: forall sh x x1.
             (KnownSTK x1, KnownSTK x, KnownShS sh)
          => (target (TKS2 '[] x1) -> target (TKS2 '[] x))
          -> target (TKS2 sh x1)
          -> target (TKS2 sh x)
  tsmap0N f v =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ tsbuild @target @(Rank sh) (f . sindex0 v)
  tszipWith0N :: forall sh x x1 x2.
                 (KnownSTK x1, KnownSTK x2, KnownSTK x, KnownShS sh)
              => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
                  -> target (TKS2 '[] x))
              -> target (TKS2 sh x1) -> target (TKS2 sh x2)
              -> target (TKS2 sh x)
  tszipWith0N f u v =
    gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
    $ tsbuild @target @(Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))

  txbuild :: forall m sh x.
             (KnownSTK x, KnownShX (Take m sh), ConvertTensor target)
          => IShX sh
          -> (IxXOf target (Take m sh) -> target (TKX2 (Drop m sh) x))
          -> target (TKX2 sh x)
  txbuild sh0 f0 =
    let buildSh :: IShX sh1 -> IShX (sh1 ++ Drop m sh)
                -> (IxXOf target sh1 -> target (TKX2 (Drop m sh) x))
                -> target (TKX2 (sh1 ++ Drop m sh) x)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSX, _) -> f ZIX
          (k :$% sh2, _ :$% sh2m) ->
            withKnownShX (ssxFromShape sh2m) $
            let g i = buildSh sh2 sh2m (f . (i :.%))
            in withSNat (fromSMayNat' k) $ \(SNat @n) ->
                 xmcast (ssxFromShape sh1m) $ txbuild1 @_ @n g
    in gcastWith (unsafeCoerceRefl :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (shxTakeSSX (Proxy @(Drop m sh)) sh0
                             (knownShX @(Take m sh))) sh0 f0
  txbuild1 :: (KnownNat k, KnownShX sh, KnownSTK x)
           => (IntOf target -> target (TKX2 sh x))
           -> target (TKX2 (Just k ': sh) x)

  tbuild1 :: forall y k. ConvertTensor target
               -- y comes first, because k easy to set via SNat
          => SNat k -> STensorKind y -> (IntOf target -> target y)
          -> target (BuildTensorKind k y)
  tbuild1 snat@SNat stk0 f =
    let replSTK :: STensorKind z -> (IntOf target -> target z)
                -> target (BuildTensorKind k z)
        replSTK stk g = case stk of
          STKScalar -> sbuild1 (sfromK . g)
          STKR SNat x | Dict <- lemKnownSTK x ->
            rbuild1 (sNatValue snat) g
          STKS sh x | Dict <- lemKnownSTK x ->
            withKnownShS sh $ sbuild1 g
          STKX sh x | Dict <- lemKnownSTK x ->
            withKnownShX sh $ xbuild1 g
          STKProduct @z1 @z2 stk1 stk2 ->
              let f1 i = tproject1 @_ @z1 @z2 $ g i
                  f2 i = tproject2 @_ @z1 @z2 $ g i
                    -- TODO: looks expensive, but hard to do better,
                    -- so let's hope g is full of variables
              in tpair (replSTK stk1 f1) (replSTK stk2 f2)
    in replSTK stk0 f

  -- | A strict right mapAccum.
  --
  -- The applications of 'tfwd' and 'trevDt' performed already at this point
  -- ensure that the computation of a derivative is not repeated
  -- and that its result is shared. However, most of the time
  -- the computation is unnneeded, so the AST instance uses a non-strict
  -- constructor 'AstLambda' for it's instance of 'HFunOf'.
  --
  -- If the same argument functions are passed to many mapAccum calls, as in
  -- > let f = ... in ... (tmapAccumR ... f ...) ... (tmapAccumL ... f ...)
  -- extra care is needed to prevent double derivative computation.
  -- One needs to use tmapAccumRDer manually as in (simplified)
  -- > let f = ...; df = tfwd f; rf = trev f
  -- > in ... (tmapAccumRDer f df rf ...) ... (tmapAccumLDer f df rf ...)
  tmapAccumRDer
    :: forall accShs bShs eShs k.
       Proxy target
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
  tmapAccumLDer
    :: forall accShs bShs eShs k.
       Proxy target
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
  tApply :: HFunOf target x z -> target x -> target z
  tlambda :: FullTensorKind x -> HFun x z -> HFunOf target x z

  -- If the result of the argument function is not a scalar, the result
  -- of this operation is the gradient of a function that additionally
  -- sums all elements of the result. If all elements are equally important
  -- for optimization, this may be exactly what is needed for gradient descent,
  -- unless there are floats of different resolution among the elements and,
  -- e.g., one wants to compensate for that.
  --
  -- These methods (and tlambda) are exactly what is needed as arguments
  -- of tmapAccumRDer.
  trev
    :: FullTensorKind x  -- shape of x and dx
    -> HFun x z  -- x |-> z
    -> HFunOf target x (ADTensorKind x)  -- x |-> dx
  trevDt
    :: FullTensorKind x  -- shape of x and dx
    -> HFun x z  -- x |-> z
    -> HFunOf target (TKProduct (ADTensorKind z) x) (ADTensorKind x)
                 -- [dz, x] |-> dx
  tfwd
    :: FullTensorKind x  -- shape of x and dx
    -> HFun x z  -- x |-> z
    -> HFunOf target (TKProduct (ADTensorKind x) x) (ADTensorKind z)
                 -- [dx, x] |-> dz

  tprimalPart :: target y -> PrimalOf target y
  tdualPart :: STensorKind y -> target y -> DualOf target y
  tfromPrimal :: STensorKind y -> PrimalOf target y -> target y
  tfromDual :: DualOf target y -> target y
  tScale :: (Num (target y), Num (PrimalOf target y))
         => STensorKind y -> PrimalOf target y -> DualOf target y
         -> DualOf target y
  tScale stk s t =
    tdualPart stk $ tfromPrimal @target stk s * tfromDual t


  -- General operations that don't require LetTensor nor ShareTensor
  tsize :: STensorKind y -> target y -> Int
  tsize stk a = case stk of
    STKScalar @r -> case testEquality (typeRep @r) (typeRep @Z0) of
      Just Refl -> 0
      _ -> 1
    STKR _ x | Dict <- lemKnownSTK x -> rsize a
    STKS _ x | Dict <- lemKnownSTK x -> ssize a
    STKX _ x | Dict <- lemKnownSTK x -> xsize a
    STKProduct stk1 stk2 ->
      tsize stk1 (tproject1 a) + tsize stk2 (tproject2 a)
  tftk :: STensorKind y -> target y -> FullTensorKind y
  tpair :: target x -> target z -> target (TKProduct x z)
  tproject1 :: target (TKProduct x z) -> target x
  tproject2 :: target (TKProduct x z) -> target z
  tcond :: Boolean (BoolOf target)
        => STensorKind y
        -> BoolOf target -> target y -> target y -> target y
  ifF :: (Boolean (BoolOf target), KnownSTK y)
      => BoolOf target -> target y -> target y -> target y
  ifF = tcond knownSTK
  minF :: (Boolean (BoolOf target), OrdF target y, KnownSTK y)
       => target y -> target y -> target y
  minF u v = ifF (u <=. v) u v
  maxF :: (Boolean (BoolOf target), OrdF target y, KnownSTK y)
       => target y -> target y -> target y
  maxF u v = ifF (u >=. v) u v

  xmcast :: (KnownSTK x, KnownShX sh, Rank sh ~ Rank sh2, ConvertTensor target)
         => StaticShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)
  xmcast sh2 a = case tftk knownSTK a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShX sh2 $
        withKnownShS sh $
        xfromS $ sfromX @_ @sh a

  -- General operations that use ShareTensor if available, LetTensor otherwise
  tsum
    :: forall z k. ConvertTensor target
    => SNat k -> STensorKind z -> target (BuildTensorKind k z)
    -> target z
  default tsum
    :: forall z k. (ShareTensor target, ConvertTensor target)
    => SNat k -> STensorKind z -> target (BuildTensorKind k z)
    -> target z
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ ssum u
    STKR SNat x | Dict <- lemKnownSTK x -> rsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ ssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xsum u
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (tsum snat stk1 u1)
               (tsum snat stk2 u2)
  treplicate
    :: forall z k. ConvertTensor target
    => SNat k -> STensorKind z -> target z
    -> target (BuildTensorKind k z)
  default treplicate
    :: forall z k. (ShareTensor target, ConvertTensor target)
    => SNat k -> STensorKind z -> target z
    -> target (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> rreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate sh u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xreplicate u
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (treplicate snat stk1 u1)
               (treplicate snat stk2 u2)
  tindexBuild
    :: forall z k. ConvertTensor target
    => SNat k -> STensorKind z -> target (BuildTensorKind k z) -> IntOf target
    -> target z
  default tindexBuild
    :: forall z k. (ShareTensor target, ConvertTensor target)
    => SNat k -> STensorKind z -> target (BuildTensorKind k z) -> IntOf target
    -> target z
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ sindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> rindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ sindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      let (u1, u2) = tunpair u
      in tpair (tindexBuild snat stk1 u1 i)
               (tindexBuild snat stk2 u2 i)

  -- Methods needed only to split off the module that defines them
  tconstantTarget
    :: (forall r. GoodScalar r => r) -> FullTensorKind y -> target y
  -- The arguments need to be duplicable
  taddTarget :: STensorKind y -> target y -> target y -> target y

class ConvertTensor (target :: Target) where
  tpairConv :: target x -> target z -> target (TKProduct x z)
    -- a clone of tpair, to make this class independent of BaseTensor
  default tpairConv :: BaseTensor target
                    => target x -> target z -> target (TKProduct x z)
  tpairConv = tpair
  tunpairDup :: target (TKProduct x z) -> (target x, target z)
  default tunpairDup :: ShareTensor target
                     => target (TKProduct x z) -> (target x, target z)
  tunpairDup = tunpair

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

  -- The semantics for products is element-wise and for others it's either
  -- identity or the domain is shaped and tfromS type-casts to the codomain
  -- by hiding some (or none) type information (so the codomain has to be
  -- a "subtype" of the domain) or error.
  -- A corollary is that tfromS behaves uniformly vs BuildTensorKind.
  tfromS :: STensorKind y -> STensorKind z -> target y -> target z

  kfromR :: GoodScalar r => target (TKR 0 r) -> target (TKScalar r)
  kfromR = kfromS . sfromR
  kfromS :: GoodScalar r => target (TKS '[] r) -> target (TKScalar r)
  kfromS = tfromS knownSTK knownSTK
  kfromX :: GoodScalar r => target (TKX '[] r) -> target (TKScalar r)
  kfromX = kfromS . sfromX
  rfromK :: GoodScalar r => target (TKScalar r) -> target (TKR 0 r)
  rfromK = rfromS . sfromK
  rfromS :: forall sh r. (KnownShS sh, KnownSTK r)
         => target (TKS2 sh r) -> target (TKR2 (Rank sh) r)
  rfromS = tfromS knownSTK (STKR (shsRank (knownShS @sh)) (knownSTK @r))
  rfromX :: forall sh r. KnownSTK r
         => target (TKX2 sh r) -> target (TKR2 (Rank sh) r)
  sfromK :: GoodScalar r => target (TKScalar r) -> target (TKS '[] r)
  sfromR :: (KnownShS sh, KnownSTK r)
         => target (TKR2 (Rank sh) r) -> target (TKS2 sh r)
  sfromX :: (KnownShS sh, Rank sh ~ Rank sh', KnownSTK r)
         => target (TKX2 sh' r) -> target (TKS2 sh r)
  xfromK :: GoodScalar r => target (TKScalar r) -> target (TKX '[] r)
  xfromK = xfromS . sfromK
  xfromR :: forall sh' r. (KnownShX sh', KnownSTK r)
         => target (TKR2 (Rank sh') r) -> target (TKX2 sh' r)
  xfromS :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', KnownSTK r)
         => target (TKS2 sh r) -> target (TKX2 sh' r)
  xfromS = tfromS knownSTK knownSTK

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

tunit :: BaseTensor target
      => target TKUnit
tunit = kconcrete Z0
tlet :: forall x z target. LetTensor target
     => target x -> (target x -> target z) -> target z
tlet = ttlet

rconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Ranked n r -> target (TKR n r)
rconcrete = trconcrete
rscalar :: forall r target. (GoodScalar r, BaseTensor target)
        => r -> target (TKR 0 r)
rscalar r = rconcrete $ Nested.rscalar r
rrepl :: forall n r target. (GoodScalar r, BaseTensor target)
      => IShR n -> r -> target (TKR n r)
rrepl sh a = tconcrete (FTKR sh FTKScalar) (RepN $ Nested.rreplicateScal sh a)
ringestData :: forall n r target. (GoodScalar r, BaseTensor target)
            => IShR n -> [r] -> target (TKR n r)
ringestData sh l =
  tconcrete (FTKR sh FTKScalar) (RepN $ Nested.rfromListPrimLinear sh l)

sconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Shaped sh r -> target (TKS sh r)
sconcrete = tsconcrete
sscalar :: forall r target. (GoodScalar r, BaseTensor target)
        => r -> target (TKS '[] r)
sscalar r = sconcrete $ Nested.sscalar r
srepl :: (KnownShS sh, GoodScalar r, BaseTensor target)
      => r -> target (TKS sh r)
srepl = sconcrete . Nested.sreplicateScal knownShS
  -- TODO: the following simplifies better, because the replication is not
  -- hidden at low level:
  -- Dict <- lemKnownNatSize (knownShS @sh) =
  --   sreplicate0N . sscalar
  -- though we could also look at the low level in @isSmall@ and mark
  -- replicated fromPrimals as small
singestData :: (KnownShS sh, GoodScalar r, BaseTensor target)
            => [r] -> target (TKS sh r)
singestData l = sconcrete $ Nested.sfromListPrimLinear knownShS l

xconcrete :: (GoodScalar r, BaseTensor target)
          => Nested.Mixed sh r -> target (TKX sh r)
xconcrete = txconcrete
xscalar :: forall r target. (GoodScalar r, BaseTensor target)
        => r -> target (TKX '[] r)
xscalar r = xconcrete $ Nested.mscalar r
xrepl :: forall sh r target. (GoodScalar r, BaseTensor target)
      => IShX sh -> r -> target (TKX sh r)
xrepl sh a = tconcrete (FTKX sh FTKScalar) (RepN $ Nested.mreplicateScal sh a)
xingestData :: forall sh r target. (GoodScalar r, BaseTensor target)
            => IShX sh -> [r] -> target (TKX sh r)
xingestData sh l =
  tconcrete (FTKX sh FTKScalar) (RepN $ Nested.mfromListPrimLinear sh l)

kconcrete :: (GoodScalar r, BaseTensor target)
          => r -> target (TKScalar r)
kconcrete = tkconcrete

rfromList :: (KnownNat n, KnownSTK x, BaseTensor target)
          => NonEmpty (target (TKR2 n x)) -> target (TKR2 (1 + n) x)
rfromList = trfromVector . V.fromList . NonEmpty.toList
  -- going through strict vectors, because laziness is risky with impurity
rfromVector :: (KnownNat n, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKR2 n x))
            -> target (TKR2 (1 + n) x)
rfromVector = trfromVector
rfromListLinear :: forall n x target. (KnownSTK x, BaseTensor target)
                => IShR n -> [target (TKR2 0 x)] -> target (TKR2 n x)
rfromListLinear sh = trfromVectorLinear sh . V.fromList
rfromVectorLinear :: forall n x target. (KnownSTK x, BaseTensor target)
                  => IShR n -> Data.Vector.Vector (target (TKR2 0 x))
                  -> target (TKR2 n x)
rfromVectorLinear = trfromVectorLinear
runravelToList :: forall n x target.
                  (KnownSTK x, KnownNat n, BaseTensor target)
               => target (TKR2 (1 + n) x) -> [target (TKR2 n x)]
runravelToList = trunravelToList

sfromList :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
          => NonEmpty (target (TKS2 sh x)) -> target (TKS2 (n ': sh) x)
sfromList = tsfromVector . V.fromList . NonEmpty.toList
-- This is morally non-empty strict vectors:
sfromVector :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKS2 sh x))
            -> target (TKS2 (n ': sh) x)
sfromVector = tsfromVector
sfromListLinear :: (KnownShS sh, KnownSTK x, BaseTensor target)
                => [target (TKS2 '[] x)] -> target (TKS2 sh x)
sfromListLinear = tsfromVectorLinear . V.fromList
sfromVectorLinear :: forall sh x target.
                     (KnownSTK x, KnownShS sh, BaseTensor target)
                  => Data.Vector.Vector (target (TKS2 '[] x))
                  -> target (TKS2 sh x)
sfromVectorLinear = tsfromVectorLinear
sunravelToList :: forall n sh x target.
                  (KnownSTK x, KnownNat n, KnownShS sh, BaseTensor target)
               => target (TKS2 (n ': sh) x) -> [target (TKS2 sh x)]
sunravelToList = tsunravelToList

xfromList :: forall n sh x target.
             (KnownSTK x, KnownNat n, KnownShX sh, BaseTensor target)
          => NonEmpty (target (TKX2 sh x)) -> target (TKX2 (Just n ': sh) x)
xfromList = txfromVector . V.fromList . NonEmpty.toList
  -- going through strict vectors, because laziness is risky with impurity
xfromVector :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
            => Data.Vector.Vector (target (TKX2 sh x))
            -> target (TKX2 (Just n ': sh) x)
xfromVector = txfromVector
xfromListLinear :: forall sh x target. (KnownSTK x, BaseTensor target)
                => IShX sh -> [target (TKX2 '[] x)] -> target (TKX2 sh x)
xfromListLinear sh = txfromVectorLinear sh . V.fromList
xfromVectorLinear :: forall sh x target. (KnownSTK x, BaseTensor target)
                  => IShX sh -> Data.Vector.Vector (target (TKX2 '[] x))
                  -> target (TKX2 sh x)
xfromVectorLinear = txfromVectorLinear
xunravelToList :: forall n sh x target.
                  (KnownSTK x, KnownNat n, KnownShX sh, BaseTensor target)
               => target (TKX2 (Just n ': sh) x) -> [target (TKX2 sh x)]
xunravelToList = txunravelToList

rsum :: (KnownNat n, KnownSTK x, BaseTensor target)
     => target (TKR2 (1 + n) x) -> target (TKR2 n x)
rsum = trsum
rsum0 :: (KnownNat n, KnownSTK x, BaseTensor target)
      => target (TKR2 n x) -> target (TKR2 0 x)
rsum0 = trsum0
rdot0 :: ( KnownNat n, GoodScalar x, BaseTensor target)
      => target (TKR n x) -> target (TKR n x) -> target (TKR 0 x)
rdot0 = trdot0
rdot1In :: (GoodScalar r, BaseTensor target)
        => target (TKR 2 r) -> target (TKR 2 r)
        -> target (TKR 1 r)
rdot1In = trdot1In
rmatvecmul :: (GoodScalar r, BaseTensor target)
           => target (TKR 2 r) -> target (TKR 1 r) -> target (TKR 1 r)
rmatvecmul = trmatvecmul
rmatmul2 :: (GoodScalar r, Numeric r, BaseTensor target)
         => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
rmatmul2 = trmatmul2
rreplicate :: (KnownNat n, KnownSTK x, BaseTensor target)
           => Int -> target (TKR2 n x) -> target (TKR2 (1 + n) x)
rreplicate = trreplicate
rreplicate0N :: (KnownNat n, KnownSTK x, BaseTensor target)
             => IShR n -> target (TKR2 0 x) -> target (TKR2 n x)
rreplicate0N = trreplicate0N

ssum :: (KnownNat n, KnownShS sh, KnownSTK x, BaseTensor target)
     => target (TKS2 (n ': sh) x) -> target (TKS2 sh x)
ssum = tssum
ssum0 :: forall sh x target. (KnownSTK x, KnownShS sh, BaseTensor target)
      => target (TKS2 sh x) -> target (TKS2 '[] x)
ssum0 = tssum0
sdot0 :: forall sh r target. (GoodScalar r, KnownShS sh, BaseTensor target)
      => target (TKS sh r) -> target (TKS sh r) -> target (TKS '[] r)
sdot0 = tsdot0
sdot1In :: (KnownNat n, KnownNat m, GoodScalar r, BaseTensor target)
        => SNat n
        -> target (TKS '[m, n] r) -> target (TKS '[m, n] r)
        -> target (TKS '[m] r)  -- TODO: generalize
sdot1In = tsdot1In
smatvecmul :: forall m n r target.
              (GoodScalar r, KnownNat m, KnownNat n, BaseTensor target)
           => target (TKS '[m, n] r) -> target (TKS '[n] r)
           -> target (TKS '[m] r)
smatvecmul = tsmatvecmul
smatmul2 :: forall n m p r target.
            ( KnownNat n, KnownNat m, KnownNat p, GoodScalar r, Numeric r
            , BaseTensor target )
         => target (TKS '[m, n] r) -> target (TKS '[n, p] r)
         -> target (TKS '[m, p] r)
smatmul2 = tsmatmul2
sreplicate :: (KnownNat k, KnownShS sh, KnownSTK x, BaseTensor target)
           => target (TKS2 sh x) -> target (TKS2 (k ': sh) x)
sreplicate = tsreplicate knownShS
sreplicate0N :: forall sh x target.
                (KnownSTK x, KnownShS sh, BaseTensor target)
             => target (TKS2 '[] x) -> target (TKS2 sh x)
sreplicate0N = tsreplicate0N knownShS

xsum :: (KnownNat n, KnownShX sh, KnownSTK x, BaseTensor target)
     => target (TKX2 (Just n ': sh) x) -> target (TKX2 sh x)
xsum = txsum
xsum0 :: (KnownShX sh, KnownSTK x, BaseTensor target, ConvertTensor target)
      => target (TKX2 sh x) -> target (TKX2 '[] x)
xsum0 = txsum0
xdot0 :: ( KnownShX sh, GoodScalar r
         , BaseTensor target, ConvertTensor target )
      => target (TKX sh r) -> target (TKX sh r) -> target (TKX '[] r)
xdot0 = txdot0
xdot1In :: (KnownNat n, KnownNat m, GoodScalar r, BaseTensor target)
        => target (TKX '[Just m, Just n] r)
        -> target (TKX '[Just m, Just n] r)
        -> target (TKX '[Just m] r)
xdot1In = txdot1In
xmatvecmul :: forall mm mn r target.
              (GoodScalar r, BaseTensor target, ConvertTensor target)
           => Nested.SMayNat Int SNat mm -> Nested.SMayNat Int SNat mn
           -> target (TKX '[mm, mn] r) -> target (TKX '[mn] r)
           -> target (TKX '[mm] r)
xmatvecmul = txmatvecmul
xmatmul2 :: forall n m p r target.
            ( GoodScalar r, BaseTensor target, ConvertTensor target
            , Numeric r, KnownNat n, KnownNat m, KnownNat p )
         => target (TKX '[Just m, Just n] r)
         -> target (TKX '[Just n, Just p] r)
         -> target (TKX '[Just m, Just p] r)
xmatmul2 = txmatmul2
xreplicate :: (KnownNat k, KnownShX sh, KnownSTK x, BaseTensor target)
           => target (TKX2 sh x) -> target (TKX2 (Just k ': sh) x)
xreplicate = txreplicate
xreplicate0N :: (KnownShX sh, KnownSTK x, BaseTensor target)
             => IShX sh -> target (TKX2 '[] x) -> target (TKX2 sh x)
xreplicate0N = txreplicate0N

rindex, (!) :: (KnownNat m, KnownNat n, KnownSTK x, BaseTensor target)
            => target (TKR2 (m + n) x) -> IxROf target m -> target (TKR2 n x)
rindex = trindex
infixl 9 !
(!) = rindex  -- prefix form better when type applications are necessary
rindex0 :: (KnownNat m, KnownSTK x, BaseTensor target)
        => target (TKR2 m x) -> IxROf target m -> target (TKR2 0 x)
rindex0 = trindex0
roneHot :: forall m n x target.
           ( KnownSTK x, KnownNat m, KnownNat n
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqF (PrimalOf target) (TKScalar Int64), BaseTensor target)
        => IShR m -> target (TKR2 n x) -> IxROf target m
        -> target (TKR2 (m + n) x)
roneHot = troneHot
rscatter :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
         => IShR (p + n) -> target (TKR2 (m + n) x)
         -> (IxROf target m -> IxROf target p)
         -> target (TKR2 (p + n) x)
rscatter = trscatter
rscatter1 :: forall n p x target.
             (KnownSTK x, KnownNat n, KnownNat p, BaseTensor target)
          => IShR (p + n) -> target (TKR2 (1 + n) x)
          -> (IntOf target -> IxROf target p)
          -> target (TKR2 (p + n) x)
rscatter1 = trscatter1
rgather :: (KnownNat m, KnownNat n, KnownNat p, KnownSTK x, BaseTensor target)
        => IShR (m + n) -> target (TKR2 (p + n) x)
        -> (IxROf target m -> IxROf target p)
        -> target (TKR2 (m + n) x)
rgather = trgather
rgather1 :: forall n p x target.
            (KnownSTK x, KnownNat n, KnownNat p, BaseTensor target)
         => Int -> target (TKR2 (p + n) x)
         -> (IntOf target -> IxROf target p)
         -> target (TKR2 (1 + n) x)
rgather1 = trgather1

sindex, (!$) :: (KnownShS shm, KnownShS shn, KnownSTK x, BaseTensor target)
             => target (TKS2 (shm ++ shn) x) -> IxSOf target shm
             -> target (TKS2 shn x)
sindex = tsindex
infixl 9 !$
(!$) = sindex  -- prefix form better when type applications are necessary
sindex0 :: forall sh1 x target. (KnownShS sh1, KnownSTK x, BaseTensor target)
        => target (TKS2 sh1 x) -> IxSOf target sh1
        -> target (TKS2 '[] x)
sindex0 = tsindex0
soneHot :: forall sh1 sh2 x target.
           ( KnownShS sh1, KnownShS sh2, KnownSTK x
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqF (PrimalOf target) (TKScalar Int64), BaseTensor target )
        => target (TKS2 sh2 x) -> IxSOf target sh1
        -> target (TKS2 (sh1 ++ sh2) x)
soneHot = tsoneHot
sscatter
  :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shm ++ shn) x)
  -> (IxSOf target shm -> IxSOf target shp)
  -> target (TKS2 (shp ++ shn) x)
sscatter @shm @shn @shp = tsscatter @_ @shm @shn @shp
sscatter1
  :: forall n2 shn shp x target.
     (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (n2 ': shn) x)
  -> (IntOf target -> IxSOf target shp)
  -> target (TKS2 (shp ++ shn) x)
sscatter1 = tsscatter1
sgather
  :: (KnownShS shm, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shp ++ shn) x)
  -> (IxSOf target shm -> IxSOf target shp)
  -> target (TKS2 (shm ++ shn) x)
sgather @shm @shn @shp = tsgather @_ @shm @shn @shp
sgather1
  :: forall n2 shn shp x target.
     (KnownNat n2, KnownShS shn, KnownShS shp, KnownSTK x, BaseTensor target)
  => target (TKS2 (shp ++ shn) x)
  -> (IntOf target -> IxSOf target shp)
  -> target (TKS2 (n2 ': shn) x)
sgather1 = tsgather1

xindex :: (KnownShX sh1, KnownShX sh2, KnownSTK x, BaseTensor target)
       => target (TKX2 (sh1 ++ sh2) x) -> IxXOf target sh1
       -> target (TKX2 sh2 x)
xindex = txindex
xindex0 :: forall sh1 x target. (KnownShX sh1, KnownSTK x, BaseTensor target)
        => target (TKX2 sh1 x) -> IxXOf target sh1
        -> target (TKX2 '[] x)
xindex0 = txindex0
xoneHot :: forall sh1 sh2 x target.
           ( KnownShX sh1, KnownShX sh2, KnownSTK x
           , BoolOf (PrimalOf target) ~ BoolOf target
           , EqF (PrimalOf target) (TKScalar Int64)
           , BaseTensor target, ConvertTensor target )
        => IShX sh1 -> target (TKX2 sh2 x) -> IxXOf target sh1
        -> target (TKX2 (sh1 ++ sh2) x)
xoneHot = txoneHot
xscatter :: ( KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x
            , BaseTensor target )
         => IShX (shp ++ shn) -> target (TKX2 (shm ++ shn) x)
         -> (IxXOf target shm -> IxXOf target shp)
         -> target (TKX2 (shp ++ shn) x)
xscatter @shm @shn @shp = txscatter @_ @shm @shn @shp
xscatter1 :: forall n2 shn shp x target.
             ( KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x
             , BaseTensor target )
          => IShX (shp ++ shn) -> target (TKX2 (Just n2 ': shn) x)
          -> (IntOf target -> IxXOf target shp)
          -> target (TKX2 (shp ++ shn) x)
xscatter1 = txscatter1
xgather :: ( KnownShX shm, KnownShX shn, KnownShX shp, KnownSTK x
           , BaseTensor target )
        => IShX (shm ++ shn)
        -> target (TKX2 (shp ++ shn) x)
        -> (IxXOf target shm -> IxXOf target shp)
        -> target (TKX2 (shm ++ shn) x)
xgather @shm @shn @shp = txgather @_ @shm @shn @shp
xgather1 :: forall n2 shn shp x target.
            ( KnownNat n2, KnownShX shn, KnownShX shp, KnownSTK x
            , BaseTensor target )
         => SNat n2 -> target (TKX2 (shp ++ shn) x)
         -> (IntOf target -> IxXOf target shp)
         -> target (TKX2 (Just n2 ': shn) x)
xgather1 = txgather1

rfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKR n r) -> target (TKR n r2)
rfloor = trfloor
rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKR n r1) -> target (TKR n r2)
rfromIntegral = trfromIntegral
rcast :: ( RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2
         , BaseTensor target )
      => target (TKR n r1) -> target (TKR n r2)
rcast = trcast
rminIndex, rmaxIndex  -- partial
  :: forall n r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKR (1 + n) r) -> target (TKR n r2)
rminIndex = trminIndex
rmaxIndex = trmaxIndex
riota :: (GoodScalar r, BaseTensor target)
      => Int -> target (TKR 1 r)  -- from 0 to n - 1
riota = triota

sfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKS sh r) -> target (TKS sh r2)
sfloor = tsfloor
sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKS sh r1) -> target (TKS sh r2)
sfromIntegral = tsfromIntegral
scast :: ( RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2
         , BaseTensor target )
      => target (TKS sh r1) -> target (TKS sh r2)
scast = tscast
sminIndex, smaxIndex  -- partial
  :: forall sh n r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKS (n ': sh) r) -> target (TKS (Init (n ': sh)) r2)
sminIndex = tsminIndex
smaxIndex = tsmaxIndex
siota :: (KnownNat n, GoodScalar r, BaseTensor target)
      => target (TKS '[n] r)  -- from 0 to n - 1
siota = tsiota

xfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKX sh r) -> target (TKX sh r2)
xfloor = txfloor
xfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKX sh r1) -> target (TKX sh r2)
xfromIntegral = txfromIntegral
xcast :: ( RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2
         , BaseTensor target )
      => target (TKX sh r1) -> target (TKX sh r2)
xcast = txcast
xminIndex, xmaxIndex  -- partial
  :: forall sh mn r r2 target. (GoodScalar r, GoodScalar r2, BaseTensor target)
  => target (TKX (mn ': sh) r) -> target (TKX (Init (mn ': sh)) r2)
xminIndex = txminIndex
xmaxIndex = txmaxIndex
xiota :: (KnownNat n, GoodScalar r, BaseTensor target)
      => target (TKX '[Just n] r)  -- from 0 to n - 1
xiota = txiota

kfloor :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
          , BaseTensor target )
       => target (TKScalar r) -> target (TKScalar r2)
kfloor = tkfloor
kfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, BaseTensor target)
              => target (TKScalar r1) -> target (TKScalar r2)
kfromIntegral = tkfromIntegral
kcast :: ( RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2
         , BaseTensor target )
      => target (TKScalar r1) -> target (TKScalar r2)
kcast = tkcast

rappend :: forall n x target. (KnownSTK x, BaseTensor target)
        => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
        -> target (TKR2 (1 + n) x)
rappend = trappend
rconcat :: forall n x target. (KnownSTK x, BaseTensor target)
        => NonEmpty (target (TKR2 (1 + n) x)) -> target (TKR2 (1 + n) x)
rconcat = foldr1 rappend
rslice :: forall n x target. (KnownSTK x, BaseTensor target)
       => Int -> Int -> target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
rslice = trslice
runcons :: (KnownNat n, KnownSTK x, BaseTensor target)
        => target (TKR2 (1 + n) x)
        -> Maybe (target (TKR2 n x), target (TKR2 (1 + n) x))
runcons v = case rshape v of
              len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
rreverse :: forall n x target. (KnownSTK x, BaseTensor target)
         => target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x)
rreverse = trreverse
rtr :: forall n x target. (KnownSTK x, BaseTensor target)
    => target (TKR2 (2 + n) x) -> target (TKR2 (2 + n) x)
rtr = trtranspose [1, 0]
rtranspose :: forall n x target. (KnownSTK x, BaseTensor target)
           => Permutation.PermR -> target (TKR2 n x) -> target (TKR2 n x)
rtranspose = trtranspose
rflatten :: forall n x target. (KnownSTK x, BaseTensor target)
         => target (TKR2 n x) -> target (TKR2 1 x)
rflatten u = trreshape (rsize u :$: ZSR) u
rreshape :: forall n m x target. (KnownSTK x, BaseTensor target)
         => IShR m -> target (TKR2 n x) -> target (TKR2 m x)
rreshape = trreshape

sappend :: forall m n sh x target. (KnownSTK x, BaseTensor target)
        => target (TKS2 (m ': sh) x) -> target (TKS2 (n ': sh) x)
        -> target (TKS2 ((m + n) ': sh) x)
sappend = tsappend
sslice :: forall i n k sh x target. (KnownSTK x, BaseTensor target)
       => SNat i -> SNat n -> SNat k
       -> target (TKS2 (i + n + k ': sh) x) -> target (TKS2 (n ': sh) x)
sslice = tsslice
suncons :: forall n sh x target.
           (KnownSTK x, KnownNat n, KnownShS sh, BaseTensor target)
        => target (TKS2 (n ': sh) x)
        -> Maybe (target (TKS2 sh x), target (TKS2 (n - 1 ': sh) x))
suncons v = case cmpNat (Proxy @1) (Proxy @n) of
 EQI -> Just ( v !$ (0 :.$ ZIS)
             , sslice @1 @(n - 1) @0 SNat SNat SNat v )
 LTI -> Just ( v !$ (0 :.$ ZIS)
             , sslice @1 @(n - 1) @0 SNat SNat SNat v )
 _ -> Nothing
sreverse :: forall n sh x target. (KnownSTK x, BaseTensor target)
         => target (TKS2 (n ': sh) x) -> target (TKS2 (n ': sh) x)
sreverse = tsreverse
str :: forall n m sh x target. (KnownSTK x, BaseTensor target)
    => target (TKS2 (n ': m ': sh) x) -> target (TKS2 (m ': n ': sh) x)
str = gcastWith (unsafeCoerceRefl :: (2 <=? Rank (n ': m ': sh)) :~: True) $
      tstranspose (Permutation.makePerm @'[1, 0])
stranspose :: forall perm sh x target.
              ( Permutation.KnownPerm perm, Permutation.IsPermutation perm
              , Rank perm <= Rank sh, KnownSTK x, BaseTensor target )
           => target (TKS2 sh x)
           -> target (TKS2 (Permutation.PermutePrefix perm sh) x)
stranspose = tstranspose (Permutation.makePerm @perm)
sflatten :: forall sh x target. (KnownSTK x, KnownShS sh, BaseTensor target )
         => target (TKS2 sh x) -> target (TKS2 '[Nested.Product sh] x)
sflatten | SNat <- shsProduct (knownShS @sh) = sreshape
sreshape :: forall sh sh2 x target.
            ( KnownSTK x, KnownShS sh2, Nested.Product sh ~ Nested.Product sh2
            , BaseTensor target )
         => target (TKS2 sh x) -> target (TKS2 sh2 x)
sreshape = tsreshape knownShS

xappend :: forall m n sh x target. (KnownSTK x, BaseTensor target)
        => target (TKX2 (Just m ': sh) x) -> target (TKX2 (Just n ': sh) x)
        -> target (TKX2 (Just (m + n) ': sh) x)
xappend = txappend
xappend0 :: forall sh x target.
            (KnownSTK x, BaseTensor target, ConvertTensor target)
         => target (TKX2 (Nothing ': sh) x) -> target (TKX2 (Nothing ': sh) x)
        -> target (TKX2 (Nothing ': sh) x)
xappend0 a b = case xshape a of
 mmsnat :$% sh ->
   withSNat (fromSMayNat' mmsnat) $ \msnat ->
   withSNat (shxLength $ xshape b) $ \nsnat ->
   let sh0 = Nested.SUnknown () :!% ssxFromShape sh
       sha = Nested.SKnown msnat :!% ssxFromShape sh
       shb = Nested.SKnown nsnat :!% ssxFromShape sh
   in withKnownShX (ssxFromShape sh) $
      xmcast sh0 $ xappend (xmcast sha a) (xmcast shb b)
xconcat :: forall sh x target.
           (KnownSTK x, BaseTensor target, ConvertTensor target)
        => NonEmpty (target (TKX2 (Nothing ': sh) x))
        -> target (TKX2 (Nothing ': sh) x)
xconcat = foldr1 xappend0
xslice :: forall i n k sh x target. (KnownSTK x, BaseTensor target)
       => SNat i -> SNat n -> SNat k
       -> target (TKX2 (Just (i + n + k) ': sh) x)
       -> target (TKX2 (Just n ': sh) x)
xslice = txslice
xuncons :: forall n sh x target.
           (KnownSTK x, KnownNat n, KnownShX sh, BaseTensor target)
        => target (TKX2 (Just n ': sh) x)
        -> Maybe (target (TKX2 sh x), target (TKX2 (Just (n - 1) ': sh) x))
xuncons v = case cmpNat (Proxy @1) (Proxy @n) of
 EQI -> Just ( v `xindex` (0 :.% ZIX)
             , xslice @1 @(n - 1) @0 SNat SNat SNat v )
 LTI -> Just ( v `xindex` (0 :.% ZIX)
             , xslice @1 @(n - 1) @0 SNat SNat SNat v )
 _ -> Nothing
xreverse :: forall mn sh x target. (KnownSTK x, BaseTensor target)
         => target (TKX2 (mn ': sh) x) -> target (TKX2 (mn ': sh) x)
xreverse = txreverse
xtr :: forall n m sh x target. (KnownSTK x, BaseTensor target)
    => target (TKX2 (Just n ': Just m ': sh) x)
    -> target (TKX2 (Just m ': Just n ': sh) x)
xtr = gcastWith (unsafeCoerceRefl
                 :: (2 <=? Rank (Just n ': Just m ': sh)) :~: True) $
      txtranspose @_ @'[1, 0]
xtranspose :: forall perm sh x target.
              ( Permutation.KnownPerm perm, Permutation.IsPermutation perm
              , Rank perm <= Rank sh, KnownSTK x, BaseTensor target )
           => target (TKX2 sh x)
           -> target (TKX2 (Permutation.PermutePrefix perm sh) x)
xtranspose = txtranspose @_ @perm
xflatten :: forall sh x target. (KnownSTK x, BaseTensor target)
         => target (TKX2 sh x) -> target (TKX2 '[Nothing] x)
xflatten u = txreshape (Nested.SUnknown (xsize u) :$% ZSX) u
xreshape :: forall sh sh2 x target. (KnownSTK x, BaseTensor target)
         => IShX sh2 -> target (TKX2 sh x) -> target (TKX2 sh2 x)
xreshape = txreshape

rbuild :: forall m n x target.
          (KnownNat m, KnownNat n, KnownSTK x, BaseTensor target)
       => IShR (m + n) -> (IxROf target m -> target (TKR2 n x))
       -> target (TKR2 (m + n) x)
rbuild = trbuild
rbuild1 :: (KnownNat n, KnownSTK x, BaseTensor target)
        => Int -> (IntOf target -> target (TKR2 n x))
        -> target (TKR2 (1 + n) x)
rbuild1 = trbuild1
rmap :: (KnownNat m, KnownNat n, KnownSTK x, KnownSTK x2, BaseTensor target)
     => (target (TKR2 n x) -> target (TKR2 n x2))
     -> target (TKR2 (m + n) x) -> target (TKR2 (m + n) x2)
rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
rmap1 :: (KnownNat n, KnownSTK x, KnownSTK x2, BaseTensor target)
      => (target (TKR2 n x) -> target (TKR2 n x2))
      -> target (TKR2 (1 + n) x) -> target (TKR2 (1 + n) x2)
rmap1 f u = rbuild1 (rwidth u) (\i -> f (u ! [i]))
rmap0N :: (KnownNat n, KnownSTK x, KnownSTK x1, BaseTensor target)
       => (target (TKR2 0 x1) -> target (TKR2 0 x)) -> target (TKR2 n x1)
       -> target (TKR2 n x)
rmap0N = trmap0N
rzipWith :: ( KnownNat m, KnownNat n1, KnownNat n2, KnownNat n, KnownSTK r
            , KnownSTK r1, KnownSTK r2, BaseTensor target )
         => IShR (m + n)
         -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
         -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2)
         -> target (TKR2 (m + n) r)
rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
rzipWith1 :: ( KnownNat n1, KnownNat n2, KnownNat n, KnownSTK r
             , KnownSTK r1, KnownSTK r2, BaseTensor target)
          => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n r))
          -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n) r)
rzipWith1 f u v = rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]))
rzipWith0N :: ( KnownNat n, KnownSTK x, KnownSTK x1, KnownSTK x2
              , BaseTensor target )
           => (target (TKR2 0 x1) -> target (TKR2 0 x2) -> target (TKR2 0 x))
           -> target (TKR2 n x1) -> target (TKR2 n x2) -> target (TKR2 n x)
rzipWith0N  = trzipWith0N
rzipWith3 :: ( KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3
             , KnownNat n, KnownSTK r
             , KnownSTK r1, KnownSTK r2, KnownSTK r3, BaseTensor target )
          => IShR (m + n)
          -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
          -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
          -> target (TKR2 (m + n) r)
rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
rzipWith31 :: ( KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n, KnownSTK r
              , KnownSTK r1, KnownSTK r2, KnownSTK r3, BaseTensor target )
           => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n r))
           -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
           -> target (TKR2 (1 + n) r)
rzipWith31 f u v w =
  rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
rzipWith30N :: ( KnownNat n, KnownSTK r
               , KnownSTK r1, KnownSTK r2, KnownSTK r3, BaseTensor target )
            => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r))
            -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r)
rzipWith30N f u v w =
  rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
rzipWith4 :: ( KnownNat m
             , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
             , KnownNat n, KnownSTK r
             , KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
             , BaseTensor target )
          => IShR (m + n)
          -> (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
              -> target (TKR2 n r))
          -> target (TKR2 (m + n1) r1) -> target (TKR2 (m + n2) r2) -> target (TKR2 (m + n3) r3)
          -> target (TKR2 (m + n4) r4)
          -> target (TKR2 (m + n) r)
rzipWith4 sh f u v w x =
  rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
rzipWith41 :: ( KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
              , KnownNat n, KnownSTK r
              , KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
              , BaseTensor target )
           => (target (TKR2 n1 r1) -> target (TKR2 n2 r2) -> target (TKR2 n3 r3) -> target (TKR2 n4 r4)
               -> target (TKR2 n r))
           -> target (TKR2 (1 + n1) r1) -> target (TKR2 (1 + n2) r2) -> target (TKR2 (1 + n3) r3)
           -> target (TKR2 (1 + n4) r4)
           -> target (TKR2 (1 + n) r)
rzipWith41 f u v w x =
  rbuild1 (rwidth u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
rzipWith40N :: ( KnownNat n, KnownSTK r
               , KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
               , BaseTensor target )
            => (target (TKR2 0 r1) -> target (TKR2 0 r2) -> target (TKR2 0 r3) -> target (TKR2 0 r4)
                -> target (TKR2 0 r))
            -> target (TKR2 n r1) -> target (TKR2 n r2) -> target (TKR2 n r3) -> target (TKR2 n r4)
            -> target (TKR2 n r)
rzipWith40N f u v w x =
  rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                              (rindex0 x ix))

sbuild :: forall m sh x target.
          (KnownShS sh, KnownShS (Take m sh), KnownSTK x, BaseTensor target)
       => (IxSOf target (Take m sh) -> target (TKS2 (Drop m sh) x))
       -> target (TKS2 sh x)
sbuild = tsbuild
sbuild1 :: (KnownNat k, KnownShS sh, KnownSTK x, BaseTensor target)
        => (IntOf target -> target (TKS2 sh x))
        -> target (TKS2 (k ': sh) x)
sbuild1 = tsbuild1
smap :: forall m sh x x2 target.
        ( KnownSTK x, KnownSTK x2
        , KnownShS sh, KnownShS (Take m sh), KnownShS (Drop m sh)
        , BaseTensor target )
     => (target (TKS2 (Drop m sh) x) -> target (TKS2 (Drop m sh) x2))
     -> target (TKS2 sh x) -> target (TKS2 sh x2)
smap f v = gcastWith (unsafeCoerceRefl
                      :: sh :~: Take m sh ++ Drop m sh)
           $ sbuild (\ix -> f (v !$ ix))
smap1 :: forall sh n x x2 target.
         (KnownSTK x, KnownSTK x2, KnownNat n, KnownShS sh, BaseTensor target)
      => (target (TKS2 sh x) -> target (TKS2 sh x2))
      -> target (TKS2 (n ': sh) x) -> target (TKS2 (n ': sh) x2)
smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
smap0N :: forall sh x x1 target.
          (KnownSTK x1, KnownSTK x, KnownShS sh, BaseTensor target)
       => (target (TKS2 '[] x1) -> target (TKS2 '[] x)) -> target (TKS2 sh x1)
       -> target (TKS2 sh x)
smap0N = tsmap0N
szipWith :: forall m sh1 sh2 sh r r1 r2 target.
            ( KnownSTK r1, KnownSTK r2, KnownSTK r, KnownShS sh
            , KnownShS (Take m sh), KnownShS (Drop m sh1)
            , KnownShS (Drop m sh2)
            , sh1 ~ Take m sh ++ Drop m sh1
            , sh2 ~ Take m sh ++ Drop m sh2, BaseTensor target )
         => (target (TKS2 (Drop m sh1) r1)
             -> target (TKS2 (Drop m sh2) r2)
             -> target (TKS2 (Drop m sh) r))
         -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r)
szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
szipWith1 :: forall n sh1 sh2 sh r r1 r2 target.
             ( KnownSTK r1, KnownSTK r2, KnownSTK r
             , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh
             , BaseTensor target )
          => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh r))
          -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
          -> target (TKS2 (n ': sh) r)
szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                   (v !$ (i :.$ ZIS)))
szipWith0N :: forall sh x x1 x2 target.
              ( KnownSTK x1, KnownSTK x2, KnownSTK x, KnownShS sh
              , BaseTensor target )
           => (target (TKS2 '[] x1) -> target (TKS2 '[] x2)
               -> target (TKS2 '[] x))
           -> target (TKS2 sh x1) -> target (TKS2 sh x2)
           -> target (TKS2 sh x)
szipWith0N = tszipWith0N
szipWith3 :: forall m sh1 sh2 sh3 sh r r1 r2 r3 target.
             ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
             , KnownShS sh
             , KnownShS (Take m sh), KnownShS (Drop m sh1)
             , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
             , sh1 ~ Take m sh ++ Drop m sh1
             , sh2 ~ Take m sh ++ Drop m sh2
             , sh3 ~ Take m sh ++ Drop m sh3, BaseTensor target )
          => (target (TKS2 (Drop m sh1) r1)
              -> target (TKS2 (Drop m sh2) r2)
              -> target (TKS2 (Drop m sh3) r3)
              -> target (TKS2 (Drop m sh) r))
          -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r)
szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
szipWith31 :: forall n sh1 sh2 sh3 sh r r1 r2 r3 target.
              ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
              , KnownNat n
              , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
              , BaseTensor target )
           => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh r))
           -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
           -> target (TKS2 (n ': sh3) r3)
           -> target (TKS2 (n ': sh) r)
szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                      (v !$ (i :.$ ZIS))
                                      (w !$ (i :.$ ZIS)))
szipWith30N :: forall sh r r1 r2 r3 target.
               ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r
               , KnownShS sh, BaseTensor target )
            => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                -> target (TKS2 '[] r))
            -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r)
szipWith30N f u v w =
  gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
  $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
  $ sbuild @(Rank sh) (\ix -> f (sindex0 u ix)
                                (sindex0 v ix)
                                (sindex0 w ix))
szipWith4 :: forall m sh1 sh2 sh3 sh4 sh r r1 r2 r3 r4 target.
             ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
             , KnownSTK r, KnownShS sh
             , KnownShS (Take m sh), KnownShS (Drop m sh1)
             , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
             , KnownShS (Drop m sh4)
             , sh1 ~ Take m sh ++ Drop m sh1
             , sh2 ~ Take m sh ++ Drop m sh2
             , sh3 ~ Take m sh ++ Drop m sh3
             , sh4 ~ Take m sh ++ Drop m sh4, BaseTensor target )
          => (target (TKS2 (Drop m sh1) r1)
              -> target (TKS2 (Drop m sh2) r2)
              -> target (TKS2 (Drop m sh3) r3)
              -> target (TKS2 (Drop m sh4) r4)
              -> target (TKS2 (Drop m sh) r))
          -> target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3) -> target (TKS2 sh4 r4)
          -> target (TKS2 sh r)
szipWith4 f u v w x =
  sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
szipWith41 :: forall n sh1 sh2 sh3 sh4 sh r r1 r2 r3 r4 target.
              ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
              , KnownSTK r, KnownNat n
              , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
              , KnownShS sh, BaseTensor target )
           => (target (TKS2 sh1 r1) -> target (TKS2 sh2 r2) -> target (TKS2 sh3 r3)
               -> target (TKS2 sh4 r4) -> target (TKS2 sh r))
           -> target (TKS2 (n ': sh1) r1) -> target (TKS2 (n ': sh2) r2)
           -> target (TKS2 (n ': sh3) r3) -> target (TKS2 (n ': sh4) r4)
           -> target (TKS2 (n ': sh) r)
szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS))
                                        (x !$ (i :.$ ZIS)))
szipWith40N :: forall sh r r1 r2 r3 r4 target.
               ( KnownSTK r1, KnownSTK r2, KnownSTK r3, KnownSTK r4
               , KnownSTK r, KnownShS sh, BaseTensor target )
            => (target (TKS2 '[] r1) -> target (TKS2 '[] r2) -> target (TKS2 '[] r3)
                -> target (TKS2 '[] r4) -> target (TKS2 '[] r))
            -> target (TKS2 sh r1) -> target (TKS2 sh r2) -> target (TKS2 sh r3) -> target (TKS2 sh r4)
            -> target (TKS2 sh r)
szipWith40N f u v w x =
  gcastWith (unsafeCoerceRefl :: Drop (Rank sh) sh :~: '[])
  $ gcastWith (unsafeCoerceRefl :: Take (Rank sh) sh :~: sh)
  $ sbuild @(Rank sh) (\ix -> f (sindex0 u ix)
                                (sindex0 v ix)
                                (sindex0 w ix)
                                (sindex0 x ix))

xbuild :: forall m sh x target.
          ( KnownSTK x, KnownShX (Take m sh)
          , BaseTensor target, ConvertTensor target )
       => IShX sh
       -> (IxXOf target (Take m sh) -> target (TKX2 (Drop m sh) x))
       -> target (TKX2 sh x)
xbuild = txbuild
xbuild1 :: (KnownNat k, KnownShX sh, KnownSTK x, BaseTensor target)
        => (IntOf target -> target (TKX2 sh x))
        -> target (TKX2 (Just k ': sh) x)
xbuild1 = txbuild1
-- xmap and other special cases of build can be defined by the user.

rfold
  :: forall n m rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownSTK rn, KnownSTK rm, KnownNat n, KnownNat m )
  => (forall f. ADReady f => f (TKR2 n rn) -> f (TKR2 m rm) -> f (TKR2 n rn))
  -> target (TKR2 n rn)
  -> target (TKR2 (1 + m) rm)
  -> target (TKR2 n rn)
{-# INLINE rfold #-}
rfold f acc0 es =
  withSNat (rwidth es) $ \k -> tfold k knownSTK knownSTK f acc0 es
rscan
  :: forall n m rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownSTK rn, KnownSTK rm, KnownNat n, KnownNat m )
  => (forall f. ADReady f => f (TKR2 n rn) -> f (TKR2 m rm) -> f (TKR2 n rn))
  -> target (TKR2 n rn)
  -> target (TKR2 (1 + m) rm)
  -> target (TKR2 (1 + n) rn)
{-# INLINE rscan #-}
rscan f acc0 es =
  withSNat (rwidth es) $ \k -> tscan k knownSTK knownSTK f acc0 es
sfold
  :: forall k sh shm rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownNat k, KnownSTK rn, KnownSTK rm, KnownShS sh, KnownShS shm )
  => (forall f. ADReady f
      => f (TKS2 sh rn) -> f (TKS2 shm rm) -> f (TKS2 sh rn))
  -> target (TKS2 sh rn)
  -> target (TKS2 (k ': shm) rm)
  -> target (TKS2 sh rn)
{-# INLINE sfold #-}
sfold = tfold (SNat @k) knownSTK knownSTK
sscan
  :: forall k sh shm rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownNat k, KnownSTK rn, KnownSTK rm, KnownShS sh, KnownShS shm )
  => (forall f.
      ADReady f => f (TKS2 sh rn) -> f (TKS2 shm rm) -> f (TKS2 sh rn))
  -> target (TKS2 sh rn)
  -> target (TKS2 (k ': shm) rm)
  -> target (TKS2 (1 + k ': sh) rn)
{-# INLINE sscan #-}
sscan = tscan (SNat @k) knownSTK knownSTK
xfold
  :: forall k sh shm rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownNat k, KnownSTK rn, KnownSTK rm, KnownShX sh, KnownShX shm )
  => (forall f.
      ADReady f => f (TKX2 sh rn) -> f (TKX2 shm rm) -> f (TKX2 sh rn))
  -> target (TKX2 sh rn)
  -> target (BuildTensorKind k (TKX2 shm rm))
  -> target (TKX2 sh rn)
{-# INLINE xfold #-}
xfold = tfold (SNat @k) knownSTK knownSTK
xscan
  :: forall k sh shm rn rm target.
     ( BaseTensor target, LetTensor target
     , KnownNat k, KnownSTK rn, KnownSTK rm, KnownShX sh, KnownShX shm )
  => (forall f.
      ADReady f => f (TKX2 sh rn) -> f (TKX2 shm rm) -> f (TKX2 sh rn))
  -> target (TKX2 sh rn)
  -> target (BuildTensorKind k (TKX2 shm rm))
  -> target (BuildTensorKind (1 + k) (TKX2 sh rn))
{-# INLINE xscan #-}
xscan = tscan (SNat @k) knownSTK knownSTK

-- | A strict right mapAccum.
tmapAccumR
  :: forall accShs bShs eShs k target. BaseTensor target
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
{-# INLINE tmapAccumR #-}  -- this doesn't want to specialize
tmapAccumR proxy !k !accShs !bShs !eShs f acc0 es =
  let xftk = FTKProduct accShs eShs
      fl :: forall f. ADReady f
         => f (TKProduct accShs eShs)
         -> f (TKProduct accShs bShs)
      fl !args = ttlet args $ \ !args1 ->
                   f (tproject1 args1) (tproject2 args1)
  in tmapAccumRDer proxy k accShs bShs eShs
                   (tlambda @target xftk (HFun fl))
                   (tfwd @target xftk $ HFun fl)
                   (trevDt @target xftk $ HFun fl)
                   acc0 es
-- | A strict left mapAccum.
tmapAccumL
  :: forall accShs bShs eShs k target. BaseTensor target
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
{-# INLINE tmapAccumL #-}  -- this doesn't want to specialize
tmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
  let xftk = FTKProduct accShs eShs
      fl :: forall f. ADReady f
         => f (TKProduct accShs eShs)
         -> f (TKProduct accShs bShs)
      fl !args = ttlet args $ \ !args1 ->
                   f (tproject1 args1) (tproject2 args1)
  in tmapAccumLDer proxy k accShs bShs eShs
                   (tlambda @target xftk (HFun fl))
                   (tfwd @target xftk $ HFun fl)
                   (trevDt @target xftk $ HFun fl)
                   acc0 es

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
rrev :: forall n x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKR2 n r))
     -> FullTensorKind x
     -> target x
     -> target (ADTensorKind x)
rrev f xftk =
  \ !es -> tApply (trev @target xftk (HFun f)) es
-- We can't get sh from anywhere, so this is not possible:
-- rrev f shs es = rrevDt f shs es (rreplicate0N sh 1)
rrevDt :: forall n x r target. BaseTensor target
       => (forall f. ADReady f => f x -> f (TKR2 n r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind (TKR2 n r))  -- ^ incoming cotangent (dt)
       -> target (ADTensorKind x)
rrevDt f xftk =
  \ !es !dt -> tApply (trevDt @target xftk $ HFun f) (tpair dt es)
rfwd :: forall n x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKR2 n r))
     -> FullTensorKind x
     -> target x
     -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
     -> target (ADTensorKind (TKR2 n r))
rfwd f xftk =
  \ !es !ds -> tApply (tfwd @target xftk $ HFun f) (tpair ds es)
srev :: forall sh x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKS2 sh r))
     -> FullTensorKind x
     -> target x
     -> target (ADTensorKind x)
srev f xftk =
  \ !es -> tApply (trev @target xftk (HFun f)) es
srevDt :: forall sh x r target. BaseTensor target
       => (forall f. ADReady f => f x -> f (TKS2 sh r))
       -> FullTensorKind x
       -> target x
       -> target (ADTensorKind (TKS2 sh r))  -- ^ incoming cotangent (dt)
       -> target (ADTensorKind x)
srevDt f xftk =
  \ !es !dt -> tApply (trevDt @target xftk $ HFun f) (tpair dt es)
sfwd :: forall sh x r target. BaseTensor target
     => (forall f. ADReady f => f x -> f (TKS2 sh r))
     -> FullTensorKind x
     -> target x
     -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
     -> target (ADTensorKind (TKS2 sh r))
sfwd f xftk =
  \ !es !ds -> tApply (tfwd @target xftk $ HFun f) (tpair ds es)

-- These take @target@ first, because they change the target.
rprimalPart :: BaseTensor target
            => target (TKR2 n x) -> PrimalOf target (TKR2 n x)
rprimalPart = tprimalPart
rdualPart :: (BaseTensor target, KnownNat n, KnownSTK x)
          => target (TKR2 n x) -> DualOf target (TKR2 n x)
rdualPart = tdualPart knownSTK
rfromPrimal :: (BaseTensor target, KnownNat n, KnownSTK x)
            => PrimalOf target (TKR2 n x) -> target (TKR2 n x)
rfromPrimal = tfromPrimal knownSTK
rfromDual :: BaseTensor target
          => DualOf target (TKR2 n x) -> target (TKR2 n x)
rfromDual = tfromDual
rScale :: forall target n r.
          ( BaseTensor target, KnownNat n, GoodScalar r
          , Num (target (TKR n r)), Num (PrimalOf target (TKR n r)) )
       => PrimalOf target (TKR n r) -> DualOf target (TKR n r)
       -> DualOf target (TKR n r)
rScale = tScale @target knownSTK

sprimalPart :: BaseTensor target
            => target (TKS2 sh x) -> PrimalOf target (TKS2 sh x)
sprimalPart = tprimalPart
sdualPart :: (BaseTensor target, KnownShS sh, KnownSTK x)
          => target (TKS2 sh x) -> DualOf target (TKS2 sh x)
sdualPart = tdualPart knownSTK
sfromPrimal :: (BaseTensor target, KnownShS sh, KnownSTK x)
            => PrimalOf target (TKS2 sh x) -> target (TKS2 sh x)
sfromPrimal = tfromPrimal knownSTK
sfromDual :: BaseTensor target
          => DualOf target (TKS2 sh x) -> target (TKS2 sh x)
sfromDual = tfromDual
sScale :: forall target sh r.
          ( BaseTensor target, KnownShS sh, GoodScalar r
          , Num (target (TKS sh r)), Num (PrimalOf target (TKS sh r)) )
       => PrimalOf target (TKS sh r) -> DualOf target (TKS sh r)
       -> DualOf target (TKS sh r)
sScale = tScale @target knownSTK

xprimalPart :: BaseTensor target
            => target (TKX2 sh x) -> PrimalOf target (TKX2 sh x)
xprimalPart = tprimalPart
xdualPart :: (BaseTensor target, KnownShX sh, KnownSTK x)
          => target (TKX2 sh x) -> DualOf target (TKX2 sh x)
xdualPart = tdualPart knownSTK
xfromPrimal :: (BaseTensor target, KnownShX sh, KnownSTK x)
            => PrimalOf target (TKX2 sh x) -> target (TKX2 sh x)
xfromPrimal = tfromPrimal knownSTK
xfromDual :: BaseTensor target
          => DualOf target (TKX2 sh x) -> target (TKX2 sh x)
xfromDual = tfromDual
xScale :: forall target sh r.
          ( BaseTensor target, KnownShX sh, GoodScalar r
          , Num (target (TKX sh r)), Num (PrimalOf target (TKX sh r)) )
       => PrimalOf target (TKX sh r) -> DualOf target (TKX sh r)
       -> DualOf target (TKX sh r)
xScale = tScale @target knownSTK

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
  ( BaseTensor target
  , ConvertTensor target
  , Boolean (BoolOf target)
  , CommonTargetEqOrd target
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

type CommonTargetEqOrd :: Target -> Constraint
class ( forall r. GoodScalar r => EqF target (TKScalar r)
      , forall r. GoodScalar r => OrdF target (TKScalar r)
      , forall r n. GoodScalar r => EqF target (TKR n r)
      , forall r n. GoodScalar r => OrdF target (TKR n r)
      , forall r sh. GoodScalar r => EqF target (TKS sh r)
      , forall r sh. GoodScalar r => OrdF target (TKS sh r)
      , forall r sh. GoodScalar r => EqF target (TKX sh r)
      , forall r sh. GoodScalar r => OrdF target (TKX sh r) )
      => CommonTargetEqOrd target where
instance
      ( forall r. GoodScalar r => EqF target (TKScalar r)
      , forall r. GoodScalar r => OrdF target (TKScalar r)
      , forall r n. GoodScalar r => EqF target (TKR n r)
      , forall r n. GoodScalar r => OrdF target (TKR n r)
      , forall r sh. GoodScalar r => EqF target (TKS sh r)
      , forall r sh. GoodScalar r => OrdF target (TKS sh r)
      , forall r sh. GoodScalar r => EqF target (TKX sh r)
      , forall r sh. GoodScalar r => OrdF target (TKX sh r) )
      => CommonTargetEqOrd target where
