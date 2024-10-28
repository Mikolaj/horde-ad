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
module HordeAd.Core.TensorClass
  ( -- * Re-exports
    IShR, ShapeS
    -- * The tensor classes
  , LetTensor(..), ShareTensor(..), RankedTensor(..), ShapedTensor(..)
  , HVectorTensor(..), ProductTensor(..)
  , HFun(..)
  , tunit, rfromD, sfromD, rscalar, rrepl, ringestData, ringestData1
  , ingestData, sscalar, srepl, xrepl, unrepShallow, unrepDeep, repDeepDuplicable
  , mapDynamic, mapDynamic2, mapRep
  , mapRep2Weak
    -- * The giga-constraint
  , ADReady, ADReadyNoLet, ADReadyS, ADReadyNoLetS
  ) where

import Prelude

import Data.Array.Internal (valueOf)
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (IsList (..))
import GHC.TypeLits
  (KnownNat, OrderingI (..), cmpNat, sameNat, type (+), type (-), type (<=))
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX)
import Data.Array.Nested (KnownShX (..), Rank, type (++))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList
  (Drop, IndexSh, IndexShX, Init, ShapeS, Take, pattern (:.$), pattern ZIS)
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * Ranked tensor class definition

type TensorSupports :: (Type -> Constraint) -> (Type -> Constraint) -> RankedTensorType -> Constraint
type TensorSupports c1 c2 f =
  forall r y. (GoodScalar r, KnownNat y)
              => c1 r => c2 (f r y)

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint) -> ShapedTensorType -> Constraint
type TensorSupportsS c1 c2 f =
  forall r y. (GoodScalar r, KnownShS y)
              => c1 r => c2 (f r y)

class (RealFloat r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloat r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class HVectorTensor ranked shaped
      => LetTensor (ranked :: RankedTensorType)
                   (shaped :: ShapedTensorType)
                   | ranked -> shaped, shaped -> ranked where
  rlet :: forall n m r r2. (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2)
       => ranked r n -> (ranked r n -> ranked r2 m)
       -> ranked r2 m
  rlet = blet @_ @_ @(TKR r n) @(TKR r2 m)
  rletHVectorIn :: forall n r. (KnownNat n, GoodScalar r)
                => HVectorOf ranked
                -> (HVector ranked -> ranked r n)
                -> ranked r n
  rletHVectorIn a f =
    tlet @_ @_ @TKUntyped @(TKR r n) (HVectorPseudoTensor a) f
  rletHFunIn :: (KnownNat n, GoodScalar r, TensorKind x, TensorKind z)
             => HFunOf ranked x z
             -> (HFunOf ranked x z -> ranked r n)
             -> ranked r n
  slet :: forall sh sh2 r r2.
          ( KnownShS sh, KnownShS sh2, GoodScalar r, GoodScalar r2
          , shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked )
       => shaped r sh -> (shaped r sh -> shaped r2 sh2)
       -> shaped r2 sh2
  slet = blet @_ @_ @(TKS r sh) @(TKS r2 sh2)
  sletHVectorIn :: forall sh r.
                   ( KnownShS sh, GoodScalar r
                   , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
                => HVectorOf (RankedOf shaped)
                -> (HVector (RankedOf shaped) -> shaped r sh)
                -> shaped r sh
  sletHVectorIn a f =
    tlet @_ @_ @TKUntyped @(TKS r sh) (HVectorPseudoTensor a) f
  sletHFunIn :: (KnownShS sh, GoodScalar r, TensorKind x, TensorKind z)
             => HFunOf (RankedOf shaped) x z
             -> (HFunOf (RankedOf shaped) x z -> shaped r sh)
             -> shaped r sh
  dletHVectorInHVector
    :: HVectorOf ranked
    -> (HVector ranked -> HVectorOf ranked)
    -> HVectorOf ranked
  dletHVectorInHVector a f =
    unHVectorPseudoTensor
    $ tlet @_ @_ @TKUntyped @TKUntyped (HVectorPseudoTensor a)
                                       (HVectorPseudoTensor . f)
  -- When the programmer uses the same closed function many times, the HFun
  -- makes it possible to prevent multiple simplification, inlining, etc.,
  -- once for each copy (shared on the Haskell heap) of the function
  -- representation. However, the engine code itself never uses closed
  -- functions in a way that would benefit from the HFun lets.
  --
  -- To prevent double derivative computation in
  -- > let f = ... in ... (dmapAccumR ... f ...) ... (dmapAccumR ... f ...)
  -- one needs to use dmapAccumRDer manually as in (simplified)
  -- > let f = ...; df = dfwd f; rf = drev f
  -- > in ... (dmapAccumRDer f df rf ...) ... (dmapAccumRDer f df rf ...)
  dletHFunInHVector
    :: (TensorKind x, TensorKind z)
    => HFunOf ranked x z
    -> (HFunOf ranked x z -> HVectorOf ranked)
    -> HVectorOf ranked
  dlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep ranked x
       -> (RepDeep ranked x -> Rep ranked z)
       -> Rep ranked z
  -- This type signature generalizes dletHVectorInHVector and is easier
  -- for the user to work with, giving him access to concrete vectors and tuples.
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep ranked x
       -> (RepShallow ranked x -> Rep ranked z)
       -> Rep ranked z
  blet :: forall x z. (TensorKind x, TensorKind z)
       => Rep ranked x
       -> (Rep ranked x -> Rep ranked z)
       -> Rep ranked z
  treplicate :: ( RankedTensor ranked, ShapedTensor shaped, ProductTensor ranked
                , shaped ~ ShapedOf ranked, RankedOf shaped ~ ranked )
             => SNat k -> STensorKindType z
             -> Rep ranked z
             -> Rep ranked (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar _ -> rreplicate (sNatValue snat) $ unRepScalar u
    STKR STKScalar{} SNat -> rreplicate (sNatValue snat) u
    STKS STKScalar{} sh -> withKnownShS sh $ sreplicate u
    STKX STKScalar{} sh -> withKnownShX sh $ xreplicate u
    STKProduct @z1 @z2 stk1 stk2
      | Dict <- lemTensorKindOfS stk1
      , Dict <- lemTensorKindOfS stk2
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z1)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z2) ->
        tlet u $ \ (!u1, !u2) ->
          tpair (treplicate snat stk1 u1) (treplicate snat  stk2 u2)
    STKUntyped ->
      tlet u $ \ !hv ->
        HVectorPseudoTensor $ dmkHVector
        $ replicate1HVectorF rreplicate sreplicate snat hv
    _ -> error "TODO"

  toShare :: TensorKind y
          => Rep ranked y
          -> Rep (ShareOf ranked) y
  tunshare :: TensorKind y
           => Rep (ShareOf ranked) y
           -> Rep ranked y
  tunshare = error "tunshare: this instance should never be used"
  tconstant :: STensorKindType y
            -> Rep (PrimalOf ranked) y
            -> Rep ranked y
  taddLet :: STensorKindType y -> Rep ranked y -> Rep ranked y -> Rep ranked y

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
  -- so it's awkward to put the methods into @RankedTensor@,
  -- which shouldn't know about lets, etc.
  rrev :: forall x r n.
          ( TensorKind x, GoodScalar r, KnownNat n
          , ProductTensor ranked, shaped ~ ShapedOf ranked )
       => (forall f. ADReady f => RepDeep f x -> f r n)
       -> TensorKindFull x
       -> RepDeep ranked x
       -> Rep ranked (ADTensorKind x)
  rrev f ftk | Dict <- lemTensorKindOfAD (stensorKind @x) =
    let g :: forall f. ADReady f => Rep f x -> Rep f (TKR r n)
        g !x = dlet x $ \ !xDeep -> f xDeep
    in \ !es -> dHApply (drev @ranked ftk $ HFun g) (unrepDeep es)
  -- We can't get sh from anywhere, so this is not possible:
  -- rrev f shs es = rrevDt f shs es (rreplicate0N sh 1)
  rrevDt :: forall x r n.
            ( TensorKind x, GoodScalar r, KnownNat n
            , ProductTensor ranked, shaped ~ ShapedOf ranked )
         => (forall f. ADReady f => RepDeep f x -> f r n)
         -> TensorKindFull x
         -> RepDeep ranked x
         -> Rep ranked (ADTensorKind (TKR r n))  -- ^ incoming cotangent (dt)
         -> Rep ranked (ADTensorKind x)
  rrevDt f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
               , Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    let g :: forall f. ADReady f => Rep f x -> Rep f (TKR r n)
        g !x = dlet x $ \ !xDeep -> f xDeep
    in \ !es !dt -> dHApply (drevDt @ranked ftk $ HFun g)
                            (tpair dt (unrepDeep es))
  rfwd :: forall x r n.
          ( TensorKind x, GoodScalar r, KnownNat n
          , ProductTensor ranked, shaped ~ ShapedOf ranked )
       => (forall f. ADReady f => RepDeep f x -> f r n)
       -> TensorKindFull x
       -> RepDeep ranked x
       -> RepDeep ranked (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> Rep ranked (ADTensorKind (TKR r n))
  rfwd f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
             , Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    let g :: forall f. ADReady f => Rep f x -> Rep f (TKR r n)
        g !x = dlet x $ \ !xDeep -> f xDeep
    in \ !es !ds -> dHApply (dfwd @ranked ftk $ HFun g)
                            (tpair (unrepDeep ds) (unrepDeep es))
  srev :: forall x r sh.
          ( TensorKind x, GoodScalar r, KnownShS sh, ProductTensor ranked
          , ShapedTensor shaped, shaped ~ ShapedOf ranked
          , ADTensorKind (TKS r sh) ~ TKS r sh )
       => (forall f. ADReadyS f => RepDeep (RankedOf f) x -> f r sh)
       -> TensorKindFull x
       -> RepDeep ranked x
       -> Rep ranked (ADTensorKind x)
  srev f ftk es = srevDt f ftk es (srepl 1)
  srevDt :: forall x r sh.
            ( TensorKind x, GoodScalar r, KnownShS sh
            , ProductTensor ranked, shaped ~ ShapedOf ranked )
         => (forall f. ADReadyS f => RepDeep (RankedOf f) x -> f r sh)
         -> TensorKindFull x
         -> RepDeep ranked x
         -> Rep ranked (ADTensorKind (TKS r sh))  -- ^ incoming cotangent (dt)
         -> Rep ranked (ADTensorKind x)
  srevDt f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
               , Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    let g :: forall f. ADReady f => Rep f x -> Rep f (TKS r sh)
        g !x = dlet x $ \ !xDeep -> f xDeep
    in \ !es !dt -> dHApply (drevDt @ranked ftk $ HFun g)
                            (tpair dt (unrepDeep es))
  sfwd :: forall x r sh.
          ( TensorKind x, GoodScalar r, KnownShS sh
          , ProductTensor ranked, shaped ~ ShapedOf ranked )
       => (forall f. ADReadyS f => RepDeep (RankedOf f) x -> f r sh)
       -> TensorKindFull x
       -> RepDeep ranked x
       -> RepDeep ranked (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> Rep ranked (ADTensorKind (TKS r sh))
  sfwd f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
             , Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    let g :: forall f. ADReady f => Rep f x -> Rep f (TKS r sh)
        g !x = dlet x $ \ !xDeep -> f xDeep
    in \ !es !ds -> dHApply (dfwd @ranked ftk $ HFun g)
                            (tpair (unrepDeep ds) (unrepDeep es))

class ShareTensor (ranked :: RankedTensorType) where
  tshare :: forall y. (TensorKind y, ProductTensor ranked)
         => Rep ranked y -> Rep ranked y
  tunpair :: (TensorKind x, TensorKind z)
          => Rep ranked (TKProduct x z)
          -> RepShallow ranked (TKProduct x z)
  tunvector :: Rep ranked TKUntyped
            -> RepShallow ranked TKUntyped
  taddShare :: STensorKindType y -> Rep ranked y -> Rep ranked y
            -> Rep ranked y

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Num (IntOf ranked), Num (IntOf (MixedOf ranked))
      , IntegralF (IntOf ranked), IntegralF (IntOf (MixedOf ranked))
      , CRanked ranked Num, CMixed (MixedOf ranked) Num
      , TensorSupports RealFloatAndFloatElt Floating ranked
      , TensorSupports RealFloatAndFloatElt RealFloatF ranked
      , TensorSupports Integral IntegralF ranked
      , CMixedSupports RealFloatAndFloatElt Floating (MixedOf ranked)
      , CMixedSupports RealFloatAndFloatElt RealFloatF (MixedOf ranked)
      , CMixedSupports Integral IntegralF (MixedOf ranked) )
      => RankedTensor (ranked :: RankedTensorType) where

  -- Integer codomain
  rshape :: (GoodScalar r, KnownNat n) => ranked r n -> IShR n
  rrank :: forall r n. (GoodScalar r, KnownNat n) => ranked r n -> Int
  rrank _ = valueOf @n
  rsize :: (GoodScalar r, KnownNat n) => ranked r n -> Int
  rsize = sizeShape . rshape
  rlength :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> Int
  rlength v = case rshape v of
    ZSR -> error "rlength: impossible pattern needlessly required"
    k :$: _ -> k
  rminIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  rmaxIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  rfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => ranked r n -> ranked r2 n
  riota :: GoodScalar r => ranked r 1  -- 0, 1 .. infinity
  riota = undefined  -- infinite, hence diverges; don't override

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- may indicate the rank of the codomain, if bounded.

  -- First index is for outermost dimension; empty index means identity,
  -- index ouf of bounds produces zero (but beware of vectorization).
  rindex, (!) :: (GoodScalar r, KnownNat m, KnownNat n)
              => ranked r (m + n) -> IndexOf ranked m -> ranked r n
  infixl 9 !
  (!) = rindex  -- prefix form better when type applications are necessary
  rindex0 :: (GoodScalar r, KnownNat m)
          => ranked r m -> IndexOf ranked m -> ranked r 0
  rindex0 = rindex
  rsum :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r n
  rsum0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 0
  rsum0 = rsum . rflatten
  rdot0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r n -> ranked r 0
  rdot0 t u = rsum (rflatten (t * u))
  rmatvecmul :: GoodScalar r => ranked r 2 -> ranked r 1 -> ranked r 1
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
  rmatvecmul m v = rbuild1 (rlength m) (\i -> rdot0 v (m ! [i]))
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  rmatmul2 :: (GoodScalar r, Numeric r)
           => ranked r 2 -> ranked r 2 -> ranked r 2
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
-- rmatmul2 m1 m2 = rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR -> rsum (rtranspose [2,1,0] (rreplicate width2 m1)
                                  * rtranspose [1,0] (rreplicate (rlength m1) m2))
    _ -> error "rmatmul2: impossible pattern needlessly required"
  rscatter :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> ranked r (m + n)
           -> (IndexOf ranked m -> IndexOf ranked p)
           -> ranked r (p + n)
  rscatter1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
            => IShR (p + n) -> ranked r (1 + n)
            -> (IntOf ranked -> IndexOf ranked p)
            -> ranked r (p + n)
  rscatter1 sh v f = rscatter @ranked @r @1 sh v
                              (\(i :.: ZIR) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  rfromList :: (GoodScalar r, KnownNat n)
            => NonEmpty (ranked r n) -> ranked r (1 + n)
  rfromList = rfromVector . V.fromList . NonEmpty.toList
    -- going through strict vectors, because laziness is risky with impurity
  rfromList0N :: (GoodScalar r, KnownNat n)
              => IShR n -> [ranked r 0] -> ranked r n
  rfromList0N sh = rfromVector0N sh . V.fromList
  -- This is morally non-empty strict vectors:
  rfromVector :: (GoodScalar r, KnownNat n)
              => Data.Vector.Vector (ranked r n) -> ranked r (1 + n)
  rfromVector0N :: (GoodScalar r, KnownNat n)
                => IShR n -> Data.Vector.Vector (ranked r 0) -> ranked r n
  rfromVector0N sh = rreshape sh . rfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'rlet'.
  runravelToList :: forall r n. (GoodScalar r, KnownNat n)
                 => ranked r (1 + n) -> [ranked r n]
  runravelToList t =
    let f :: Int -> ranked r n
        f i = rindex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate :: (GoodScalar r, KnownNat n)
             => Int -> ranked r n -> ranked r (1 + n)
  rreplicate0N :: (GoodScalar r, KnownNat n)
               => IShR n -> ranked r 0 -> ranked r n
  rreplicate0N sh = rreshape sh . rreplicate (sizeShape sh)
  rappend :: (GoodScalar r, KnownNat n)
          => ranked r (1 + n) -> ranked r (1 + n) -> ranked r (1 + n)
  rconcat :: (GoodScalar r, KnownNat n)
          => [ranked r (1 + n)] -> ranked r (1 + n)
  rconcat = foldr1 rappend
  rslice :: (GoodScalar r, KnownNat n)
         => Int -> Int -> ranked r (1 + n) -> ranked r (1 + n)
  runcons :: (GoodScalar r, KnownNat n)
          => ranked r (1 + n) -> Maybe (ranked r n, ranked r (1 + n))
  runcons v = case rshape v of
                ZSR -> Nothing
                len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
  rreverse :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r (1 + n)
  rtr :: (GoodScalar r, KnownNat n) => ranked r (2 + n) -> ranked r (2 + n)
  rtr = rtranspose [1, 0]
  rtranspose :: (GoodScalar r, KnownNat n)
             => Permutation.PermR -> ranked r n -> ranked r n
  rflatten :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 1
  rflatten u = rreshape (flattenShape $ rshape u) u
  rreshape :: (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> ranked r n -> ranked r m
  rbuild :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
         => IShR (m + n) -> (IndexOf ranked m -> ranked r n)
         -> ranked r (m + n)
  rbuild sh0 f0 =
    let buildSh :: IShR m1 -> (IndexOf ranked m1 -> ranked r n)
                -> ranked r (m1 + n)
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | Dict <- knownShR sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in rbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  rbuild1 :: (GoodScalar r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf ranked -> ranked r n) -> ranked r (1 + n)
  rmap :: (GoodScalar r, GoodScalar r2, KnownNat m, KnownNat n)
       => (ranked r n -> ranked r2 n)
       -> ranked r (m + n) -> ranked r2 (m + n)
  rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
  rmap1 :: (GoodScalar r, GoodScalar r2, KnownNat n)
        => (ranked r n -> ranked r2 n)
        -> ranked r (1 + n) -> ranked r2 (1 + n)
  rmap1 f u = rbuild1 (rlength u) (\i -> f (u ! [i]))
  rmap0N :: (GoodScalar r, GoodScalar r1, KnownNat n)
         => (ranked r1 0 -> ranked r 0) -> ranked r1 n -> ranked r n
  rmap0N f v = rbuild (rshape v) (f . rindex0 v)
  rzipWith :: ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n )
           => IShR (m + n)
           -> (ranked r1 n1 -> ranked r2 n2 -> ranked r n)
           -> ranked r1 (m + n1) -> ranked r2 (m + n2) -> ranked r (m + n)
  rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
  rzipWith1 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n1, KnownNat n2, KnownNat n )
            => (ranked r1 n1 -> ranked r2 n2 -> ranked r n)
            -> ranked r1 (1 + n1) -> ranked r2 (1 + n2) -> ranked r (1 + n)
  rzipWith1 f u v = rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]))
  rzipWith0N :: (GoodScalar r1, GoodScalar r2, GoodScalar r, KnownNat n)
             => (ranked r1 0 -> ranked r2 0 -> ranked r 0)
             -> ranked r1 n -> ranked r2 n -> ranked r n
  rzipWith0N f u v = rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))
  rzipWith3 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
               , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
            => IShR (m + n)
            -> (ranked r1 n1 -> ranked r2 n2 -> ranked r3 n3 -> ranked r n)
            -> ranked r1 (m + n1) -> ranked r2 (m + n2) -> ranked r3 (m + n3)
            -> ranked r (m + n)
  rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
  rzipWith31 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
             => (ranked r1 n1 -> ranked r2 n2 -> ranked r3 n3 -> ranked r n)
             -> ranked r1 (1 + n1) -> ranked r2 (1 + n2) -> ranked r3 (1 + n3)
             -> ranked r (1 + n)
  rzipWith31 f u v w =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
  rzipWith30N :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , KnownNat n )
              => (ranked r1 0 -> ranked r2 0 -> ranked r3 0 -> ranked r 0)
              -> ranked r1 n -> ranked r2 n -> ranked r3 n -> ranked r n
  rzipWith30N f u v w =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
  rzipWith4 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
               , GoodScalar r, KnownNat m
               , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
               , KnownNat n )
            => IShR (m + n)
            -> (ranked r1 n1 -> ranked r2 n2 -> ranked r3 n3 -> ranked r4 n4
                -> ranked r n)
            -> ranked r1 (m + n1) -> ranked r2 (m + n2) -> ranked r3 (m + n3)
            -> ranked r4 (m + n4)
            -> ranked r (m + n)
  rzipWith4 sh f u v w x =
    rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
  rzipWith41 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                , GoodScalar r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
                , KnownNat n )
             => (ranked r1 n1 -> ranked r2 n2 -> ranked r3 n3 -> ranked r4 n4
                 -> ranked r n)
             -> ranked r1 (1 + n1) -> ranked r2 (1 + n2) -> ranked r3 (1 + n3)
             -> ranked r4 (1 + n4)
             -> ranked r (1 + n)
  rzipWith41 f u v w x =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
  rzipWith40N :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r
                 , KnownNat n )
              => (ranked r1 0 -> ranked r2 0 -> ranked r3 0 -> ranked r4 0
                  -> ranked r 0)
              -> ranked r1 n -> ranked r2 n -> ranked r3 n -> ranked r4 n
              -> ranked r n
  rzipWith40N f u v w x =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                                (rindex0 x ix))
  rgather :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
          => IShR (m + n) -> ranked r (p + n)
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> ranked r (m + n)
  rgather1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
           => Int -> ranked r (p + n)
           -> (IntOf ranked -> IndexOf ranked p)
           -> ranked r (1 + n)
  rgather1 k v f = rgather @ranked @r @1
                           (k :$: dropShape (rshape v)) v
                           (\(i :.: ZIR) -> f i)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => ranked r1 n -> ranked r2 n
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => ranked r1 n -> ranked r2 n
  rconst :: (GoodScalar r, KnownNat n) => Nested.Ranked n r -> ranked r n
  rfromS :: (GoodScalar r, KnownShS sh)
         => ShapedOf ranked r sh -> ranked r (Rank sh)
  -- Prevents wrong shape in @0@ with ranked (but not shaped) tensors
  -- at any rank greater than zero.
  rzero :: (GoodScalar r, KnownNat n)
        => IShR n -> ranked r n
  rzero sh = rreplicate0N sh 0

  -- ** No serviceable parts beyond this point ** --

  rscaleByScalar :: (GoodScalar r, KnownNat n)
                 => ranked r 0 -> ranked r n -> ranked r n
  rscaleByScalar s v = v * rreplicate0N (rshape v) s
  rdot1In :: GoodScalar r
          => ranked r 2 -> ranked r 2
          -> ranked r 1  -- TODO: generalize
  rdot1In t u = rsum $ rtr (t * u)

  -- Primal/dual things.
  rconstant :: (GoodScalar r, KnownNat n) => PrimalOf ranked r n -> ranked r n
  rprimalPart :: (GoodScalar r, KnownNat n)
              => ranked r n -> PrimalOf ranked r n
  rdualPart :: (GoodScalar r, KnownNat n)
            => ranked r n -> DualOf ranked r n
  rD :: (GoodScalar r, KnownNat n)
     => PrimalOf ranked r n -> DualOf ranked r n -> ranked r n
  rScale :: (GoodScalar r, KnownNat n)
         => PrimalOf ranked r n -> DualOf ranked r n -> DualOf ranked r n
  -- TODO: we'd probably also need dZero, dIndex0 and others from IsPrimal,
  -- because IsPrimal has subtly different types, operating on Deltas (Dual)
  -- instead of on terms (DualOf) that denote Deltas
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  xshape :: (GoodScalar r, KnownShX sh) => MixedOf ranked r sh -> IShX sh
  xindex :: forall r sh1 sh2.
            ( GoodScalar r, KnownShX sh1, KnownShX sh2
            , KnownShX (sh1 ++ sh2) )
         => MixedOf ranked r (sh1 ++ sh2) -> IndexShX (MixedOf ranked) sh1
         -> MixedOf ranked r sh2
  xfromVector :: (GoodScalar r, KnownNat n, KnownShX sh)
              => Data.Vector.Vector (MixedOf ranked r sh)
              -> MixedOf ranked r (Just n ': sh)
  xreplicate :: (KnownNat n, KnownShX sh, GoodScalar r)
             => MixedOf ranked r sh -> MixedOf ranked r (Just n ': sh)
  xconst :: (GoodScalar r, KnownShX sh)
         => Nested.Mixed sh r -> MixedOf ranked r sh
  xzero :: forall r sh.
           (GoodScalar r, KnownShX sh, RankedOf (MixedOf ranked) ~ ranked)
        => IShX sh -> MixedOf ranked r sh
  xzero sh = xrepl sh 0
  xconstant :: (GoodScalar r, KnownShX sh)
            => PrimalOf (MixedOf ranked) r sh -> MixedOf ranked r sh
  xprimalPart :: (GoodScalar r, KnownShX sh)
              => MixedOf ranked r sh -> PrimalOf (MixedOf ranked) r sh
  xdualPart :: (GoodScalar r, KnownShX sh)
            => MixedOf ranked r sh -> DualOf (MixedOf ranked) r sh
  xD :: (GoodScalar r, KnownShX sh)
     => PrimalOf (MixedOf ranked) r sh -> DualOf (MixedOf ranked) r sh
     -> MixedOf ranked r sh


-- * Shaped tensor class definition

class ( Num (IntOf shaped), IntegralF (IntOf shaped), CShaped shaped Num
      , TensorSupportsS RealFloatAndFloatElt Floating shaped
      , TensorSupportsS RealFloatAndFloatElt RealFloatF shaped
      , TensorSupportsS Integral IntegralF shaped
      , shaped ~ ShapedOf (RankedOf shaped) )
      => ShapedTensor (shaped :: ShapedTensorType) where

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, KnownShS sh)
         => shaped r sh -> ShS sh
  sshape _ = knownShS @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (Rank sh))
        => shaped r sh -> Int
  srank _ = valueOf @(Rank sh)
  ssize :: forall sh r. (GoodScalar r, KnownShS sh) => shaped r sh -> Int
  ssize _ = sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => shaped r (n ': sh) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Init (n ': sh))
  smaxIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Init (n ': sh))
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShS sh)
         => shaped r sh -> shaped r2 sh
    -- the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => shaped r '[n]  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( GoodScalar r, KnownShS sh1, KnownShS sh2
                  , KnownShS (sh1 ++ sh2) )
               => shaped r (sh1 ++ sh2) -> IndexSh shaped sh1
               -> shaped r sh2
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, KnownShS sh1)
          => shaped r sh1 -> IndexSh shaped sh1
          -> shaped r '[]
  sindex0 = gcastWith (unsafeCoerce Refl :: sh1 ++ '[] :~: sh1)
              sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
       => shaped r (n ': sh) -> shaped r sh
  ssum0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => shaped r sh -> shaped r '[]
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => shaped r sh -> shaped r sh -> shaped r '[]
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (i :.$ ZIS)))
  smatmul2 :: forall r n m p.
              (GoodScalar r, Numeric r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Permutation.makePerm @'[2, 1, 0]) (sreplicate @shaped @p m1)
          * stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @shaped @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh)
       , KnownShS (sh2 ++ Drop p sh) )
    => shaped r (sh2 ++ Drop p sh)
    -> (IndexSh shaped sh2 -> IndexSh shaped (Take p sh))
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh) )
    => shaped r (n2 ': Drop p sh)
    -> (IntOf shaped -> IndexSh shaped (Take p sh))
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (\(i :.$ _) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (GoodScalar r, KnownNat n, KnownShS sh)
            => NonEmpty (shaped r sh) -> shaped r (n ': sh)
  sfromList = sfromVector . V.fromList . NonEmpty.toList
  sfromList0N :: forall r sh.
                 (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
              => [shaped r '[]] -> shaped r sh
  sfromList0N = sfromVector0N . V.fromList
  -- This is morally non-empty strict vectors:
  sfromVector :: (GoodScalar r, KnownNat n, KnownShS sh)
              => Data.Vector.Vector (shaped r sh) -> shaped r (n ': sh)
  sfromVector0N :: forall r sh.
                   (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
                => Data.Vector.Vector (shaped r '[])
                -> shaped r sh
  sfromVector0N = sreshape @shaped @r @'[Nested.Product sh] @sh . sfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'slet'.
  sunravelToList :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
                 => shaped r (n ': sh) -> [shaped r sh]
  sunravelToList t =
    let f :: Int -> shaped r sh
        f i = sindex t (ShapedList.singletonIndex $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate :: (KnownNat n, KnownShS sh, GoodScalar r)
             => shaped r sh -> shaped r (n ': sh)
  sreplicate0N :: forall r sh.
                  (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
               => shaped r '[] -> shaped r sh
  sreplicate0N = sreshape @shaped @r @'[Nested.Product sh] @sh
                 . sreplicate @shaped @(Nested.Product sh)
  sappend :: (GoodScalar r, KnownNat m, KnownNat n, KnownShS sh)
          => shaped r (m ': sh) -> shaped r (n ': sh)
          -> shaped r ((m + n) ': sh)
  sslice :: (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Proxy i -> Proxy n
         -> shaped r (i + n + k ': sh) -> shaped r (n ': sh)
  suncons :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => shaped r (n ': sh) -> Maybe (shaped r sh, shaped r (n - 1 ': sh))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (GoodScalar r, KnownNat n, KnownShS sh)
           => shaped r (n ': sh) -> shaped r (n ': sh)
  str :: ( GoodScalar r, KnownNat n, KnownNat m, KnownShS sh
         , KnownNat (Rank sh) )
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose (Permutation.makePerm @'[1, 0])
  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , Rank perm <= Rank sh, GoodScalar r )
             => Permutation.Perm perm -> shaped r sh
             -> shaped r (Permutation.PermutePrefix perm sh)
  sflatten :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
           => shaped r sh -> shaped r '[Nested.Product sh]
  sflatten = sreshape
  sreshape :: ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2 )
           => shaped r sh -> shaped r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh. (GoodScalar r, KnownShS sh, KnownShS (Take m sh))
         => (IndexSh shaped (Take m sh) -> shaped r (Drop m sh))
         -> shaped r sh
  sbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IndexSh shaped sh1 -> shaped r (Drop m sh))
          -> shaped r (sh1 ++ Drop m sh)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          ((:$$) SNat sh2, (:$$) _ sh2m) | Dict <- sshapeKnown sh2m ->
            let g i = buildSh sh2 sh2m (f . (i :.$))
            in sbuild1 g
    in gcastWith (unsafeCoerce Refl
                  :: sh :~: Take m sh ++ Drop m sh)
       $ buildSh (knownShS @(Take m sh))
                 (knownShS @sh)
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf shaped -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: forall r r2 m sh.
          ( GoodScalar r, GoodScalar r2, KnownNat m
          , KnownShS sh, KnownShS (Take m sh), KnownShS (Drop m sh) )
       => (shaped r (Drop m sh) -> shaped r2 (Drop m sh))
       -> shaped r sh -> shaped r2 sh
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: Take m sh ++ Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r r2 sh n.
           (GoodScalar r, GoodScalar r2, KnownNat n, KnownShS sh)
        => (shaped r sh -> shaped r2 sh)
        -> shaped r (n ': sh) -> shaped r2 (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
  smap0N :: forall r1 r sh.
            (GoodScalar r1, GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => (shaped r1 '[] -> shaped r '[]) -> shaped r1 sh -> shaped r sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @shaped @r @(Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownShS sh1, KnownShS sh2, KnownShS sh
              , KnownShS (Take m sh), KnownShS (Drop m sh1)
              , KnownShS (Drop m sh2), KnownShS (Drop m sh)
              , sh1 ~ Take m sh ++ Drop m sh1
              , sh2 ~ Take m sh ++ Drop m sh2 )
           => (shaped r1 (Drop m sh1)
               -> shaped r2 (Drop m sh2)
               -> shaped r (Drop m sh))
           -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh )
            => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh)
            -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
            -> shaped r (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                     (v !$ (i :.$ ZIS)))
  szipWith0N :: forall r1 r2 r sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r
                , KnownShS sh, KnownNat (Rank sh) )
             => (shaped r1 '[] -> shaped r2 '[] -> shaped r '[])
             -> shaped r1 sh -> shaped r2 sh -> shaped r sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  szipWith3 :: forall r1 r2 r3 r m sh1 sh2 sh3 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
               , KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3 )
            => (shaped r1 (Drop m sh1)
                -> shaped r2 (Drop m sh2)
                -> shaped r3 (Drop m sh3)
                -> shaped r (Drop m sh))
            -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3 -> shaped r sh
  szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
  szipWith31 :: forall r1 r2 r3 r n sh1 sh2 sh3 sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                , KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh )
             => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3 -> shaped r sh)
             -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
             -> shaped r3 (n ': sh3)
             -> shaped r (n ': sh)
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS)))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , KnownShS sh, KnownNat (Rank sh) )
              => (shaped r1 '[] -> shaped r2 '[] -> shaped r3 '[]
                  -> shaped r '[])
              -> shaped r1 sh -> shaped r2 sh -> shaped r3 sh -> shaped r sh
  szipWith30N f u v w =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix))
  szipWith4 :: forall r1 r2 r3 r4 r m sh1 sh2 sh3 sh4 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
               , GoodScalar r, KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
               , KnownShS sh
               , KnownShS (Take m sh), KnownShS (Drop m sh1)
               , KnownShS (Drop m sh2), KnownShS (Drop m sh3)
               , KnownShS (Drop m sh4), KnownShS (Drop m sh)
               , sh1 ~ Take m sh ++ Drop m sh1
               , sh2 ~ Take m sh ++ Drop m sh2
               , sh3 ~ Take m sh ++ Drop m sh3
               , sh4 ~ Take m sh ++ Drop m sh4 )
            => (shaped r1 (Drop m sh1)
                -> shaped r2 (Drop m sh2)
                -> shaped r3 (Drop m sh3)
                -> shaped r4 (Drop m sh4)
                -> shaped r (Drop m sh))
            -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3 -> shaped r4 sh4
            -> shaped r sh
  szipWith4 f u v w x =
    sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
  szipWith41 :: forall r1 r2 r3 r4 r n sh1 sh2 sh3 sh4 sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                , GoodScalar r, KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
                , KnownShS sh )
             => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3
                 -> shaped r4 sh4 -> shaped r sh)
             -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
             -> shaped r3 (n ': sh3) -> shaped r4 (n ': sh4)
             -> shaped r (n ': sh)
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                          (v !$ (i :.$ ZIS))
                                          (w !$ (i :.$ ZIS))
                                          (x !$ (i :.$ ZIS)))
  szipWith40N :: forall r1 r2 r3 r4 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r, KnownShS sh, KnownNat (Rank sh) )
              => (shaped r1 '[] -> shaped r2 '[] -> shaped r3 '[]
                  -> shaped r4 '[] -> shaped r '[])
              -> shaped r1 sh -> shaped r2 sh -> shaped r3 sh -> shaped r4 sh
              -> shaped r sh
  szipWith40N f u v w x =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix)
                                                (sindex0 x ix))
  sgather
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh)
       , KnownShS (sh2 ++ Drop p sh) )
    => shaped r sh
    -> (IndexSh shaped sh2 -> IndexSh shaped (Take p sh))
    -> shaped r (sh2 ++ Drop p sh)
  sgather1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh) )
    => shaped r sh
    -> (IntOf shaped -> IndexSh shaped (Take p sh))
    -> shaped r (n2 ': Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (\(i :.$ _) -> f i)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownShS sh)
        => shaped r1 sh -> shaped r2 sh
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                => shaped r1 sh -> shaped r2 sh
  sconst :: (GoodScalar r, KnownShS sh) => Nested.Shaped sh r -> shaped r sh
  sfromR :: (GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => RankedOf shaped r (Rank sh) -> shaped r sh

  -- ** No serviceable parts beyond this point ** --

  sscaleByScalar
    :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v * sreplicate0N s
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => Proxy m
          -> shaped r '[n, m] -> shaped r '[n, m]
          -> shaped r '[n]  -- TODO: generalize
  sdot1In _ t u = ssum $ str (t * u)

  -- Primal/dual things.
  sconstant :: (GoodScalar r, KnownShS sh)
            => PrimalOf shaped r sh -> shaped r sh
  sprimalPart :: (GoodScalar r, KnownShS sh)
              => shaped r sh -> PrimalOf shaped r sh
  sdualPart :: (GoodScalar r, KnownShS sh)
            => shaped r sh -> DualOf shaped r sh
  sD :: (GoodScalar r, KnownShS sh)
     => PrimalOf shaped r sh -> DualOf shaped r sh -> shaped r sh
  sScale :: (GoodScalar r, KnownShS sh)
         => PrimalOf shaped r sh -> DualOf shaped r sh -> DualOf shaped r sh


-- * HVectorTensor class definition

-- This particular fundep really helps with type reconstruction in user code,
-- e.g., in the shaped nested folds tests.
class HVectorTensor (ranked :: RankedTensorType)
                    (shaped :: ShapedTensorType)
                    | ranked -> shaped, shaped -> ranked where
  dshape :: HVectorOf ranked -> VoidHVector
  tshapeFull :: STensorKindType y -> Rep ranked y
             -> TensorKindFull y
  tcond :: IfF ranked
        => STensorKindType y
        -> BoolOf ranked
        -> Rep ranked y -> Rep ranked y
        -> Rep ranked y
  tprimalPart :: STensorKindType y
              -> Rep ranked y
              -> Rep (PrimalOf ranked) y
  tdualPart :: STensorKindType y
            -> Rep ranked y
            -> Rep (DualOf ranked) y
  dmkHVector :: HVector ranked -> HVectorOf ranked
  dlambda :: (TensorKind x, TensorKind z)
          => TensorKindFull x -> HFun x z -> HFunOf ranked x z
  dHApply :: (TensorKind x, TensorKind z)
          => HFunOf ranked x z -> Rep ranked x
          -> Rep ranked z
  dunHVector :: HVectorOf ranked -> HVector ranked
    -- ^ Warning: this operation easily breaks sharing.
    -- The operation can't usually be implemented to preserve
    -- sharing, because it's type signature doesn't fit the let
    -- and share operations available.
  dbuild1 :: SNat k
          -> (IntOf ranked -> HVectorOf ranked)  -- sh_i
          -> HVectorOf ranked  -- k ': sh_i
  dzipWith1 :: SNat k
            -> ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
               , RankedOf (PrimalOf (ShapedOf ranked))
                 ~ RankedOf (PrimalOf ranked) )
            => (HVector ranked -> HVectorOf ranked)
                 -- ^ both hVectors can have arbitrary tensors in them
            -> HVector ranked -> HVectorOf ranked
                 -- ^ each hVector has the same tensor shapes and scalar types
                 -- as its corresponding hVector above, except for the extra
                 -- outermost dimension k
  dzipWith1 k f u =
    dbuild1 @ranked k (f . index1HVectorF rshape sshape rindex sindex u)
  -- If the result of the argument function is not a scalar,
  -- the result of this operation is the gradient of a function that additionally
  -- sums all elements of the result. If all elements are equally important
  -- for optimization, this may be exactly what is needed for gradient descent,
  -- unless there are floats of different resolution among the elements and,
  -- e.g., one wants to compensate for that.
  --
  -- These methods (and dlambda) producing HFunOf is analogous to dmkHVector
  -- producing HVectorOf and it's exactly what is needed as arguments
  -- of dmapAccumRDer
  drev
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf ranked x (ADTensorKind x)  -- a |-> da
  drevDt
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf ranked (TKProduct (ADTensorKind z) x) (ADTensorKind x)
                 -- [db, a] |-> da
  dfwd
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf ranked (TKProduct (ADTensorKind x) x) (ADTensorKind z)
                 -- [da, a] |-> db
  -- | A strict left fold.
  rfold
    :: forall rn rm n m.
       ( GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m
       , RankedTensor ranked, ProductTensor ranked )
    => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
    -> ranked rn n  -- ^ initial value
    -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
    -> ranked rn n
  rfold f acc0 es =
    let shm :: IShR m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rfold: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      tproject1
        (dmapAccumL (Proxy @ranked)
           snat
           (FTKR @rn sh)
           (FTKUntyped V.empty)
           (FTKR @rm shm)
           (let g :: forall f. ADReady f
                  => Rep f (TKR rn n) -> Rep f (TKR rm m)
                  -> Rep f (TKProduct (TKR rn n) TKUntyped)
                g !acc !e =
                  tpair (f acc e)
                         (HVectorPseudoTensor $ dmkHVector V.empty)
            in g)
           acc0
           es)
  -- | A strict left scan.
  rscan
    :: forall rn rm n m.
       ( GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m
       , RankedTensor ranked, LetTensor ranked shaped, ProductTensor ranked  )
    => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
    -> ranked rn n
    -> ranked rm (1 + m)
    -> ranked rn (1 + n)
  rscan f acc0 es =
    let shm :: IShR m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rscan: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      let bs =
            tproject2
            $ dmapAccumL (Proxy @ranked)
                snat
                (FTKR @rn sh)
                (FTKR @rn sh)
                (FTKR @rm shm)
                (let g :: forall f. ADReady f
                       => Rep f (TKR rn n) -> Rep f (TKR rm m)
                       -> Rep f (TKProduct (TKR rn n) (TKR rn n))
                     g !acc !e = blet (f acc e) $ \ !res -> tpair res res
                 in g)
                acc0
                es
      in rappend (rfromList [acc0]) bs
  -- | A strict left fold.
  sfold
    :: forall rn rm sh shm k.
       ( GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k
       , ProductTensor ranked
       , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
    => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
    -> shaped rn sh
    -> shaped rm (k ': shm)
    -> shaped rn sh
  sfold f acc0 es =
    tproject1
      (dmapAccumL (Proxy @ranked)
         (SNat @k)
         (FTKS @rn @sh knownShS)
         (FTKUntyped V.empty)
         (FTKS @rm @shm knownShS)
         (let g :: forall f. ADReady f
                => Rep f (TKS rn sh) -> Rep f (TKS rm shm)
                -> Rep f (TKProduct (TKS rn sh) TKUntyped)
              g !acc !e =
                tpair (f acc e)
                       (HVectorPseudoTensor $ dmkHVector V.empty)
          in g)
         acc0
         es)
  sscan
    :: forall rn rm sh shm k.
       ( GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k
       , ShapedTensor shaped, LetTensor ranked shaped, ProductTensor ranked
       , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
    => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
    -> shaped rn sh
    -> shaped rm (k ': shm)
    -> shaped rn (1 + k ': sh)
  sscan f acc0 es =
    let bs =
          tproject2
          $ dmapAccumL (Proxy @ranked)
             (SNat @k)
             (FTKS @rn @sh knownShS)
             (FTKS @rn @sh knownShS)
             (FTKS @rm @shm knownShS)
             (let g :: forall f. ADReady f
                    => Rep f (TKS rn sh) -> Rep f (TKS rm shm)
                    -> Rep f (TKProduct (TKS rn sh) (TKS rn sh))
                  g !acc !e = blet (f acc e) $ \ !res -> tpair res res
              in g)
             acc0
             es
    in sappend (sfromList [acc0]) bs
  -- | A strict right mapAccum.
  --
  -- The applications of 'dfwd' and 'drevDt' performed already at this point
  -- ensure that the computation of a derivative is not repeated
  -- and that its result is shared. However, most of the time
  -- the computation is unnneeded, so the AST instance uses a non-strict
  -- constructor 'AstLambda' for it's instance of 'HFunOf'.
  dmapAccumR
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy ranked
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> (forall f. ADReady f
        => RepDeep f accShs -> RepDeep f eShs
        -> Rep f (TKProduct accShs bShs))
    -> Rep ranked accShs
    -> Rep ranked (BuildTensorKind k eShs)
    -> Rep ranked (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumR proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => Rep f (TKProduct accShs eShs)
           -> Rep f (TKProduct accShs bShs)
        fl !args = tlet args $ \ (!acc1, !e1) ->
          dlet acc1 $ \ !acc ->
            dlet e1 $ \ !e ->
              f acc e
    in dmapAccumRDer proxy k accShs bShs eShs
                     (dlambda @ranked shs (HFun fl))
                     (dfwd @ranked shs $ HFun fl)
                     (drevDt @ranked shs $ HFun fl)
                     acc0 es
  dmapAccumRDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy ranked
    -> SNat k
    -> TensorKindFull accShs  -- ^ shapes of acc, the accumulator
    -> TensorKindFull bShs -- ^ shapes of b
    -> TensorKindFull eShs -- ^ shapes of e
    -> HFunOf ranked (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf ranked (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf ranked (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> Rep ranked accShs  -- ^ acc0 :: accShs
    -> Rep ranked (BuildTensorKind k eShs)
         -- ^ es :: k ': eShs
    -> Rep ranked (TKProduct accShs (BuildTensorKind k bShs))
         -- ^ (x, bs) :: (accShs, k ': bShs)
  -- | A strict left mapAccum.
  dmapAccumL
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy ranked
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> (forall f. ADReady f
        => RepDeep f accShs -> RepDeep f eShs
        -> Rep f (TKProduct accShs bShs))
    -> Rep ranked accShs
    -> Rep ranked (BuildTensorKind k eShs)
    -> Rep ranked (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => Rep f (TKProduct accShs eShs)
           -> Rep f (TKProduct accShs bShs)
        fl !args = tlet args $ \ (!acc1, !e1) ->
          dlet acc1 $ \ !acc ->
            dlet e1 $ \ !e ->
              f acc e
    in dmapAccumLDer proxy k accShs bShs eShs
                     (dlambda @ranked shs (HFun fl))
                     (dfwd @ranked shs $ HFun fl)
                     (drevDt @ranked shs $ HFun fl)
                     acc0 es
  dmapAccumLDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy ranked
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> HFunOf ranked (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> HFunOf ranked (TKProduct (ADTensorKind (TKProduct accShs eShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs bShs))
    -> HFunOf ranked (TKProduct (ADTensorKind (TKProduct accShs bShs))
                                (TKProduct accShs eShs))
                     (ADTensorKind (TKProduct accShs eShs))
    -> Rep ranked accShs
    -> Rep ranked (BuildTensorKind k eShs)
    -> Rep ranked (TKProduct accShs (BuildTensorKind k bShs))

-- TODO: tmkHVector should be removed, but the Delta instance needed
-- in interpreter makes this difficult.
class ProductTensor (ranked :: RankedTensorType) where
  tpair :: (TensorKind x, TensorKind z)
         => Rep ranked x -> Rep ranked z
         -> Rep ranked (TKProduct x z)
  tproject1 :: (TensorKind x, TensorKind z)
            => Rep ranked (TKProduct x z)
            -> Rep ranked x
  tproject2 :: (TensorKind x, TensorKind z)
            => Rep ranked (TKProduct x z)
            -> Rep ranked z
  tmkHVector :: HVector ranked -> HVectorOf ranked

tunit :: RankedTensor ranked
      => Rep ranked TKUnit
tunit = RepScalar $ rscalar ()

rfromD :: forall r n ranked.
          (RankedTensor ranked, GoodScalar r, KnownNat n)
       => DynamicTensor ranked -> ranked r n
rfromD (DynamicRanked @r2 @n2 t) = case sameNat (Proxy @n2) (Proxy @n) of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "rfromD: scalar mismatch"
  _ -> error $ "rfromD: rank mismatch "
               ++ show (valueOf @n2 :: Int, valueOf @n :: Int)
rfromD (DynamicShaped @r2 @sh2 t) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> rfromS t
    _ -> error "rfromD: scalar mismatch"
  _ -> error "rfromD: rank mismatch"
rfromD (DynamicRankedDummy @r2 @sh2 _ _) =
  withListSh (Proxy @sh2) $ \(sh1 :: IShR n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"
rfromD (DynamicShapedDummy @r2 @sh2 _ _) =
  withListSh (Proxy @sh2) $ \(sh1 :: IShR n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"

sfromD :: forall r sh shaped.
          ( ShapedTensor shaped
          , GoodScalar r, KnownShS sh
          , ShapedOf (RankedOf shaped) ~ shaped )
       => DynamicTensor (RankedOf shaped) -> shaped r sh
sfromD (DynamicRanked @r2 @n2 t) = case matchingRank @sh @n2 of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> sfromR t
    _ -> error "sfromD: scalar mismatch"
  _ -> error "sfromD: rank mismatch"
sfromD (DynamicShaped @r2 @sh2 t) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (shapeT @sh2, shapeT @sh)
sfromD (DynamicRankedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> srepl 0
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (shapeT @sh2, shapeT @sh)
sfromD (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> srepl 0
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (shapeT @sh2, shapeT @sh)

rscalar :: (GoodScalar r, RankedTensor ranked) => r -> ranked r 0
rscalar = rconst . Nested.rscalar

rrepl :: forall r n ranked. (GoodScalar r, KnownNat n, RankedTensor ranked)
      => [Int] -> r -> ranked r n
rrepl sh = rconst . Nested.rreplicateScal (fromList sh)

ringestData :: forall ranked r n.
              (GoodScalar r, KnownNat n, RankedTensor ranked)
           => [Int] -> [r] -> ranked r n
ringestData sh l = rconst $ Nested.rfromListPrimLinear (listToShape sh) l

ringestData1 :: forall ranked r. (GoodScalar r, RankedTensor ranked)
            => [r] -> ranked r 1
ringestData1 l = rconst $ Nested.rfromList1Prim l

ingestData :: forall shaped r sh.
              (GoodScalar r, KnownShS sh, ShapedTensor shaped)
           => [r] -> shaped r sh
ingestData l= sconst $ Nested.sfromListPrimLinear knownShS l

sscalar :: (GoodScalar r, ShapedTensor shaped) => r -> shaped r '[]
sscalar = sconst . Nested.sscalar

srepl :: forall sh r shaped. (GoodScalar r, KnownShS sh, ShapedTensor shaped)
      => r -> shaped r sh
srepl =
  sconst . Nested.sreplicateScal knownShS
  -- TODO: the following simplifies better, because the replication is not
  -- hidden at low level:
  -- Dict <- lemKnownNatSize (knownShS @sh) =
  --   sreplicate0N . sscalar
  -- though we could also look at the low level in @isSmall@ and mark
  -- replicated constants as small

xrepl :: forall sh r mixed.
         ( GoodScalar r, KnownShX sh, RankedTensor (RankedOf mixed)
         , MixedOf (RankedOf mixed) ~ mixed )
      => IShX sh -> r -> mixed r sh
xrepl sh =
  xconst . Nested.mreplicateScal sh

unrepShallow :: forall ranked y.
                    ( TensorKind y, HVectorTensor ranked (ShapedOf ranked)
                    , ProductTensor ranked )
                 => RepShallow ranked y
                 -> Rep ranked y
unrepShallow t = case stensorKind @y of
  STKScalar{} -> t
  STKR STKScalar{} _ -> t
  STKS STKScalar{} _ -> t
  STKX STKScalar{} _ -> t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 -> uncurry tpair t
  STKUntyped -> HVectorPseudoTensor $ dmkHVector t
  _ -> error "TODO"

unrepDeep :: forall ranked y.
             ( TensorKind y, HVectorTensor ranked (ShapedOf ranked)
             , ProductTensor ranked )
          => RepDeep ranked y
          -> Rep ranked y
unrepDeep t = case stensorKind @y of
  STKScalar{} -> t
  STKR STKScalar{} _ -> t
  STKS STKScalar{} _ -> t
  STKX STKScalar{} _ -> t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    tpair (unrepDeep (fst t)) (unrepDeep (snd t))
  STKUntyped -> HVectorPseudoTensor $ dmkHVector t
  _ -> error "TODO"

-- The argument of the first call (but not of recursive calls)
-- is assumed to be duplicable. In AST case, this creates
-- a tower of projections for product, but if it's balanced,
-- that's of logarithmic length, so maybe even better than sharing
-- excessively, which is hard for technical typing reasons.
-- See toRepDDuplicable.
repDeepDuplicable
  :: (HVectorTensor ranked (ShapedOf ranked), ProductTensor ranked)
  => STensorKindType y -> Rep ranked y
  -> RepDeep ranked y
repDeepDuplicable stk t = case stk of
  STKScalar{} -> t
  STKR STKScalar{} _ -> t
  STKS STKScalar{} _ -> t
  STKX STKScalar{} _ -> t
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    (repDeepDuplicable stk1 (tproject1 t), repDeepDuplicable stk2 (tproject2 t))
  STKUntyped -> dunHVector $ unHVectorPseudoTensor t
  _ -> error "TODO"

mapDynamic
  :: (RankedTensor f, ShapedTensor (ShapedOf f))
  => (forall r n. (GoodScalar r, KnownNat n)
      => Rep f (TKR r n) -> Rep g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => Rep f (TKS r sh) -> Rep g (TKS r sh))
  -> DynamicTensor f -> DynamicTensor g
mapDynamic fr _fs (DynamicRanked t) = DynamicRanked $ fr t
mapDynamic _fr fs (DynamicShaped t) = DynamicShaped $ fs t
mapDynamic fr _fs (DynamicRankedDummy @r @sh _ _) =
  withListSh (Proxy @sh) $ \sh1 ->
    DynamicRanked @r $ fr (rzero sh1)
mapDynamic _fr fs (DynamicShapedDummy @r @sh _ _) =
  DynamicShaped $ fs @r @sh (srepl 0)

mapDynamic2
  :: ( RankedTensor f1, ShapedTensor (ShapedOf f1)
     , RankedTensor f2, ShapedTensor (ShapedOf f2) )
  => (forall r n. (GoodScalar r, KnownNat n)
      => Rep f1 (TKR r n) -> Rep f2 (TKR r n)
      -> Rep g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => Rep f1 (TKS r sh) -> Rep f2 (TKS r sh)
      -> Rep g (TKS r sh))
  -> DynamicTensor f1 -> DynamicTensor f2 -> DynamicTensor g
mapDynamic2 fr _fs (DynamicRanked @r1 @n1 t1) (DynamicRanked @r2 @n2 t2) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameNat (Proxy @n1) (Proxy @n2) of
      Just Refl -> DynamicRanked $ fr t1 t2
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 fr _fs (DynamicRanked @r1 @n1 t1) (DynamicRankedDummy @r2 @sh2 _ _) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case matchingRank @sh2 @n1 of
      Just Refl -> withListSh (Proxy @sh2) $ \shp ->
        DynamicRanked @r1 $ fr t1 (rzero shp)
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 fr _fs (DynamicRankedDummy @r1 @sh1 _ _) (DynamicRanked @r2 @n2 t2) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case matchingRank @sh1 @n2 of
      Just Refl -> withListSh (Proxy @sh1) $ \shp ->
        DynamicRanked @r1 $ fr (rzero shp) t2
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 fr _fs (DynamicRankedDummy @r1 @sh1 _ _)
                (DynamicRankedDummy @r2 @sh2 _ _) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> withListSh (Proxy @sh1) $ \shp ->
        DynamicRanked @r1 $ fr (rzero shp) (rzero shp)
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 _fr fs (DynamicShaped @r1 @sh1 t1) (DynamicShaped @r2 @sh2 t2) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> DynamicShaped $ fs t1 t2
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 _fr fs (DynamicShaped @r1 @sh1 t1) (DynamicShapedDummy @r2 @sh2 _ _) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> DynamicShaped $ fs t1 (srepl 0)
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 _fr fs (DynamicShapedDummy @r1 @sh1 _ _) (DynamicShaped @r2 @sh2 t2) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> DynamicShaped $ fs (srepl 0) t2
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 _fr fs (DynamicShapedDummy @r1 @sh1 _ _)
                (DynamicShapedDummy @r2 @sh2 _ _) =
  case testEquality (typeRep @r1) (typeRep @r2) of
    Just Refl -> case sameShape @sh1 @sh2 of
      Just Refl -> DynamicShaped @_ @sh1 $ fs (srepl @_ @r1 0) (srepl @_ @r1 0)
      Nothing -> error "mapDynamic2: n mismatch"
    Nothing -> error "mapDynamic2: r mismatch"
mapDynamic2 _ _ _ _ = error "mapDynamic2: unexpected arguments"

mapRep
  :: forall f g y.
     ( ProductTensor f, ProductTensor g
     , RankedTensor f, ShapedTensor (ShapedOf f)
     , HVectorTensor f (ShapedOf f) )
  => (forall r n. (GoodScalar r, KnownNat n)
      => Rep f (TKR r n) -> Rep g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => Rep f (TKS r sh) -> Rep g (TKS r sh))
  -> (forall r sh. (GoodScalar r, KnownShX sh)
      => Rep f (TKX r sh) -> Rep g (TKX r sh))
  -> STensorKindType y
  -> Rep f y
  -> Rep g y
mapRep fr fs fx stk b = case stk of
  STKScalar _ -> RepScalar $ fr $ unRepScalar b
  STKR STKScalar{} SNat -> fr b
  STKS STKScalar{} sh -> withKnownShS sh $ fs b
  STKX STKScalar{} sh -> withKnownShX sh $ fx b
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    let !t1 = mapRep fr fs fx stk1 $ tproject1 b
        !t2 = mapRep fr fs fx stk2 $ tproject2 b
    in tpair t1 t2
      -- this shares properly only when the product instance for f is (,)
      -- and tlet wouldn't work because f and g differ
  STKUntyped ->
    -- Here @dletHVectorInHVector@ or @tlet@ wouldn't work
    -- because f and g differ.
    let fd :: DynamicTensor f -> DynamicTensor g
        fd = mapDynamic fr fs
    in HVectorPseudoTensor $ tmkHVector
       $ V.map fd
       $ dunHVector $ unHVectorPseudoTensor b
  _ -> error "TODO"

{- Not needed ATM and quite broken.
mapRep2
  :: forall f1 f2 g y.
     ( ProductTensor f1, ProductTensor f2, ProductTensor g
     , RankedTensor f1, ShapedTensor (ShapedOf f1)
     , RankedTensor f2, ShapedTensor (ShapedOf f2)
     , HVectorTensor f1 (ShapedOf f1)
     , HVectorTensor f2 (ShapedOf f2) )
  => (forall r n. (GoodScalar r, KnownNat n)
      => Rep f1 (TKR r n) -> Rep f2 (TKR r n)
      -> Rep g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => Rep f1 (TKS r sh) -> Rep f2 (TKS r sh)
      -> Rep g (TKS r sh))
  -> STensorKindType y
  -> Rep f1 y -> Rep f2 y
  -> Rep g y
mapRep2 fr fs stk b1 b2 = case stk of
  STKR{} -> fr b1 b2
  STKS{} -> fs b1 b2
  STKProduct stk1 stk2 ->
    let !t1 = mapRep2 fr fs stk1 (tproject1 b1) (tproject1 b2)
        !t2 = mapRep2 fr fs stk2 (tproject2 b1) (tproject2 b2)
    in tpair t1 t2
      -- this shares properly only when the product instance for f1 and f2 is (,)
  STKUntyped ->
    let fd :: DynamicTensor f1 -> DynamicTensor f2 -> DynamicTensor g
        fd = mapDynamic2 fr fs
    in HVectorPseudoTensor $ tmkHVector
       $ V.zipWith fd
           (dunHVector $ unHVectorPseudoTensor b1)
           (dunHVector $ unHVectorPseudoTensor b2)
-- TODO: we probably need two versions, one with let, one with share
--           (dunHVector $ tshare $ unHVectorPseudoTensor b1)
--           (dunHVector $ tshare $ unHVectorPseudoTensor b2)
-}

mapRep2Weak
  :: forall f1 f2 g y. (ProductTensor f1, ProductTensor f2, ProductTensor g)
  => (forall r n. (GoodScalar r, KnownNat n)
      => Rep f1 (TKR r n) -> Rep f2 (TKR r n)
      -> Rep g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => Rep f1 (TKS r sh) -> Rep f2 (TKS r sh)
      -> Rep g (TKS r sh))
  -> (forall r sh. (GoodScalar r, KnownShX sh)
      => Rep f1 (TKX r sh) -> Rep f2 (TKX r sh)
      -> Rep g (TKX r sh))
  -> STensorKindType y
  -> Rep f1 y -> Rep f2 y
  -> Rep g y
mapRep2Weak fr fs fx stk b1 b2 = case stk of
  STKScalar _ -> RepScalar $ fr (unRepScalar b1) (unRepScalar b2)
  STKR STKScalar{} SNat -> fr b1 b2
  STKS STKScalar{} sh -> withKnownShS sh $ fs b1 b2
  STKX STKScalar{} sh -> withKnownShX sh $ fx b1 b2
  STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                       , Dict <- lemTensorKindOfS stk2 ->
    let !t1 = mapRep2Weak fr fs fx stk1 (tproject1 b1) (tproject1 b2)
        !t2 = mapRep2Weak fr fs fx stk2 (tproject2 b1) (tproject2 b2)
    in tpair t1 t2
      -- this shares properly only when the product instance for f1 and f2 is (,)
  STKUntyped -> error "TODO: mapRep2Weak is weak"
  _ -> error "TODO"

-- These are user-accessible, so the constraint is `ADReady`, which means
-- lets, but no shares.
type role HFun nominal nominal
newtype HFun (x :: TensorKindType) (z :: TensorKindType) =
  HFun {unHFun :: forall f. ADReady f
               => Rep f x -> Rep f z}

instance Show (HFun x y) where
  show _ = "<lambda>"


-- * The giga-constraint

type ADReady ranked = ADReadyBoth ranked (ShapedOf ranked)

type ADReadyNoLet ranked = ADReadyBothNoLet ranked (ShapedOf ranked)

type ADReadyS shaped = ADReadyBoth (RankedOf shaped) shaped

type ADReadyNoLetS shaped = ADReadyBothNoLet (RankedOf shaped) shaped

type ADReadyBoth ranked shaped =
  ( ADReadyBothNoLet ranked shaped
  , LetTensor ranked shaped
-- The following can't be added, because we have instances like ADVal (AstRaw),
-- so AstRaw would need to have a LetTensor instance:
--  , LetTensor (PrimalOf ranked) (PrimalOf shaped)
  )

type ADReadyBothNoLet ranked shaped =
  ( ADReadyEqsClasses ranked shaped (MixedOf ranked)
  , ADReadyEqsClasses (ShareOf ranked) (ShapedOf (ShareOf ranked))
                      (MixedOf (ShareOf ranked))
  , ShareTensor (ShareOf ranked)
  , ShareTensor (PrimalOf (ShareOf ranked))
  , ShareOf (ShareOf ranked) ~ ShareOf ranked
  )

type ADReadyEqsClasses ranked shaped mixed =
  ( ADReadyEqs ranked shaped mixed
  , ADReadyClasses ranked shaped mixed
  , ADReadyClasses (PrimalOf ranked) (PrimalOf shaped) (PrimalOf mixed)
  , ProductTensor (DualOf ranked)
  )

type ADReadyEqs ranked shaped mixed =
  ( RankedOf ranked ~ ranked
  , RankedOf shaped ~ ranked
  , RankedOf mixed ~ ranked
  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked
  , RankedOf (PrimalOf shaped) ~ PrimalOf ranked
  , RankedOf (PrimalOf mixed) ~ PrimalOf ranked
  , ShapedOf (PrimalOf ranked) ~ PrimalOf shaped
  , ShapedOf (DualOf ranked) ~ DualOf shaped
  , ShapedOf (PrimalOf ranked) ~ PrimalOf shaped
  , MixedOf (PrimalOf ranked) ~ PrimalOf mixed
  , MixedOf (DualOf ranked) ~ DualOf mixed
  , MixedOf (PrimalOf ranked) ~ PrimalOf mixed
  , BoolOf ranked ~ BoolOf shaped
  , BoolOf ranked ~ BoolOf mixed
  , BoolOf (PrimalOf ranked) ~ BoolOf ranked
  , BoolOf (PrimalOf shaped) ~ BoolOf ranked
  , BoolOf (PrimalOf mixed) ~ BoolOf ranked
  )

type ADReadyClasses ranked shaped mixed =
  ( Boolean (BoolOf ranked)
  , IfF ranked, IfF shaped, IfF mixed
  , EqF ranked, EqF shaped, EqF mixed
  , OrdF ranked, OrdF shaped, OrdF mixed
  , RankedTensor ranked
  , ShapedTensor shaped
  , HVectorTensor ranked shaped
  , ProductTensor ranked
  , CRanked ranked Show
  , CShaped shaped Show
  , CMixed mixed Show
  , Show (HVectorOf ranked)
  , CRepProduct ranked Show
  , CHFun2 ranked Show
  )
