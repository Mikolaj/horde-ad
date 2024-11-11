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
  , LetTensor(..), ShareTensor(..), BaseTensor(..)
  , HFun(..)
  , tunit, rfromD, sfromD, rscalar, rrepl, ringestData
  , ingestData, sscalar, srepl, xrepl, nullRep
  , mapDynamic2
    -- * The giga-constraint
  , ADReady, ADReadyNoLet
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

type TensorSupports :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupports c1 c2 f =
  forall r n. (GoodScalar r, KnownNat n)
              => c1 r => c2 (f (TKR r n))

type TensorSupportsS :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsS c1 c2 f =
  forall r sh. (GoodScalar r, KnownShS sh)
               => c1 r => c2 (f (TKS r sh))

type TensorSupportsX :: (Type -> Constraint) -> (Type -> Constraint) -> Target -> Constraint
type TensorSupportsX c1 c2 f =
  forall r sh. (GoodScalar r, KnownShX sh)
               => c1 r => c2 (f (TKX r sh))

class (RealFloat r, Nested.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloat r, Nested.FloatElt r)
         => RealFloatAndFloatElt r

class LetTensor (target :: Target) where
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => target x
       -> (target x -> target z)
       -> target z
  treplicate :: BaseTensor target
             => SNat k -> STensorKindType z
             -> target z
             -> target (BuildTensorKind k z)
  treplicate snat@SNat stk u = case stk of
    STKScalar _ -> rreplicate (sNatValue snat) $ runRepScalar u
    STKR STKScalar{} SNat -> rreplicate (sNatValue snat) u
    STKS STKScalar{} sh -> withKnownShS sh $ sreplicate u
    STKX STKScalar{} sh -> withKnownShX sh $ xreplicate u
    STKProduct @z1 @z2 stk1 stk2
      | Dict <- lemTensorKindOfS stk1
      , Dict <- lemTensorKindOfS stk2
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z1)
      , Dict <- lemTensorKindOfBuild snat (stensorKind @z2) ->
        tlet u $ \ !u1 ->
          tpair (treplicate snat stk1 (tproject1 u1))
                (treplicate snat stk2 (tproject2 u1))
    STKUntyped ->
      tlet u $ \ !u1 ->
        dmkHVector
        $ replicate1HVectorF rreplicate sreplicate snat
        $ dunHVector u1
    _ -> error "TODO"

  toShare :: TensorKind y
          => target y
          -> ShareOf target y
  tunshare :: TensorKind y
           => ShareOf target y
           -> target y
  tunshare = error "tunshare: this instance should never be used"

class ShareTensor (target :: Target) where
  tshare :: forall y. (TensorKind y, BaseTensor target)
         => target y -> target y
  tunpair :: (TensorKind x, TensorKind z)
          => target (TKProduct x z)
          -> (target x, target z)
  tunvector :: target TKUntyped
            -> HVector target
  taddShare :: STensorKindType y -> target y -> target y
            -> target y

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Num (IntOf target)
      , IntegralF (IntOf target)
      , TensorSupports Num Num target
      , TensorSupports RealFloatAndFloatElt Floating target
      , TensorSupports RealFloatAndFloatElt RealFloatF target
      , TensorSupports Integral IntegralF target
      , TensorSupportsS Num Num target
      , TensorSupportsS RealFloatAndFloatElt Floating target
      , TensorSupportsS RealFloatAndFloatElt RealFloatF target
      , TensorSupportsS Integral IntegralF target
      , TensorSupportsX Num Num target
      , TensorSupportsX RealFloatAndFloatElt Floating target
      , TensorSupportsX RealFloatAndFloatElt RealFloatF target
      , TensorSupportsX Integral IntegralF target )
      => BaseTensor (target :: Target) where

  rmkRepScalar :: GoodScalar r => target (TKR r 0) -> target (TKScalar r)
  runRepScalar :: GoodScalar r => target (TKScalar r) -> target (TKR r 0)

  -- Integer codomain
  rshape :: (GoodScalar r, KnownNat n) => target (TKR r n) -> IShR n
  rrank :: forall r n. (GoodScalar r, KnownNat n) => target (TKR r n) -> Int
  rrank _ = valueOf @n
  rsize :: (GoodScalar r, KnownNat n) => target (TKR r n) -> Int
  rsize = sizeShape . rshape
  rlength :: (GoodScalar r, KnownNat n) => target (TKR r (1 + n)) -> Int
  rlength v = case rshape v of
    ZSR -> error "rlength: impossible pattern needlessly required"
    k :$: _ -> k
  rminIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => target (TKR r (1 + n)) -> target (TKR r2 n)  -- partial
  rmaxIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => target (TKR r (1 + n)) -> target (TKR r2 n)  -- partial
  rfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => target (TKR r n) -> target (TKR r2 n)
  riota :: GoodScalar r => target (TKR r 1)  -- 0, 1 .. infinity
  riota = undefined  -- infinite, hence diverges; don't override

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- may indicate the rank of the codomain, if bounded.

  -- First index is for outermost dimension; empty index means identity,
  -- index ouf of bounds produces zero (but beware of vectorization).
  rindex, (!) :: (GoodScalar r, KnownNat m, KnownNat n)
              => target (TKR r (m + n)) -> IndexOf target m -> target (TKR r n)
  infixl 9 !
  (!) = rindex  -- prefix form better when type applications are necessary
  rindex0 :: (GoodScalar r, KnownNat m)
          => target (TKR r m) -> IndexOf target m -> target (TKR r 0)
  rindex0 = rindex
  rsum :: (GoodScalar r, KnownNat n) => target (TKR r (1 + n)) -> target (TKR r n)
  rsum0 :: (GoodScalar r, KnownNat n) => target (TKR r n) -> target (TKR r 0)
  rsum0 = rsum . rflatten
  rdot0 :: (GoodScalar r, KnownNat n) => target (TKR r n) -> target (TKR r n) -> target (TKR r 0)
  rdot0 t u = rsum (rflatten (t * u))
  rmatvecmul :: GoodScalar r => target (TKR r 2) -> target (TKR r 1) -> target (TKR r 1)
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
  rmatvecmul m v = rbuild1 (rlength m) (\i -> rdot0 v (m ! [i]))
-- rmatvecmul m v = rflatten $ rmap1 (rreplicate 1 . rdot0 v) m
  rmatmul2 :: (GoodScalar r, Numeric r)
           => target (TKR r 2) -> target (TKR r 2) -> target (TKR r 2)
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
-- rmatmul2 m1 m2 = rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR -> rsum (rtranspose [2,1,0] (rreplicate width2 m1)
                                  * rtranspose [1,0] (rreplicate (rlength m1) m2))
    _ -> error "rmatmul2: impossible pattern needlessly required"
  rscatter :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> target (TKR r (m + n))
           -> (IndexOf target m -> IndexOf target p)
           -> target (TKR r (p + n))
  rscatter1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
            => IShR (p + n) -> target (TKR r (1 + n))
            -> (IntOf target -> IndexOf target p)
            -> target (TKR r (p + n))
  rscatter1 sh v f = rscatter @target @r @1 sh v
                              (\(i :.: ZIR) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  rfromList :: (GoodScalar r, KnownNat n)
            => NonEmpty (target (TKR r n)) -> target (TKR r (1 + n))
  rfromList = rfromVector . V.fromList . NonEmpty.toList
    -- going through strict vectors, because laziness is risky with impurity
  rfromList0N :: (GoodScalar r, KnownNat n)
              => IShR n -> [target (TKR r 0)] -> target (TKR r n)
  rfromList0N sh = rfromVector0N sh . V.fromList
  -- This is morally non-empty strict vectors:
  rfromVector :: (GoodScalar r, KnownNat n)
              => Data.Vector.Vector (target (TKR r n)) -> target (TKR r (1 + n))
  rfromVector0N :: (GoodScalar r, KnownNat n)
                => IShR n -> Data.Vector.Vector (target (TKR r 0)) -> target (TKR r n)
  rfromVector0N sh = rreshape sh . rfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  runravelToList :: forall r n. (GoodScalar r, KnownNat n)
                 => target (TKR r (1 + n)) -> [target (TKR r n)]
  runravelToList t =
    let f :: Int -> target (TKR r n)
        f i = rindex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate :: (GoodScalar r, KnownNat n)
             => Int -> target (TKR r n) -> target (TKR r (1 + n))
  rreplicate0N :: (GoodScalar r, KnownNat n)
               => IShR n -> target (TKR r 0) -> target (TKR r n)
  rreplicate0N sh = rreshape sh . rreplicate (sizeShape sh)
  rappend :: (GoodScalar r, KnownNat n)
          => target (TKR r (1 + n)) -> target (TKR r (1 + n)) -> target (TKR r (1 + n))
  rconcat :: (GoodScalar r, KnownNat n)
          => [target (TKR r (1 + n))] -> target (TKR r (1 + n))
  rconcat = foldr1 rappend
  rslice :: (GoodScalar r, KnownNat n)
         => Int -> Int -> target (TKR r (1 + n)) -> target (TKR r (1 + n))
  runcons :: (GoodScalar r, KnownNat n)
          => target (TKR r (1 + n)) -> Maybe (target (TKR r n), target (TKR r (1 + n)))
  runcons v = case rshape v of
                ZSR -> Nothing
                len :$: _ -> Just (v ! [0], rslice 1 (len - 1) v)
  rreverse :: (GoodScalar r, KnownNat n) => target (TKR r (1 + n)) -> target (TKR r (1 + n))
  rtr :: (GoodScalar r, KnownNat n) => target (TKR r (2 + n)) -> target (TKR r (2 + n))
  rtr = rtranspose [1, 0]
  rtranspose :: (GoodScalar r, KnownNat n)
             => Permutation.PermR -> target (TKR r n) -> target (TKR r n)
  rflatten :: (GoodScalar r, KnownNat n) => target (TKR r n) -> target (TKR r 1)
  rflatten u = rreshape (flattenShape $ rshape u) u
  rreshape :: (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> target (TKR r n) -> target (TKR r m)
  rbuild :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
         => IShR (m + n) -> (IndexOf target m -> target (TKR r n))
         -> target (TKR r (m + n))
  rbuild sh0 f0 =
    let buildSh :: IShR m1 -> (IndexOf target m1 -> target (TKR r n))
                -> target (TKR r (m1 + n))
        buildSh ZSR f = f ZIR
        buildSh (k :$: sh) f | Dict <- knownShR sh =
          let g i = buildSh sh (\ix -> f (i :.: ix))
          in rbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  rbuild1 :: (GoodScalar r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf target -> target (TKR r n)) -> target (TKR r (1 + n))
  rmap :: (GoodScalar r, GoodScalar r2, KnownNat m, KnownNat n)
       => (target (TKR r n) -> target (TKR r2 n))
       -> target (TKR r (m + n)) -> target (TKR r2 (m + n))
  rmap f v = rbuild (rshape v) (\ix -> f (v ! ix))
  rmap1 :: (GoodScalar r, GoodScalar r2, KnownNat n)
        => (target (TKR r n) -> target (TKR r2 n))
        -> target (TKR r (1 + n)) -> target (TKR r2 (1 + n))
  rmap1 f u = rbuild1 (rlength u) (\i -> f (u ! [i]))
  rmap0N :: (GoodScalar r, GoodScalar r1, KnownNat n)
         => (target (TKR r1 0) -> target (TKR r 0)) -> target (TKR r1 n) -> target (TKR r n)
  rmap0N f v = rbuild (rshape v) (f . rindex0 v)
  rzipWith :: ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n )
           => IShR (m + n)
           -> (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r n))
           -> target (TKR r1 (m + n1)) -> target (TKR r2 (m + n2)) -> target (TKR r (m + n))
  rzipWith sh f u v = rbuild sh (\ix -> f (u ! ix) (v ! ix))
  rzipWith1 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n1, KnownNat n2, KnownNat n )
            => (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r n))
            -> target (TKR r1 (1 + n1)) -> target (TKR r2 (1 + n2)) -> target (TKR r (1 + n))
  rzipWith1 f u v = rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]))
  rzipWith0N :: (GoodScalar r1, GoodScalar r2, GoodScalar r, KnownNat n)
             => (target (TKR r1 0) -> target (TKR r2 0) -> target (TKR r 0))
             -> target (TKR r1 n) -> target (TKR r2 n) -> target (TKR r n)
  rzipWith0N f u v = rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))
  rzipWith3 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
               , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
            => IShR (m + n)
            -> (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r3 n3) -> target (TKR r n))
            -> target (TKR r1 (m + n1)) -> target (TKR r2 (m + n2)) -> target (TKR r3 (m + n3))
            -> target (TKR r (m + n))
  rzipWith3 sh f u v w = rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix))
  rzipWith31 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n )
             => (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r3 n3) -> target (TKR r n))
             -> target (TKR r1 (1 + n1)) -> target (TKR r2 (1 + n2)) -> target (TKR r3 (1 + n3))
             -> target (TKR r (1 + n))
  rzipWith31 f u v w =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]))
  rzipWith30N :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , KnownNat n )
              => (target (TKR r1 0) -> target (TKR r2 0) -> target (TKR r3 0) -> target (TKR r 0))
              -> target (TKR r1 n) -> target (TKR r2 n) -> target (TKR r3 n) -> target (TKR r n)
  rzipWith30N f u v w =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix))
  rzipWith4 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
               , GoodScalar r, KnownNat m
               , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
               , KnownNat n )
            => IShR (m + n)
            -> (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r3 n3) -> target (TKR r4 n4)
                -> target (TKR r n))
            -> target (TKR r1 (m + n1)) -> target (TKR r2 (m + n2)) -> target (TKR r3 (m + n3))
            -> target (TKR r4 (m + n4))
            -> target (TKR r (m + n))
  rzipWith4 sh f u v w x =
    rbuild sh (\ix -> f (u ! ix) (v ! ix) (w ! ix) (x ! ix))
  rzipWith41 :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                , GoodScalar r
                , KnownNat n1, KnownNat n2, KnownNat n3, KnownNat n4
                , KnownNat n )
             => (target (TKR r1 n1) -> target (TKR r2 n2) -> target (TKR r3 n3) -> target (TKR r4 n4)
                 -> target (TKR r n))
             -> target (TKR r1 (1 + n1)) -> target (TKR r2 (1 + n2)) -> target (TKR r3 (1 + n3))
             -> target (TKR r4 (1 + n4))
             -> target (TKR r (1 + n))
  rzipWith41 f u v w x =
    rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]) (w ! [i]) (x ! [i]))
  rzipWith40N :: ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r
                 , KnownNat n )
              => (target (TKR r1 0) -> target (TKR r2 0) -> target (TKR r3 0) -> target (TKR r4 0)
                  -> target (TKR r 0))
              -> target (TKR r1 n) -> target (TKR r2 n) -> target (TKR r3 n) -> target (TKR r4 n)
              -> target (TKR r n)
  rzipWith40N f u v w x =
    rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix) (rindex0 w ix)
                                (rindex0 x ix))
  rgather :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
          => IShR (m + n) -> target (TKR r (p + n))
          -> (IndexOf target m -> IndexOf target p)
          -> target (TKR r (m + n))
  rgather1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
           => Int -> target (TKR r (p + n))
           -> (IntOf target -> IndexOf target p)
           -> target (TKR r (1 + n))
  rgather1 k v f = rgather @target @r @1
                           (k :$: dropShape (rshape v)) v
                           (\(i :.: ZIR) -> f i)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => target (TKR r1 n) -> target (TKR r2 n)
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => target (TKR r1 n) -> target (TKR r2 n)
  rconcrete :: (GoodScalar r, KnownNat n) => Nested.Ranked n r -> target (TKR r n)
  rfromS :: (GoodScalar r, KnownShS sh)
         => target (TKS r sh) -> target (TKR r (Rank sh))
  -- Prevents wrong shape in @0@ with ranked (but not shaped) tensors
  -- at any rank greater than zero.
  rzero :: (GoodScalar r, KnownNat n)
        => IShR n -> target (TKR r n)
  rzero sh = rreplicate0N sh 0

  -- ** No serviceable parts beyond this point ** --

  rscaleByScalar :: (GoodScalar r, KnownNat n)
                 => target (TKR r 0) -> target (TKR r n) -> target (TKR r n)
  rscaleByScalar s v = v * rreplicate0N (rshape v) s
  rdot1In :: GoodScalar r
          => target (TKR r 2) -> target (TKR r 2)
          -> target (TKR r 1)  -- TODO: generalize
  rdot1In t u = rsum $ rtr (t * u)

  -- Primal/dual things.
  rfromPrimal :: (GoodScalar r, KnownNat n) => PrimalOf target (TKR r n) -> target (TKR r n)
  rprimalPart :: (GoodScalar r, KnownNat n)
              => target (TKR r n) -> PrimalOf target (TKR r n)
  rdualPart :: (GoodScalar r, KnownNat n)
            => target (TKR r n) -> DualOf target (TKR r n)
  rD :: (GoodScalar r, KnownNat n)
     => PrimalOf target (TKR r n) -> DualOf target (TKR r n) -> target (TKR r n)
  rScale :: (GoodScalar r, KnownNat n)
         => PrimalOf target (TKR r n) -> DualOf target (TKR r n)
         -> DualOf target (TKR r n)
  -- TODO: we'd probably also need dZero, dIndex0 and others from IsPrimal,
  -- because IsPrimal has subtly different types, operating on Deltas (Dual)
  -- instead of on terms (DualOf) that denote Deltas
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  xshape :: (GoodScalar r, KnownShX sh) => target (TKX r sh) -> IShX sh
  xindex :: forall r sh1 sh2.
            ( GoodScalar r, KnownShX sh1, KnownShX sh2
            , KnownShX (sh1 ++ sh2) )
         => target (TKX r (sh1 ++ sh2)) -> IndexShX target sh1
         -> target (TKX r sh2)
  xfromVector :: (GoodScalar r, KnownNat n, KnownShX sh)
              => Data.Vector.Vector (target (TKX r sh))
              -> target (TKX r (Just n ': sh))
  xreplicate :: (KnownNat n, KnownShX sh, GoodScalar r)
             => target (TKX r sh) -> target (TKX r (Just n ': sh))
  xconcrete :: (GoodScalar r, KnownShX sh)
         => Nested.Mixed sh r -> target (TKX r sh)
  xzero :: forall r sh. (GoodScalar r, KnownShX sh)
        => IShX sh -> target (TKX r sh)
  xzero sh = xrepl sh 0
  xfromPrimal :: (GoodScalar r, KnownShX sh)
            => PrimalOf target (TKX r sh) -> target (TKX r sh)
  xprimalPart :: (GoodScalar r, KnownShX sh)
              => target (TKX r sh) -> PrimalOf target (TKX r sh)
  xdualPart :: (GoodScalar r, KnownShX sh)
            => target (TKX r sh) -> DualOf target (TKX r sh)
  xD :: (GoodScalar r, KnownShX sh)
     => PrimalOf target (TKX r sh)-> DualOf target (TKX r sh)
     -> target (TKX r sh)

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, KnownShS sh)
         => target (TKS r sh) -> ShS sh
  sshape _ = knownShS @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (Rank sh))
        => target (TKS r sh) -> Int
  srank _ = valueOf @(Rank sh)
  ssize :: forall sh r. (GoodScalar r, KnownShS sh) => target (TKS r sh) -> Int
  ssize _ = sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => target (TKS r (n ': sh)) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => target (TKS r (n ': sh)) -> target (TKS r2 (Init (n ': sh)))
  smaxIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Init (n ': sh)) )  -- partial
            => target (TKS r (n ': sh)) -> target (TKS r2 (Init (n ': sh)))
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShS sh)
         => target (TKS r sh) -> target (TKS r2 sh)
    -- the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => target (TKS r '[n])  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( GoodScalar r, KnownShS sh1, KnownShS sh2
                  , KnownShS (sh1 ++ sh2) )
               => target (TKS r (sh1 ++ sh2)) -> IndexSh target sh1
               -> target (TKS r sh2)
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, KnownShS sh1)
          => target (TKS r sh1) -> IndexSh target sh1
          -> target (TKS r '[])
  sindex0 = gcastWith (unsafeCoerce Refl :: sh1 ++ '[] :~: sh1)
              sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
       => target (TKS r (n ': sh)) -> target (TKS r sh)
  ssum0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS r sh) -> target (TKS r '[])
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
        => target (TKS r sh) -> target (TKS r sh) -> target (TKS r '[])
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => target (TKS r '[m, n]) -> target (TKS r '[n]) -> target (TKS r '[m])
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (i :.$ ZIS)))
  smatmul2 :: forall r n m p.
              (GoodScalar r, Numeric r, KnownNat n, KnownNat m, KnownNat p)
           => target (TKS r '[m, n]) -> target (TKS r '[n, p]) -> target (TKS r '[m, p])
  smatmul2 m1 m2 =
    ssum (stranspose (Permutation.makePerm @'[2, 1, 0]) (sreplicate @target @p m1)
          * stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @target @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh)
       , KnownShS (sh2 ++ Drop p sh) )
    => target (TKS r (sh2 ++ Drop p sh))
    -> (IndexSh target sh2 -> IndexSh target (Take p sh))
    -> target (TKS r sh)
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh) )
    => target (TKS r (n2 ': Drop p sh))
    -> (IntOf target -> IndexSh target (Take p sh))
    -> target (TKS r sh)
  sscatter1 v f = sscatter @target @r @'[n2] v (\(i :.$ _) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (GoodScalar r, KnownNat n, KnownShS sh)
            => NonEmpty (target (TKS r sh)) -> target (TKS r (n ': sh))
  sfromList = sfromVector . V.fromList . NonEmpty.toList
  sfromList0N :: forall r sh.
                 (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
              => [target (TKS r '[])] -> target (TKS r sh)
  sfromList0N = sfromVector0N . V.fromList
  -- This is morally non-empty strict vectors:
  sfromVector :: (GoodScalar r, KnownNat n, KnownShS sh)
              => Data.Vector.Vector (target (TKS r sh)) -> target (TKS r (n ': sh))
  sfromVector0N :: forall r sh.
                   (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
                => Data.Vector.Vector (target (TKS r '[]))
                -> target (TKS r sh)
  sfromVector0N = sreshape @target @r @'[Nested.Product sh] @sh . sfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'tlet'.
  sunravelToList :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
                 => target (TKS r (n ': sh)) -> [target (TKS r sh)]
  sunravelToList t =
    let f :: Int -> target (TKS r sh)
        f i = sindex t (ShapedList.singletonIndex $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate :: (KnownNat n, KnownShS sh, GoodScalar r)
             => target (TKS r sh) -> target (TKS r (n ': sh))
  sreplicate0N :: forall r sh.
                  (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
               => target (TKS r '[]) -> target (TKS r sh)
  sreplicate0N = sreshape @target @r @'[Nested.Product sh] @sh
                 . sreplicate @target @(Nested.Product sh)
  sappend :: (GoodScalar r, KnownNat m, KnownNat n, KnownShS sh)
          => target (TKS r (m ': sh)) -> target (TKS r (n ': sh))
          -> target (TKS r ((m + n) ': sh))
  sslice :: (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
         => Proxy i -> Proxy n
         -> target (TKS r (i + n + k ': sh)) -> target (TKS r (n ': sh))
  suncons :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => target (TKS r (n ': sh)) -> Maybe (target (TKS r sh), target (TKS r (n - 1 ': sh)))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @target @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :.$ ZIS)
                , sslice @target @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (GoodScalar r, KnownNat n, KnownShS sh)
           => target (TKS r (n ': sh)) -> target (TKS r (n ': sh))
  str :: ( GoodScalar r, KnownNat n, KnownNat m, KnownShS sh
         , KnownNat (Rank sh) )
      => target (TKS r (n ': m ': sh)) -> target (TKS r (m ': n ': sh))
  str = stranspose (Permutation.makePerm @'[1, 0])
  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , Rank perm <= Rank sh, GoodScalar r )
             => Permutation.Perm perm -> target (TKS r sh)
             -> target (TKS r (Permutation.PermutePrefix perm sh))
  sflatten :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
           => target (TKS r sh) -> target (TKS r '[Nested.Product sh])
  sflatten = sreshape
  sreshape :: ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Product sh ~ Nested.Product sh2 )
           => target (TKS r sh) -> target (TKS r sh2)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh. (GoodScalar r, KnownShS sh, KnownShS (Take m sh))
         => (IndexSh target (Take m sh) -> target (TKS r (Drop m sh)))
         -> target (TKS r sh)
  sbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 ++ Drop m sh)
          -> (IndexSh target sh1 -> target (TKS r (Drop m sh)))
          -> target (TKS r (sh1 ++ Drop m sh))
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
          => (IntOf target -> target (TKS r sh))
          -> target (TKS r (n ': sh))
  smap :: forall r r2 m sh.
          ( GoodScalar r, GoodScalar r2, KnownNat m
          , KnownShS sh, KnownShS (Take m sh), KnownShS (Drop m sh) )
       => (target (TKS r (Drop m sh)) -> target (TKS r2 (Drop m sh)))
       -> target (TKS r sh) -> target (TKS r2 sh)
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: Take m sh ++ Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r r2 sh n.
           (GoodScalar r, GoodScalar r2, KnownNat n, KnownShS sh)
        => (target (TKS r sh) -> target (TKS r2 sh))
        -> target (TKS r (n ': sh)) -> target (TKS r2 (n ': sh))
  smap1 f u = sbuild1 (\i -> f (u !$ (i :.$ ZIS)))
  smap0N :: forall r1 r sh.
            (GoodScalar r1, GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => (target (TKS r1 '[]) -> target (TKS r '[])) -> target (TKS r1 sh) -> target (TKS r sh)
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @r @(Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownShS sh1, KnownShS sh2, KnownShS sh
              , KnownShS (Take m sh), KnownShS (Drop m sh1)
              , KnownShS (Drop m sh2), KnownShS (Drop m sh)
              , sh1 ~ Take m sh ++ Drop m sh1
              , sh2 ~ Take m sh ++ Drop m sh2 )
           => (target (TKS r1 (Drop m sh1))
               -> target (TKS r2 (Drop m sh2))
               -> target (TKS r (Drop m sh)))
           -> target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r sh)
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh )
            => (target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r sh))
            -> target (TKS r1 (n ': sh1)) -> target (TKS r2 (n ': sh2))
            -> target (TKS r (n ': sh))
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                     (v !$ (i :.$ ZIS)))
  szipWith0N :: forall r1 r2 r sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r
                , KnownShS sh, KnownNat (Rank sh) )
             => (target (TKS r1 '[]) -> target (TKS r2 '[]) -> target (TKS r '[]))
             -> target (TKS r1 sh) -> target (TKS r2 sh) -> target (TKS r sh)
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
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
            => (target (TKS r1 (Drop m sh1))
                -> target (TKS r2 (Drop m sh2))
                -> target (TKS r3 (Drop m sh3))
                -> target (TKS r (Drop m sh)))
            -> target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r3 sh3) -> target (TKS r sh)
  szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
  szipWith31 :: forall r1 r2 r3 r n sh1 sh2 sh3 sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                , KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh )
             => (target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r3 sh3) -> target (TKS r sh))
             -> target (TKS r1 (n ': sh1)) -> target (TKS r2 (n ': sh2))
             -> target (TKS r3 (n ': sh3))
             -> target (TKS r (n ': sh))
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                        (v !$ (i :.$ ZIS))
                                        (w !$ (i :.$ ZIS)))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS r1 '[]) -> target (TKS r2 '[]) -> target (TKS r3 '[])
                  -> target (TKS r '[]))
              -> target (TKS r1 sh) -> target (TKS r2 sh) -> target (TKS r3 sh) -> target (TKS r sh)
  szipWith30N f u v w =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
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
            => (target (TKS r1 (Drop m sh1))
                -> target (TKS r2 (Drop m sh2))
                -> target (TKS r3 (Drop m sh3))
                -> target (TKS r4 (Drop m sh4))
                -> target (TKS r (Drop m sh)))
            -> target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r3 sh3) -> target (TKS r4 sh4)
            -> target (TKS r sh)
  szipWith4 f u v w x =
    sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix) (x !$ ix))
  szipWith41 :: forall r1 r2 r3 r4 r n sh1 sh2 sh3 sh4 sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                , GoodScalar r, KnownNat n
                , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
                , KnownShS sh )
             => (target (TKS r1 sh1) -> target (TKS r2 sh2) -> target (TKS r3 sh3)
                 -> target (TKS r4 sh4) -> target (TKS r sh))
             -> target (TKS r1 (n ': sh1)) -> target (TKS r2 (n ': sh2))
             -> target (TKS r3 (n ': sh3)) -> target (TKS r4 (n ': sh4))
             -> target (TKS r (n ': sh))
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ (i :.$ ZIS))
                                          (v !$ (i :.$ ZIS))
                                          (w !$ (i :.$ ZIS))
                                          (x !$ (i :.$ ZIS)))
  szipWith40N :: forall r1 r2 r3 r4 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r, KnownShS sh, KnownNat (Rank sh) )
              => (target (TKS r1 '[]) -> target (TKS r2 '[]) -> target (TKS r3 '[])
                  -> target (TKS r4 '[]) -> target (TKS r '[]))
              -> target (TKS r1 sh) -> target (TKS r2 sh) -> target (TKS r3 sh) -> target (TKS r4 sh)
              -> target (TKS r sh)
  szipWith40N f u v w x =
    gcastWith (unsafeCoerce Refl :: Drop (Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Take (Rank sh) sh :~: sh)
    $ sbuild @target @_ @(Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix)
                                                (sindex0 x ix))
  sgather
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh)
       , KnownShS (sh2 ++ Drop p sh) )
    => target (TKS r sh)
    -> (IndexSh target sh2 -> IndexSh target (Take p sh))
    -> target (TKS r (sh2 ++ Drop p sh))
  sgather1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownNat p
       , KnownShS (Take p sh), KnownShS (Drop p sh) )
    => target (TKS r sh)
    -> (IntOf target -> IndexSh target (Take p sh))
    -> target (TKS r (n2 ': Drop p sh))
  sgather1 v f = sgather @target @r @'[n2] v (\(i :.$ _) -> f i)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownShS sh)
        => target (TKS r1 sh) -> target (TKS r2 sh)
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                => target (TKS r1 sh) -> target (TKS r2 sh)
  sconcrete :: (GoodScalar r, KnownShS sh) => Nested.Shaped sh r -> target (TKS r sh)
  sfromR :: (GoodScalar r, KnownShS sh, KnownNat (Rank sh))
         => target (TKR r (Rank sh)) -> target (TKS r sh)

  -- ** No serviceable parts beyond this point ** --

  sscaleByScalar
    :: (GoodScalar r, KnownShS sh, KnownNat (Nested.Product sh))
    => target (TKS r '[]) -> target (TKS r sh) -> target (TKS r sh)
  sscaleByScalar s v = v * sreplicate0N s
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => Proxy m
          -> target (TKS r '[n, m]) -> target (TKS r '[n, m])
          -> target (TKS r '[n])  -- TODO: generalize
  sdot1In _ t u = ssum $ str (t * u)

  -- Primal/dual things.
  sfromPrimal :: (GoodScalar r, KnownShS sh)
            => PrimalOf target (TKS r sh) -> target (TKS r sh)
  sprimalPart :: (GoodScalar r, KnownShS sh)
              => target (TKS r sh) -> PrimalOf target (TKS r sh)
  sdualPart :: (GoodScalar r, KnownShS sh)
            => target (TKS r sh) -> DualOf target (TKS r sh)
  sD :: (GoodScalar r, KnownShS sh)
     => PrimalOf target (TKS r sh) -> DualOf target (TKS r sh)
     -> target (TKS r sh)
  sScale :: (GoodScalar r, KnownShS sh)
         => PrimalOf target (TKS r sh) -> DualOf target (TKS r sh)
         -> DualOf target (TKS r sh)

  tpair :: (TensorKind x, TensorKind z)
         => target x -> target z
         -> target (TKProduct x z)
  tproject1 :: (TensorKind x, TensorKind z)
            => target (TKProduct x z)
            -> target x
  tproject2 :: (TensorKind x, TensorKind z)
            => target (TKProduct x z)
            -> target z
  dshape :: target TKUntyped -> VoidHVector
  tshapeFull :: STensorKindType y -> target y
             -> TensorKindFull y
  tcond :: IfF target
        => STensorKindType y
        -> BoolOf target
        -> target y -> target y
        -> target y
  tfromPrimal :: STensorKindType y
            -> PrimalOf target y
            -> target y
  tprimalPart :: STensorKindType y
              -> target y
              -> PrimalOf target y
  tdualPart :: STensorKindType y
            -> target y
            -> DualOf target y
  tD :: STensorKindType y
     -> PrimalOf target y -> DualOf target y
     -> target y
  dmkHVector :: HVector target -> target TKUntyped
  dlambda :: (TensorKind x, TensorKind z)
          => TensorKindFull x -> HFun x z -> HFunOf target x z
  dHApply :: (TensorKind x, TensorKind z)
          => HFunOf target x z -> target x
          -> target z
  dunHVector :: target TKUntyped -> HVector target
    -- ^ Warning: this operation easily breaks sharing.
    -- The operation can't usually be implemented to preserve
    -- sharing, because it's type signature doesn't fit the let
    -- and share operations available.
  dbuild1 :: SNat k
          -> (IntOf target -> target TKUntyped)  -- sh_i
          -> target TKUntyped  -- k ': sh_i
  dzipWith1 :: SNat k
            -> (HVector target -> target TKUntyped)
                 -- ^ both hVectors can have arbitrary tensors in them
            -> HVector target -> target TKUntyped
                 -- ^ each hVector has the same tensor shapes and scalar types
                 -- as its corresponding hVector above, except for the extra
                 -- outermost dimension k
  dzipWith1 k f u =
    dbuild1 @target k (f . index1HVectorF rshape sshape rindex sindex u)
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
          (TensorKind x, GoodScalar r, KnownNat n)
       => (forall f. ADReady f => f x -> f (TKR r n))
       -> TensorKindFull x
       -> target x
       -> target (ADTensorKind x)
  rrev f ftk | Dict <- lemTensorKindOfAD (stensorKind @x) =
    \ !es -> dHApply (drev @target ftk $ HFun f) es
  -- We can't get sh from anywhere, so this is not possible:
  -- rrev f shs es = rrevDt f shs es (rreplicate0N sh 1)
  rrevDt :: forall x r n.
            (TensorKind x, GoodScalar r, KnownNat n)
         => (forall f. ADReady f => f x -> f (TKR r n))
         -> TensorKindFull x
         -> target x
         -> target (ADTensorKind (TKR r n))  -- ^ incoming cotangent (dt)
         -> target (ADTensorKind x)
  rrevDt f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
               , Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    \ !es !dt -> dHApply (drevDt @target ftk $ HFun f)
                         (tpair dt es)
  rfwd :: forall x r n.
          (TensorKind x, GoodScalar r, KnownNat n)
       => (forall f. ADReady f => f x -> f (TKR r n))
       -> TensorKindFull x
       -> target x
       -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> target (ADTensorKind (TKR r n))
  rfwd f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
             , Dict <- lemTensorKindOfAD (stensorKind @(TKR r n)) =
    \ !es !ds -> dHApply (dfwd @target ftk $ HFun f)
                         (tpair ds es)
  srev :: forall x r sh.
          ( TensorKind x, GoodScalar r, KnownShS sh
          , ADTensorKind (TKS r sh) ~ TKS r sh )
       => (forall f. ADReady f => f x -> f (TKS r sh))
       -> TensorKindFull x
       -> target x
       -> target (ADTensorKind x)
  srev f ftk es = srevDt f ftk es (srepl 1)
  srevDt :: forall x r sh.
            (TensorKind x, GoodScalar r, KnownShS sh)
         => (forall f. ADReady f => f x -> f (TKS r sh))
         -> TensorKindFull x
         -> target x
         -> target (ADTensorKind (TKS r sh))  -- ^ incoming cotangent (dt)
         -> target (ADTensorKind x)
  srevDt f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
               , Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    \ !es !dt -> dHApply (drevDt @target ftk $ HFun f)
                         (tpair dt es)
  sfwd :: forall x r sh.
          (TensorKind x, GoodScalar r, KnownShS sh)
       => (forall f. ADReady f => f x -> f (TKS r sh))
       -> TensorKindFull x
       -> target x
       -> target (ADTensorKind x)  -- ^ incoming tangent (ds)
       -> target (ADTensorKind (TKS r sh))
  sfwd f ftk | Dict <- lemTensorKindOfAD (stensorKind @x)
             , Dict <- lemTensorKindOfAD (stensorKind @(TKS r sh)) =
    \ !es !ds -> dHApply (dfwd @target ftk $ HFun f)
                         (tpair ds es)
  -- If the result of the argument function is not a scalar,
  -- the result of this operation is the gradient of a function that additionally
  -- sums all elements of the result. If all elements are equally important
  -- for optimization, this may be exactly what is needed for gradient descent,
  -- unless there are floats of different resolution among the elements and,
  -- e.g., one wants to compensate for that.
  --
  -- These methods (and dlambda) producing HFunOf is analogous to dmkHVector
  -- producing target TKUntyped instead of HVector and it's exactly what is needed as arguments
  -- of dmapAccumRDer
  drev
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target x (ADTensorKind x)  -- a |-> da
  drevDt
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind z) x) (ADTensorKind x)
                 -- [db, a] |-> da
  dfwd
    :: (TensorKind x, TensorKind z)
    => TensorKindFull x  -- shape of a and da
    -> HFun x z  -- a |-> b
    -> HFunOf target (TKProduct (ADTensorKind x) x) (ADTensorKind z)
                 -- [da, a] |-> db
  -- | A strict left fold.
  rfold
    :: forall rn rm n m.
       (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
    => (forall f. ADReady f => f (TKR rn n) -> f (TKR rm m) -> f (TKR rn n))
    -> target (TKR rn n)  -- ^ initial value
    -> target (TKR rm (1 + m))  -- ^ iteration is over the outermost dimension
    -> target (TKR rn n)
  rfold f acc0 es =
    let shm :: IShR m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rfold: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      tproject1
        (dmapAccumL (Proxy @target)
           snat
           (FTKR @rn sh)
           (FTKUntyped V.empty)
           (FTKR @rm shm)
           (let g :: forall f. ADReady f
                  => f (TKR rn n) -> f (TKR rm m)
                  -> f (TKProduct (TKR rn n) TKUntyped)
                g !acc !e =
                  tpair (f acc e)
                         (dmkHVector V.empty)
            in g)
           acc0
           es)
  -- | A strict left scan.
  rscan
    :: forall rn rm n m.
       (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
    => (forall f. ADReady f => f (TKR rn n) -> f (TKR rm m) -> f (TKR rn n))
    -> target (TKR rn n)
    -> target (TKR rm (1 + m))
    -> target (TKR rn (1 + n))
  rscan f acc0 es =
    let shm :: IShR m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rscan: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      let bs =
            tproject2
            $ dmapAccumL (Proxy @target)
                snat
                (FTKR @rn sh)
                (FTKR @rn sh)
                (FTKR @rm shm)
                (let g :: forall f. ADReady f
                       => f (TKR rn n) -> f (TKR rm m)
                       -> f (TKProduct (TKR rn n) (TKR rn n))
                     g !acc !e = tlet (f acc e) $ \ !res -> tpair res res
                 in g)
                acc0
                es
      in rappend (rfromList [acc0]) bs
  -- | A strict left fold.
  sfold
    :: forall rn rm sh shm k.
       (GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k)
    => (forall f. ADReady f => f (TKS rn sh) -> f (TKS rm shm) -> f (TKS rn sh))
    -> target (TKS rn sh)
    -> target (TKS rm (k ': shm))
    -> target (TKS rn sh)
  sfold f acc0 es =
    tproject1
      (dmapAccumL (Proxy @target)
         (SNat @k)
         (FTKS @rn @sh knownShS)
         (FTKUntyped V.empty)
         (FTKS @rm @shm knownShS)
         (let g :: forall f. ADReady f
                => f (TKS rn sh) -> f (TKS rm shm)
                -> f (TKProduct (TKS rn sh) TKUntyped)
              g !acc !e =
                tpair (f acc e)
                       (dmkHVector V.empty)
          in g)
         acc0
         es)
  sscan
    :: forall rn rm sh shm k.
       (GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k)
    => (forall f. ADReady f => f (TKS rn sh) -> f (TKS rm shm) -> f (TKS rn sh))
    -> target (TKS rn sh)
    -> target (TKS rm (k ': shm))
    -> target (TKS rn (1 + k ': sh))
  sscan f acc0 es =
    let bs =
          tproject2
          $ dmapAccumL (Proxy @target)
             (SNat @k)
             (FTKS @rn @sh knownShS)
             (FTKS @rn @sh knownShS)
             (FTKS @rm @shm knownShS)
             (let g :: forall f. ADReady f
                    => f (TKS rn sh) -> f (TKS rm shm)
                    -> f (TKProduct (TKS rn sh) (TKS rn sh))
                  g !acc !e = tlet (f acc e) $ \ !res -> tpair res res
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
  --
  -- If the same argument functions are passed to many dmapAccum calls, as in
  -- > let f = ... in ... (dmapAccumR ... f ...) ... (dmapAccumL ... f ...)
  -- extra care is needed to prevent double derivative computation.
  -- One needs to use dmapAccumRDer manually as in (simplified)
  -- > let f = ...; df = dfwd f; rf = drev f
  -- > in ... (dmapAccumRDer f df rf ...) ... (dmapAccumLDer f df rf ...)
  dmapAccumR
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> (forall f. ADReady f
        => f accShs -> f eShs
        -> f (TKProduct accShs bShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumR proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => f (TKProduct accShs eShs)
           -> f (TKProduct accShs bShs)
        fl !args = tlet args $ \ !args1 ->
                     f (tproject1 args1) (tproject2 args1)
    in dmapAccumRDer proxy k accShs bShs eShs
                     (dlambda @target shs (HFun fl))
                     (dfwd @target shs $ HFun fl)
                     (drevDt @target shs $ HFun fl)
                     acc0 es
  dmapAccumRDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> TensorKindFull accShs  -- ^ shapes of acc, the accumulator
    -> TensorKindFull bShs -- ^ shapes of b
    -> TensorKindFull eShs -- ^ shapes of e
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
  dmapAccumL
    :: forall k accShs bShs eShs.
       (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> (forall f. ADReady f
        => f accShs -> f eShs
        -> f (TKProduct accShs bShs))
    -> target accShs
    -> target (BuildTensorKind k eShs)
    -> target (TKProduct accShs (BuildTensorKind k bShs))
  dmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = FTKProduct accShs eShs
        fl :: forall f. ADReady f
           => f (TKProduct accShs eShs)
           -> f (TKProduct accShs bShs)
        fl !args = tlet args $ \ !args1 ->
                     f (tproject1 args1) (tproject2 args1)
    in dmapAccumLDer proxy k accShs bShs eShs
                     (dlambda @target shs (HFun fl))
                     (dfwd @target shs $ HFun fl)
                     (drevDt @target shs $ HFun fl)
                     acc0 es
  dmapAccumLDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => Proxy target
    -> SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
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

tunit :: BaseTensor target
      => target TKUnit
tunit = rmkRepScalar $ rscalar ()

rfromD :: forall r n target.
          (BaseTensor target, GoodScalar r, KnownNat n)
       => DynamicTensor target -> target (TKR r n)
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

sfromD :: forall r sh target.
          (BaseTensor target, GoodScalar r, KnownShS sh)
       => DynamicTensor target -> target (TKS r sh)
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

rscalar :: (GoodScalar r, BaseTensor target) => r -> target (TKR r 0)
rscalar = rconcrete . Nested.rscalar

rrepl :: forall r n target. (GoodScalar r, KnownNat n, BaseTensor target)
      => [Int] -> r -> target (TKR r n)
rrepl sh = rconcrete . Nested.rreplicateScal (fromList sh)

ringestData :: forall target r n.
              (GoodScalar r, KnownNat n, BaseTensor target)
           => [Int] -> [r] -> target (TKR r n)
ringestData sh l = rconcrete $ Nested.rfromListPrimLinear (listToShape sh) l

ingestData :: forall target r sh.
              (GoodScalar r, KnownShS sh, BaseTensor target)
           => [r] -> target (TKS r sh)
ingestData l= sconcrete $ Nested.sfromListPrimLinear knownShS l

sscalar :: (GoodScalar r, BaseTensor target) => r -> target (TKS r '[])
sscalar = sconcrete . Nested.sscalar

srepl :: forall sh r target. (GoodScalar r, KnownShS sh, BaseTensor target)
      => r -> target (TKS r sh)
srepl =
  sconcrete . Nested.sreplicateScal knownShS
  -- TODO: the following simplifies better, because the replication is not
  -- hidden at low level:
  -- Dict <- lemKnownNatSize (knownShS @sh) =
  --   sreplicate0N . sscalar
  -- though we could also look at the low level in @isSmall@ and mark
  -- replicated fromPrimals as small

xrepl :: forall sh r target.
         (GoodScalar r, KnownShX sh, BaseTensor target)
      => IShX sh -> r -> target (TKX r sh)
xrepl sh =
  xconcrete . Nested.mreplicateScal sh

nullRep :: forall y target. (TensorKind y, BaseTensor target)
        => target y -> Bool
nullRep t = case stensorKind @y of
  STKScalar{} -> False
  STKR{} -> False
  STKS{} -> False
  STKX{} -> False
  STKProduct{} -> False
  STKUntyped -> null $ dunHVector t

mapDynamic2
  :: (BaseTensor f1, BaseTensor f2)
  => (forall r n. (GoodScalar r, KnownNat n)
      => f1 (TKR r n) -> f2 (TKR r n)
      -> g (TKR r n))
  -> (forall r sh. (GoodScalar r, KnownShS sh)
      => f1 (TKS r sh) -> f2 (TKS r sh)
      -> g (TKS r sh))
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

-- These are user-accessible, so the constraint is `ADReady`, which means
-- lets, but no shares.
type role HFun nominal nominal
newtype HFun (x :: TensorKindType) (z :: TensorKindType) =
  HFun {unHFun :: forall f. ADReady f
               => f x -> f z}

instance Show (HFun x y) where
  show _ = "<lambda>"


-- * The giga-constraint

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
  , IfF target
  , EqF target
  , OrdF target
  , BaseTensor target
  , CRanked target Show
  , Show (target TKUntyped)
  )
