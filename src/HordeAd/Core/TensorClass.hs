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
    ShapeInt, ShapeS
    -- * The tensor classes
  , RankedTensor(..), ShapedTensor(..), HVectorTensor(..), HFun(..)
  , rfromD, sfromD, rscalar, ingestData, sscalar, srepl
    -- * The giga-constraint
  , ADReady, ADReadyBoth, ADReadyR, ADReadyS
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Constraint, Type)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, OrderingI (..), cmpNat, sameNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Vector)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Data.Array.Mixed.Internal.Arith as Nested.Internal.Arith
import qualified Data.Array.Mixed.Permutation as Permutation
import qualified Data.Array.Mixed.Shape as X
import qualified Data.Array.Mixed.Types as X

import           HordeAd.Core.HVector
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import           HordeAd.Util.ShapedList
  (IndexSh, IntSh, ShapeS, consIndex, pattern (:.$), pattern ZIS)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Ranked tensor class definition

type TensorSupports :: (Type -> Constraint) -> TensorType ty -> Constraint
type TensorSupports c f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => (c r, c (Vector r)) => c (f r y)

type TensorSupports2 :: (Type -> Constraint) -> (Type -> Constraint) -> TensorType ty -> Constraint
type TensorSupports2 c1 c2 f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => (c1 r, c1 (Vector r)) => c2 (f r y)

type TensorSupports3 :: (Type -> Constraint) -> (Type -> Constraint) -> TensorType ty -> Constraint
type TensorSupports3 c1 c2 f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => c1 r => c2 (f r y)

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Integral (IntOf ranked), CRanked ranked Num
      , TensorSupports3 RealFloatAndFloatElt RealFloat ranked
          -- TODO: no idea why FloatElt here is needed
      , TensorSupports Integral ranked )
      => RankedTensor (ranked :: RankedTensorType) where

  rlet :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2)
       => ranked r n -> (ranked r n -> ranked r2 m)
       -> ranked r2 m
  rlet a f = f a

  -- Integer codomain
  rshape :: (GoodScalar r, KnownNat n) => ranked r n -> ShapeInt n
  rrank :: forall r n. (GoodScalar r, KnownNat n) => ranked r n -> Int
  rrank _ = valueOf @n
  rsize :: (GoodScalar r, KnownNat n) => ranked r n -> Int
  rsize = sizeShape . rshape
  rlength :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> Int
  rlength v = case rshape v of
    ZSR -> error "tlength: impossible pattern needlessly required"
    k :$: _ -> k
  rminIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  rmaxIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  rfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => ranked r n -> ranked r2 n
  riota :: ranked r 1  -- 0, 1 .. infinity
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
  rmatmul2 :: GoodScalar r
           => ranked r 2 -> ranked r 2 -> ranked r 2
-- How to generalize to tmatmul (#69)?
-- Just rmatmul2 the two outermost dimensions?
-- rmatmul2 m1 m2 = rmap1 (rmatvecmul (rtr m2)) m1
-- rmatmul2 m1 m2 = rbuild1 (rlength m1) (\i -> rmatvecmul (rtr m2) (m1 ! [i]))
  rmatmul2 m1 m2 = case rshape m2 of
    _ :$: width2 :$: ZSR -> rsum (rtranspose [2,1,0] (rreplicate width2 m1)
                               * rtranspose [1,0] (rreplicate (rlength m1) m2))
    _ -> error "impossible pattern needlessly required"
  rscatter :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> ranked r (m + n)
           -> (IndexOf ranked m -> IndexOf ranked p)
           -> ranked r (p + n)
  rscatter1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
            => ShapeInt (p + n) -> ranked r (1 + n)
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
    -- goring through strict vectors, because laziness is risky with impurity
  rfromList0N :: (GoodScalar r, KnownNat n)
              => ShapeInt n -> [ranked r 0] -> ranked r n
  rfromList0N sh = rfromVector0N sh . V.fromList
  -- This is morally non-empty strict vectors:
  rfromVector :: (GoodScalar r, KnownNat n)
              => Data.Vector.Vector (ranked r n) -> ranked r (1 + n)
  rfromVector0N :: (GoodScalar r, KnownNat n)
                => ShapeInt n -> Data.Vector.Vector (ranked r 0) -> ranked r n
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
               => ShapeInt n -> ranked r 0 -> ranked r n
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
             => Permutation -> ranked r n -> ranked r n
  rflatten :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 1
  rflatten u = rreshape (flattenShape $ rshape u) u
  rreshape :: (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ranked r n -> ranked r m
  rbuild :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
         => ShapeInt (m + n) -> (IndexOf ranked m -> ranked r n)
         -> ranked r (m + n)
  rbuild sh0 f0 =
    let buildSh :: ShapeInt m1 -> (IndexOf ranked m1 -> ranked r n)
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
  rmap0N :: (GoodScalar r, GoodScalar r2, KnownNat n)
         => (ranked r 0 -> ranked r2 0) -> ranked r n -> ranked r2 n
  rmap0N f v = rbuild (rshape v) (f . rindex0 v)
  rzipWith :: ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownNat n1, KnownNat n2, KnownNat n )
           => ShapeInt (m + n)
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
            => ShapeInt (m + n)
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
            => ShapeInt (m + n)
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
          => ShapeInt (m + n) -> ranked r (p + n)
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> ranked r (m + n)
  rgather1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
           => Int -> ranked r (p + n)
           -> (IntOf ranked -> IndexOf ranked p)
           -> ranked r (1 + n)
  rgather1 k v f = rgather @ranked @r @1 (k :$: dropShape (rshape v)) v
                           (\(i :.: ZIR) -> f i)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => ranked r1 n -> ranked r2 n
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => ranked r1 n -> ranked r2 n
  rconst :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  rletHVectorIn :: (KnownNat n, GoodScalar r)
                => HVectorOf ranked
                -> (HVector ranked -> ranked r n)
                -> ranked r n
  rletHFunIn :: (KnownNat n, GoodScalar r)
             => HFunOf ranked
             -> (HFunOf ranked -> ranked r n)
             -> ranked r n
  rfromS :: (GoodScalar r, KnownShS sh)
         => ShapedOf ranked r sh -> ranked r (Sh.Rank sh)
  -- Prevents wrong shape in @0@ with ranked (but not shaped) tensors
  -- at any rank greater than zero.
  rzero :: (GoodScalar r, KnownNat n)
        => ShapeInt n -> ranked r n
  rzero sh = rreplicate0N sh 0

  -- ** No serviceable parts beyond this point ** --

  rscaleByScalar :: (GoodScalar r, KnownNat n)
                 => ranked r 0 -> ranked r n -> ranked r n
  rscaleByScalar s v = v * rreplicate0N (rshape v) s
  rsumIn :: (GoodScalar r, KnownNat n) => ranked r (2 + n) -> ranked r (1 + n)
  rsumIn = rsum . rtr
    -- TODO: generalize, replace by stride analysis, etc.
  rdot1In :: GoodScalar r => ranked r 2 -> ranked r 2 -> ranked r 1
  rdot1In t u = rsumIn (t * u)
    -- TODO: generalize, replace by stride analysis, etc.
  rshare :: KnownNat n => ranked r n -> ranked r n
  rshare = id

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


-- * Shaped tensor class definition

class (RealFloat r, RealFloat (Vector r), Nested.Internal.Arith.FloatElt r)
      => RealFloatAndFloatElt r
instance (RealFloat r, RealFloat (Vector r), Nested.Internal.Arith.FloatElt r)
         => RealFloatAndFloatElt r

class ( Integral (IntOf shaped), CShaped shaped Num
      , TensorSupports3 RealFloatAndFloatElt Floating shaped
      , TensorSupports3 RealFloatAndFloatElt RealFloatF shaped
      , TensorSupports2 Integral IntegralF shaped )
      => ShapedTensor (shaped :: ShapedTensorType) where

  slet :: (KnownShS sh, KnownShS sh2, GoodScalar r, GoodScalar r2)
       => shaped r sh -> (shaped r sh -> shaped r2 sh2)
       -> shaped r2 sh2
  slet a f = f a

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, KnownShS sh)
         => shaped r sh -> ShS sh
  sshape _ = knownShS @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (Sh.Rank sh))
        => shaped r sh -> Int
  srank _ = valueOf @(Sh.Rank sh)
  ssize :: forall sh r. (GoodScalar r, KnownShS sh) => shaped r sh -> Int
  ssize _ = sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => shaped r (n ': sh) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Sh.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Sh.Init (n ': sh))
  smaxIndex :: ( GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat n
               , KnownShS (Sh.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Sh.Init (n ': sh))
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownShS sh)
         => shaped r sh -> shaped r2 sh
    -- not IntSh, because the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => shaped r '[n]  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( GoodScalar r, KnownShS sh1, KnownShS sh2
                  , KnownShS (sh1 X.++ sh2) )
               => shaped r (sh1 X.++ sh2) -> IndexSh shaped sh1
               -> shaped r sh2
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, KnownShS sh1)
          => shaped r sh1 -> IndexSh shaped sh1
          -> shaped r '[]
  sindex0 = gcastWith (unsafeCoerce Refl :: sh1 X.++ '[] :~: sh1)
              sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
       => shaped r (n ': sh) -> shaped r sh
  ssum0 :: (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
        => shaped r sh -> shaped r '[]
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
        => shaped r sh -> shaped r sh -> shaped r '[]
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ consIndex i ZIS))
  smatmul2 :: forall r n m p. (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Permutation.makePerm @'[2, 1, 0]) (sreplicate @shaped @p m1)
          * stranspose (Permutation.makePerm @'[1, 0]) (sreplicate @shaped @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownShS (Sh.Take p sh)
       , KnownShS (Sh.Drop p sh), KnownShS (sh2 X.++ Sh.Drop p sh) )
    => shaped r (sh2 X.++ Sh.Drop p sh)
    -> (IndexSh shaped sh2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownShS (Sh.Take p sh)
       , KnownShS (Sh.Drop p sh) )
    => shaped r (n2 ': Sh.Drop p sh)
    -> (IntSh shaped n2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (ShapedList.unconsContIndex f)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (GoodScalar r, KnownNat n, KnownShS sh)
            => NonEmpty (shaped r sh) -> shaped r (n ': sh)
  sfromList = sfromVector . V.fromList . NonEmpty.toList
  sfromList0N :: forall r sh.
                 (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
              => [shaped r '[]] -> shaped r sh
  sfromList0N = sfromVector0N . V.fromList
  -- This is morally non-empty strict vectors:
  sfromVector :: (GoodScalar r, KnownNat n, KnownShS sh)
              => Data.Vector.Vector (shaped r sh) -> shaped r (n ': sh)
  sfromVector0N :: forall r sh.
                   (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
                => Data.Vector.Vector (shaped r '[])
                -> shaped r sh
  sfromVector0N = sreshape @shaped @r @'[Sh.Size sh] @sh . sfromVector
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
                  (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
               => shaped r '[] -> shaped r sh
  sreplicate0N = sreshape @shaped @r @'[Sh.Size sh] @sh
                 . sreplicate @shaped @(Sh.Size sh)
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
         , KnownNat (Sh.Rank sh) )
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose (Permutation.makePerm @'[1, 0])
  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , KnownNat (Sh.Rank sh), KnownShS (Sh.Permute perm sh)
                , Sh.Rank perm <= Sh.Rank sh, GoodScalar r )
             => Permutation.Perm perm -> shaped r sh
             -> shaped r (Sh.Permute perm sh)
  sflatten :: (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
           => shaped r sh -> shaped r '[Sh.Size sh]
  sflatten = sreshape
  sreshape :: ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Sh.Size sh ~ Sh.Size sh2 )
           => shaped r sh -> shaped r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh. (GoodScalar r, KnownShS sh, KnownShS (Sh.Take m sh))
         => (IndexSh shaped (Sh.Take m sh) -> shaped r (Sh.Drop m sh))
         -> shaped r sh
  sbuild =
    let buildSh
          :: forall sh1.
             ShS sh1 -> ShS (sh1 X.++ Sh.Drop m sh)
          -> (IndexSh shaped sh1 -> shaped r (Sh.Drop m sh))
          -> shaped r (sh1 X.++ Sh.Drop m sh)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSS, _) -> f ZIS
          ((:$$) SNat sh2, (:$$) _ sh2m) | Dict <- sshapeKnown sh2m ->
            let g i = buildSh sh2 sh2m (f . consIndex i)
            in sbuild1 g
    in gcastWith (unsafeCoerce Refl
                  :: sh :~: Sh.Take m sh X.++ Sh.Drop m sh)
       $ buildSh (knownShS @(Sh.Take m sh))
                 (knownShS @sh)
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntSh shaped n -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: forall r r2 m sh.
          ( GoodScalar r, GoodScalar r2, KnownNat m
          , KnownShS sh, KnownShS (Sh.Take m sh), KnownShS (Sh.Drop m sh) )
       => (shaped r (Sh.Drop m sh) -> shaped r2 (Sh.Drop m sh))
       -> shaped r sh -> shaped r2 sh
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: Sh.Take m sh X.++ Sh.Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r r2 sh n.
           (GoodScalar r, GoodScalar r2, KnownNat n, KnownShS sh)
        => (shaped r sh -> shaped r2 sh)
        -> shaped r (n ': sh) -> shaped r2 (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ consIndex i ZIS))
  smap0N :: forall r r2 sh.
            (GoodScalar r, GoodScalar r2, KnownShS sh, KnownNat (Sh.Rank sh))
         => (shaped r '[] -> shaped r2 '[]) -> shaped r sh -> shaped r2 sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @r2 @(Sh.Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, KnownShS sh1, KnownShS sh2, KnownShS sh
              , KnownShS (Sh.Take m sh), KnownShS (Sh.Drop m sh1)
              , KnownShS (Sh.Drop m sh2), KnownShS (Sh.Drop m sh)
              , sh1 ~ Sh.Take m sh X.++ Sh.Drop m sh1
              , sh2 ~ Sh.Take m sh X.++ Sh.Drop m sh2 )
           => (shaped r1 (Sh.Drop m sh1)
               -> shaped r2 (Sh.Drop m sh2)
               -> shaped r (Sh.Drop m sh))
           -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n, KnownShS sh1, KnownShS sh2, KnownShS sh )
            => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh)
            -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
            -> shaped r (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ consIndex i ZIS)
                                     (v !$ consIndex i ZIS))
  szipWith0N :: forall r1 r2 r sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r
                , KnownShS sh, KnownNat (Sh.Rank sh) )
             => (shaped r1 '[] -> shaped r2 '[] -> shaped r '[])
             -> shaped r1 sh -> shaped r2 sh -> shaped r sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Sh.Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  szipWith3 :: forall r1 r2 r3 r m sh1 sh2 sh3 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
               , KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh
               , KnownShS (Sh.Take m sh), KnownShS (Sh.Drop m sh1)
               , KnownShS (Sh.Drop m sh2), KnownShS (Sh.Drop m sh3)
               , KnownShS (Sh.Drop m sh)
               , sh1 ~ Sh.Take m sh X.++ Sh.Drop m sh1
               , sh2 ~ Sh.Take m sh X.++ Sh.Drop m sh2
               , sh3 ~ Sh.Take m sh X.++ Sh.Drop m sh3 )
            => (shaped r1 (Sh.Drop m sh1)
                -> shaped r2 (Sh.Drop m sh2)
                -> shaped r3 (Sh.Drop m sh3)
                -> shaped r (Sh.Drop m sh))
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
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ consIndex i ZIS)
                                        (v !$ consIndex i ZIS)
                                        (w !$ consIndex i ZIS))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , KnownShS sh, KnownNat (Sh.Rank sh) )
              => (shaped r1 '[] -> shaped r2 '[] -> shaped r3 '[]
                  -> shaped r '[])
              -> shaped r1 sh -> shaped r2 sh -> shaped r3 sh -> shaped r sh
  szipWith30N f u v w =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Sh.Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix))
  szipWith4 :: forall r1 r2 r3 r4 r m sh1 sh2 sh3 sh4 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
               , GoodScalar r, KnownNat m
               , KnownShS sh1, KnownShS sh2, KnownShS sh3, KnownShS sh4
               , KnownShS sh
               , KnownShS (Sh.Take m sh), KnownShS (Sh.Drop m sh1)
               , KnownShS (Sh.Drop m sh2), KnownShS (Sh.Drop m sh3)
               , KnownShS (Sh.Drop m sh4), KnownShS (Sh.Drop m sh)
               , sh1 ~ Sh.Take m sh X.++ Sh.Drop m sh1
               , sh2 ~ Sh.Take m sh X.++ Sh.Drop m sh2
               , sh3 ~ Sh.Take m sh X.++ Sh.Drop m sh3
               , sh4 ~ Sh.Take m sh X.++ Sh.Drop m sh4 )
            => (shaped r1 (Sh.Drop m sh1)
                -> shaped r2 (Sh.Drop m sh2)
                -> shaped r3 (Sh.Drop m sh3)
                -> shaped r4 (Sh.Drop m sh4)
                -> shaped r (Sh.Drop m sh))
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
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ consIndex i ZIS)
                                          (v !$ consIndex i ZIS)
                                          (w !$ consIndex i ZIS)
                                          (x !$ consIndex i ZIS))
  szipWith40N :: forall r1 r2 r3 r4 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r, KnownShS sh, KnownNat (Sh.Rank sh) )
              => (shaped r1 '[] -> shaped r2 '[] -> shaped r3 '[]
                  -> shaped r4 '[] -> shaped r '[])
              -> shaped r1 sh -> shaped r2 sh -> shaped r3 sh -> shaped r4 sh
              -> shaped r sh
  szipWith40N f u v w x =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Sh.Rank sh) (\ix -> f (sindex0 u ix)
                                                (sindex0 v ix)
                                                (sindex0 w ix)
                                                (sindex0 x ix))
  sgather
    :: forall r sh2 p sh.
       ( GoodScalar r, KnownShS sh2, KnownShS sh, KnownShS (Sh.Take p sh)
       , KnownShS (Sh.Drop p sh), KnownShS (sh2 X.++ Sh.Drop p sh) )
    => shaped r sh
    -> (IndexSh shaped sh2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r (sh2 X.++ Sh.Drop p sh)
  sgather1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, KnownShS sh, KnownShS (Sh.Take p sh)
       , KnownShS (Sh.Drop p sh) )
    => shaped r sh
    -> (IntSh shaped n2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r (n2 ': Sh.Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (ShapedList.unconsContIndex f)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownShS sh)
        => shaped r1 sh -> shaped r2 sh
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                => shaped r1 sh -> shaped r2 sh
  sconst :: (GoodScalar r, KnownShS sh) => OS.Array sh r -> shaped r sh
  sletHVectorIn :: (KnownShS sh, GoodScalar r)
                => HVectorOf (RankedOf shaped)
                -> (HVector (RankedOf shaped) -> shaped r sh)
                -> shaped r sh
  sletHFunIn :: (KnownShS sh, GoodScalar r)
             => HFunOf (RankedOf shaped)
             -> (HFunOf (RankedOf shaped) -> shaped r sh)
             -> shaped r sh
  sfromR :: (GoodScalar r, KnownShS sh, KnownNat (Sh.Rank sh))
         => RankedOf shaped r (Sh.Rank sh) -> shaped r sh

  -- ** No serviceable parts beyond this point ** --

  sscaleByScalar
    :: (GoodScalar r, KnownShS sh, KnownNat (Sh.Size sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v * sreplicate0N s
  ssumIn :: ( GoodScalar r, KnownShS sh, KnownNat n, KnownNat m
            , KnownNat (Sh.Rank sh) )
         => shaped r (n ': m ': sh) -> shaped r (n ': sh)
  ssumIn = ssum . str
    -- TODO: generalize, replace by stride analysis, etc.
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => shaped r '[n, m] -> shaped r '[n, m] -> shaped r '[n]
  sdot1In t u = ssumIn (t * u)
    -- TODO: generalize, replace by stride analysis, etc.
  sshare :: KnownShS sh => shaped r sh -> shaped r sh
  sshare = id

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
  dmkHVector :: HVector ranked -> HVectorOf ranked
  dlambda :: [VoidHVector] -> HFun -> HFunOf ranked
  dHApply :: HFunOf ranked -> [HVector ranked] -> HVectorOf ranked
  dunHVector :: HVectorOf ranked -> HVector ranked
    -- ^ Warning: this operation easily breaks sharing.
  dletHVectorInHVector
    :: HVectorOf ranked
    -> (HVector ranked -> HVectorOf ranked)
    -> HVectorOf ranked
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
    :: HFunOf ranked
    -> (HFunOf ranked -> HVectorOf ranked)
    -> HVectorOf ranked
  rletInHVector :: (GoodScalar r, KnownNat n)
                => ranked r n
                -> (ranked r n -> HVectorOf ranked)
                -> HVectorOf ranked
  sletInHVector :: (GoodScalar r, KnownShS sh)
                => shaped r sh
                -> (shaped r sh -> HVectorOf ranked)
                -> HVectorOf ranked
  dunlet :: HVectorOf ranked -> HVectorOf ranked
  dunlet = id
  dshare :: HVectorOf ranked -> HVectorOf ranked
  dshare = id
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
  -- The second argument is only used to determine tensor shapes
  -- and the third has to have the same shapes as the second.
  --
  -- The function argument needs to be quantified,
  -- because otherwise in the ADVal instance one could put an illegal
  -- InputR there, confusing the two levels of contangents.
  --
  -- These methods are in this class, because the types mention @ADReady@,
  -- which contains a @HVectorTensor@ constraint, so it's awkward to put
  -- the methods into @RankedTensor@, which shouldn't know
  -- about @HVectorTensor@.
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector ranked
       -> HVectorOf ranked
  -- We can't get sh from anywhere, so this is not possible:
  -- rrev f shs es = rrevDt f shs es (rreplicate0N sh 1)
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => HVector f -> f r n)
         -> VoidHVector
         -> HVector ranked
         -> ranked r n  -- ^ incoming cotangent (dt)
         -> HVectorOf ranked
  rrevDt f shs =
    let g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!x] = dmkHVector $ V.singleton $ DynamicRanked $ f x
        g _ = error "g: wrong number of arguments"
        h = drevDt @ranked shs (HFun g)
    in \es dt -> dHApply h [V.singleton $ DynamicRanked dt, es]
  rfwd :: (GoodScalar r, KnownNat n, RankedTensor ranked)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector ranked
       -> HVector ranked  -- ^ incoming tangent (ds)
       -> ranked r n
  rfwd f shs =
    let g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!x] = dmkHVector $ V.singleton $ DynamicRanked $ f x
        g _ = error "g: wrong number of arguments"
        h = dfwd @ranked shs (HFun g)
    in \es ds -> let hv = dHApply h [ds, es]
                 in rfromD $ dunHVector hv V.! 0
 srev :: forall r sh.
         ( GoodScalar r, KnownShS sh, shaped ~ ShapedOf ranked
          , ShapedTensor shaped )
       => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
       -> VoidHVector
       -> HVector ranked
       -> HVectorOf ranked
  srev f shs es = srevDt @_ @_ @r @sh f shs es (srepl 1)
  srevDt :: (GoodScalar r, KnownShS sh, shaped ~ ShapedOf ranked)
         => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
         -> VoidHVector
         -> HVector ranked
         -> shaped r sh
         -> HVectorOf ranked
  srevDt f shs =
    let g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!x] = dmkHVector $ V.singleton $ DynamicShaped $ f x
        g _ = error "g: wrong number of arguments"
        h = drevDt @ranked shs (HFun g)
    in \es dt -> dHApply h [V.singleton $ DynamicShaped dt, es]
  sfwd :: ( GoodScalar r, KnownShS sh, RankedTensor ranked, ShapedTensor shaped
          , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
       => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
       -> VoidHVector
       -> HVector ranked
       -> HVector ranked
       -> shaped r sh
  sfwd f shs =
    let g :: forall f. ADReady f => [HVector f] -> HVectorOf f
        g [!x] = dmkHVector $ V.singleton $ DynamicShaped $ f x
        g _ = error "g: wrong number of arguments"
        h = dfwd @ranked shs (HFun g)
    in \es ds -> let hv = dHApply h [ds, es]
                 in sfromD $ dunHVector hv V.! 0
  -- These methods (and dlambda) producing HFunOf is analogous to dmkHVector
  -- producing HVectorOf and it's exactly what is needed as arguments
  -- of dmapAccumRDer
  drevDt
    :: VoidHVector  -- shapes of a and da
    -> HFun  -- [HVector f] -> HVectorOf f
             -- a |-> b
    -> HFunOf ranked  -- [HVector f, HVector f] -> HVectorOf f
                      -- [db, a] |-> da
  dfwd
    :: VoidHVector  -- shapes of a and da
    -> HFun  -- [HVector f] -> HVectorOf f
             -- a |-> b
    -> HFunOf ranked  -- [HVector f, HVector f] -> HVectorOf f
                      -- [da, a] |-> db
  -- | A strict left fold.
  rfold
    :: forall rn rm n m.
       ( GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m
       , RankedTensor ranked )
    => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
    -> ranked rn n  -- ^ initial value
    -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
    -> ranked rn n
  rfold f acc0 es =
    let shm :: ShapeInt m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rscan: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      rletHVectorIn
        (dmapAccumL (Proxy @ranked)
           snat
           (V.singleton $ voidFromSh @rn sh)
           V.empty
           (V.singleton $ voidFromSh @rm shm)
           (let g :: forall f. ADReady f
                  => HVector f -> HVector f -> HVectorOf f
                g !acc !e =
                  rletInHVector
                    (f (rfromD $ acc V.! 0) (rfromD $ e V.! 0))
                    (dmkHVector . V.singleton . DynamicRanked)
            in g)
           (dmkHVector $ V.singleton $ DynamicRanked acc0)
           (dmkHVector $ V.singleton $ DynamicRanked es))
        (\res -> rfromD $ res V.! 0)
  -- | A strict left scan.
  rscan
    :: forall rn rm n m.
       ( GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m
       , RankedTensor ranked )
    => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
    -> ranked rn n
    -> ranked rm (1 + m)
    -> ranked rn (1 + n)
  rscan f acc0 es =
    let shm :: ShapeInt m
        (width, shm) = case rshape es of
          width2 :$: shm2 -> (width2, shm2)
          ZSR -> error "rscan: impossible pattern needlessly required"
        sh = rshape acc0
    in withSNat width $ \snat ->
      rletHVectorIn
        (dmapAccumL (Proxy @ranked)
           snat
           (V.singleton $ voidFromSh @rn sh)
           (V.singleton $ voidFromSh @rn sh)
           (V.singleton $ voidFromSh @rm shm)
           (let g :: forall f. ADReady f
                  => HVector f -> HVector f -> HVectorOf f
                g !acc !e =
                  rletInHVector
                    (f (rfromD $ acc V.! 0) (rfromD $ e V.! 0))
                    (\res -> dmkHVector
                             $ V.fromList [ DynamicRanked res
                                          , DynamicRanked res ])
            in g)
           (dmkHVector $ V.singleton $ DynamicRanked acc0)
           (dmkHVector $ V.singleton $ DynamicRanked es))
        (\res -> rappend (rfromList [acc0]) (rfromD $ res V.! 1))
  -- | A strict left fold.
  sfold
    :: forall rn rm sh shm k.
       ( GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k
       , ShapedTensor shaped
       , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
    => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
    -> shaped rn sh
    -> shaped rm (k ': shm)
    -> shaped rn sh
  sfold f acc0 es =
    sletHVectorIn
      (dmapAccumL (Proxy @ranked)
         (SNat @k)
         (V.singleton $ voidFromShS @rn @sh)
         V.empty
         (V.singleton $ voidFromShS @rm @shm)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> HVectorOf f
              g !acc !e =
                sletInHVector
                  (f (sfromD $ acc V.! 0) (sfromD $ e V.! 0))
                  (dmkHVector . V.singleton . DynamicShaped)
          in g)
         (dmkHVector $ V.singleton $ DynamicShaped acc0)
         (dmkHVector $ V.singleton $ DynamicShaped es))
      (\res -> sfromD $ res V.! 0)
  sscan
    :: forall rn rm sh shm k.
       ( GoodScalar rn, GoodScalar rm, KnownShS sh, KnownShS shm, KnownNat k
       , ShapedTensor shaped
       , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
    => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
    -> shaped rn sh
    -> shaped rm (k ': shm)
    -> shaped rn (1 + k ': sh)
  sscan f acc0 es =
    sletHVectorIn
      (dmapAccumL (Proxy @ranked)
         (SNat @k)
         (V.singleton $ voidFromShS @rn @sh)
         (V.singleton $ voidFromShS @rn @sh)
         (V.singleton $ voidFromShS @rm @shm)
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> HVectorOf f
              g !acc !e =
                sletInHVector
                  (f (sfromD $ acc V.! 0) (sfromD $ e V.! 0))
                  (\res -> dmkHVector
                           $ V.fromList [ DynamicShaped res
                                        , DynamicShaped res ])
          in g)
         (dmkHVector $ V.singleton $ DynamicShaped acc0)
         (dmkHVector $ V.singleton $ DynamicShaped es))
      (\res -> sappend @_ @_ @1 (sfromList [acc0]) (sfromD $ res V.! 1))
  -- | A strict right macAccum.
  --
  -- The applications of 'dfwd' and 'drevDt' performed already at this point
  -- ensure that the computation of a derivative is not repeated
  -- and that its result is shared. However, most of the time
  -- the computation is unnneeded, so the AST instance uses a non-strict
  -- constructor 'AstLambda' for it's instance of 'HFunOf'.
  dmapAccumR
    :: Proxy ranked
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVectorOf ranked
    -> HVectorOf ranked
    -> HVectorOf ranked
  dmapAccumR proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = accShs V.++ eShs
        fl :: forall f. ADReady f => [HVector f] -> HVectorOf f
        fl [!acc, !e] = f acc e
        fl _ = error "fl: wrong number of arguments"
        accLen = V.length accShs
        fs :: forall f. ADReady f => [HVector f] -> HVectorOf f
        fs [!acc_e] = uncurry f (V.splitAt accLen acc_e)
        fs _ = error "fs: wrong number of arguments"
    in dmapAccumRDer proxy k accShs bShs eShs
                     (dlambda @ranked [accShs, eShs] $ HFun fl)
                     (dfwd @ranked shs $ HFun fs)
                     (drevDt @ranked shs $ HFun fs)
                     acc0 es
  dmapAccumRDer
    :: Proxy ranked
    -> SNat k
    -> VoidHVector  -- ^ accShs, shapes of acc
    -> VoidHVector  -- ^ bShs, shapes of b
    -> VoidHVector  -- ^ eShs, shapes of e
    -> HFunOf ranked
    -- (forall f. ADReady f =>
    --  [ HVector f      -- ^ acc, accumulator :: accShs
    --  , HVector f ]    -- ^ e, element of es :: eShs
    --  -> HVectorOf f)  -- ^ (x, b) :: (accShs, bShs)
    -> HFunOf ranked
    -- (forall f. ADReady f =>
    --  [ HVector f      -- ^ dacc :: accShs
    --    ++ HVector f   -- ^ de :: eShs
    --  , HVector f      -- ^ acc :: accShs
    --    ++ HVector f ] -- ^ e :: eShs
    --  -> HVectorOf f)  -- ^ (dx, db) :: (accShs, bShs)
    -> HFunOf ranked
    -- (forall f. ADReady f =>
    --  [ HVector f      -- ^ dx :: accShs
    --    ++ HVector f   -- ^ db :: bShs
    --  , HVector f      -- ^ acc :: accShs
    --    ++ HVector f ] -- ^ e :: eShs
    --  -> HVectorOf f)  -- ^ (dacc, de) :: (accShs, eShs)
    -> HVectorOf ranked  -- ^ acc0 :: accShs
    -> HVectorOf ranked  -- ^ es :: k ': eShs
    -> HVectorOf ranked  -- ^ (x, bs) :: (accShs, k ': bShs)
  -- | A strict left macAccum.
  dmapAccumL
    :: Proxy ranked
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVectorOf ranked
    -> HVectorOf ranked
    -> HVectorOf ranked
  dmapAccumL proxy !k !accShs !bShs !eShs f acc0 es =
    let shs = accShs V.++ eShs
        fl :: forall f. ADReady f => [HVector f] -> HVectorOf f
        fl [!acc, !e] = f acc e
        fl _ = error "fl: wrong number of arguments"
        accLen = V.length accShs
        fs :: forall f. ADReady f => [HVector f] -> HVectorOf f
        fs [!acc_e] = uncurry f (V.splitAt accLen acc_e)
        fs _ = error "fs: wrong number of arguments"
    in dmapAccumLDer proxy k accShs bShs eShs
                     (dlambda @ranked [accShs, eShs] $ HFun fl)
                     (dfwd @ranked shs $ HFun fs)
                     (drevDt @ranked shs $ HFun fs)
                     acc0 es
  dmapAccumLDer
    :: Proxy ranked
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> HFunOf ranked
    -> HFunOf ranked
    -> HFunOf ranked
    -> HVectorOf ranked
    -> HVectorOf ranked
    -> HVectorOf ranked

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
  withListSh (Proxy @sh2) $ \(sh1 :: ShapeInt n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"
rfromD (DynamicShapedDummy @r2 @sh2 _ _) =
  withListSh (Proxy @sh2) $ \(sh1 :: ShapeInt n2) ->
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
rscalar = rconst . OR.scalar

ingestData :: forall r sh shaped.
              (GoodScalar r, KnownShS sh, ShapedTensor shaped)
           => [r] -> shaped r sh
ingestData l | Dict <- lemShapeFromKnownShS (Proxy @sh) = sconst $ OS.fromList l

sscalar :: (GoodScalar r, ShapedTensor shaped) => r -> shaped r '[]
sscalar = sconst . OS.scalar

srepl :: forall sh r shaped. (GoodScalar r, KnownShS sh, ShapedTensor shaped)
      => r -> shaped r sh
srepl | Dict <- lemShapeFromKnownShS (Proxy @sh) =
  sconst . OS.constant
  -- TODO: the following simplifies better, because the replication is not
  -- hidden at low level:
  -- Dict <- lemKnownNatSize (knownShS @sh) =
  --   sreplicate0N . sscalar
  -- though we could also look at the low level in @isSmall@ and mark
  -- replicated constants as small

newtype HFun =
  HFun {unHFun :: forall f. ADReady f => [HVector f] -> HVectorOf f}

instance Show HFun where
  show _ = "<lambda>"


-- * The giga-constraint

type ADReady ranked = ADReadyR ranked  -- implies both

type ADReadyR ranked = ADReadyBoth ranked (ShapedOf ranked)

type ADReadyS shaped = ADReadyBoth (RankedOf shaped) shaped

-- Here is in other places reflexive closure of type equalities is created
-- manually (and not for all equalities) due to #23333.
type ADReadySmall ranked shaped =
  ( shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped
  , ShapedOf shaped ~ shaped, RankedOf ranked ~ ranked
  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked
  , PrimalOf ranked ~ RankedOf (PrimalOf ranked)
  , RankedOf (PrimalOf shaped) ~ PrimalOf ranked
  , PrimalOf ranked ~ RankedOf (PrimalOf shaped)
  , ShapedOf (PrimalOf ranked) ~ PrimalOf shaped
  , PrimalOf shaped ~ ShapedOf (PrimalOf ranked)
  , BoolOf ranked ~ BoolOf shaped
  , BoolOf shaped ~ BoolOf ranked
  , BoolOf ranked ~ BoolOf (PrimalOf ranked)
  , BoolOf (PrimalOf ranked) ~ BoolOf ranked
  , BoolOf shaped ~ BoolOf (PrimalOf shaped)
  , BoolOf (PrimalOf shaped) ~ BoolOf shaped
  , Boolean (BoolOf ranked)
  , IfF ranked, IfF shaped, IfF (PrimalOf ranked), IfF (PrimalOf shaped)
  , EqF ranked, EqF shaped, EqF (PrimalOf ranked), EqF (PrimalOf shaped)
  , OrdF ranked, OrdF shaped, OrdF (PrimalOf ranked), OrdF (PrimalOf shaped)
  , RankedTensor ranked, RankedTensor (PrimalOf ranked)
  , ShapedTensor shaped, ShapedTensor (PrimalOf shaped)
  , CRanked ranked Show, CRanked (PrimalOf ranked) Show
  , CShaped shaped Show, CShaped (PrimalOf shaped) Show
  , Show (HFunOf ranked)
  )

type ADReadyBoth ranked shaped =
  ( ADReadySmall ranked shaped
  , HVectorTensor ranked shaped
  , HVectorTensor (PrimalOf ranked) (PrimalOf shaped) )
