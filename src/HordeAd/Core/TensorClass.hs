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
    ShapeInt, ShapeSh
    -- * The tensor classes
  , RankedTensor(..), ShapedTensor(..), HVectorTensor(..)
  , rfromD, sfromD
    -- * The related classes and constraints
  , ADReady, ADReadyBoth, ADReadyR, ADReadyS
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Function ((&))
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, OrderingI (..), cmpNat, sameNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Vector)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.HVector
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import           HordeAd.Internal.TensorOps
import           HordeAd.Util.ShapedList
  (ShapeSh, ShapedList (..), consShaped, shapedNat, unShapedNat)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Ranked tensor class definition

type TensorSupports :: (Type -> Constraint) -> TensorType ty -> Constraint
type TensorSupports c f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => (c r, c (Vector r)) => c (f r y)

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Integral (IntOf ranked), CRanked ranked Num
      , TensorSupports RealFloat ranked, TensorSupports Integral ranked )
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
    ZS -> error "tlength: impossible pattern needlessly required"
    k :$ _ -> k
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
    _ :$ width2 :$ ZS -> rsum (rtranspose [2,1,0] (rreplicate width2 m1)
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
                              (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  rfromList :: (GoodScalar r, KnownNat n)
            => [ranked r n] -> ranked r (1 + n)
  rfromList0N :: (GoodScalar r, KnownNat n)
              => ShapeInt n -> [ranked r 0] -> ranked r n
  rfromList0N sh = rreshape sh . rfromList
  rfromVector :: (GoodScalar r, KnownNat n)
              => Data.Vector.Vector (ranked r n) -> ranked r (1 + n)
  rfromVector v = rfromList (V.toList v)  -- horribly inefficient for large vs
  rfromVector0N :: (GoodScalar r, KnownNat n)
                => ShapeInt n -> Data.Vector.Vector (ranked r 0) -> ranked r n
  rfromVector0N sh = rreshape sh . rfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'rlet'.
  runravelToList :: (GoodScalar r, KnownNat n)
                 => ranked r (1 + n) -> [ranked r n]
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
                ZS -> Nothing
                len :$ _ -> Just (v ! [0], rslice 1 (len - 1) v)
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
    let buildSh :: KnownNat m1
                => ShapeInt m1 -> (IndexOf ranked m1 -> ranked r n)
                -> ranked r (m1 + n)
        buildSh ZS f = f ZI
        buildSh (k :$ sh) f =
          let g i = buildSh sh (\ix -> f (i :. ix))
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
  rgather1 k v f = rgather @ranked @r @1 (k :$ dropShape (rshape v)) v
                           (\(i :. ZI) -> f i)
  rcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => ranked r1 n -> ranked r2 n
  rfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => ranked r1 n -> ranked r2 n
  rconst :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  rletHVectorIn :: (KnownNat n, GoodScalar r)
                => VoidHVector
                -> HVectorOf ranked
                -> (HVector ranked -> ranked r n)
                -> ranked r n
  rfromS :: (GoodScalar r, Sh.Shape sh)
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
  rletWrap :: (GoodScalar r, KnownNat n)
           => ADShare -> ranked r n -> ranked r n
  rletWrap _l u = u
  rletUnwrap :: ranked r n -> (ADShare, ranked r n)
  rletUnwrap u = (emptyADShare, u)
  runlet :: (GoodScalar r, KnownNat n)
         => ADShare -> AstBindingsD ranked -> ranked r n
         -> ranked r n
  runlet l astBindings = assert (nullADShare l && null astBindings)
  rregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> AstBindingsD ranked
            -> (AstBindingsD ranked, ranked r n)
  rregister r l = (l, r)
  rsharePrimal :: (GoodScalar r, KnownNat n)
               => ranked r n -> ADShare -> (ADShare, ranked r n)
  rsharePrimal r l = (l, r)

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

class ( Integral (IntOf shaped), CShaped shaped Num
      , TensorSupports RealFloat shaped, TensorSupports Integral shaped )
      => ShapedTensor (shaped :: ShapedTensorType) where

  slet :: (Sh.Shape sh, Sh.Shape sh2, GoodScalar r, GoodScalar r2)
       => shaped r sh -> (shaped r sh -> shaped r2 sh2)
       -> shaped r2 sh2
  slet a f = f a

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, Sh.Shape sh)
         => shaped r sh -> ShapeSh sh
  sshape _ = ShapedList.shapeSh @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (Sh.Rank sh))
        => shaped r sh -> Int
  srank _ = valueOf @(Sh.Rank sh)
  ssize :: forall sh r. (GoodScalar r, Sh.Shape sh) => shaped r sh -> Int
  ssize _ = Sh.sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => shaped r (n ': sh) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, Sh.Shape sh, KnownNat n
               , Sh.Shape (Sh.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Sh.Init (n ': sh))
  smaxIndex :: ( GoodScalar r, GoodScalar r2, Sh.Shape sh, KnownNat n
               , Sh.Shape (Sh.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (Sh.Init (n ': sh))
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, Sh.Shape sh)
         => shaped r sh -> shaped r2 sh
    -- not IntSh, because the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => shaped r '[n]  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( GoodScalar r, Sh.Shape sh1, Sh.Shape sh2
                  , Sh.Shape (sh1 Sh.++ sh2) )
               => shaped r (sh1 Sh.++ sh2) -> IndexSh shaped sh1
               -> shaped r sh2
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, Sh.Shape sh1)
          => shaped r sh1 -> IndexSh shaped sh1
          -> shaped r '[]
  sindex0 = gcastWith (unsafeCoerce Refl :: sh1 Sh.++ '[] :~: sh1)
              sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
       => shaped r (n ': sh) -> shaped r sh
  ssum0 :: (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
        => shaped r sh -> shaped r '[]
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
        => shaped r sh -> shaped r sh -> shaped r '[]
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ consShaped i ZSH))
  smatmul2 :: forall r n m p. (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Proxy @'[2, 1, 0]) (sreplicate @shaped @p m1)
          * stranspose (Proxy @'[1, 0]) (sreplicate @shaped @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, Sh.Shape sh2, Sh.Shape sh, Sh.Shape (Sh.Take p sh)
       , Sh.Shape (Sh.Drop p sh), Sh.Shape (sh2 Sh.++ Sh.Drop p sh) )
    => shaped r (sh2 Sh.++ Sh.Drop p sh)
    -> (IndexSh shaped sh2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, Sh.Shape sh, Sh.Shape (Sh.Take p sh)
       , Sh.Shape (Sh.Drop p sh) )
    => shaped r (n2 ': Sh.Drop p sh)
    -> (IntSh shaped n2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (ShapedList.unconsContShaped f)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (GoodScalar r, KnownNat n, Sh.Shape sh)
            => [shaped r sh] -> shaped r (n ': sh)
  sfromList0N :: forall r sh.
                 (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
              => [shaped r '[]] -> shaped r sh
  sfromList0N = sreshape @shaped @r @'[Sh.Size sh] @sh . sfromList
  sfromVector :: (GoodScalar r, KnownNat n, Sh.Shape sh)
              => Data.Vector.Vector (shaped r sh) -> shaped r (n ': sh)
  sfromVector v = sfromList (V.toList v)  -- horribly inefficient for large vs
  sfromVector0N :: forall r sh.
                   (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
                => Data.Vector.Vector (shaped r '[])
                -> shaped r sh
  sfromVector0N = sreshape @shaped @r @'[Sh.Size sh] @sh . sfromVector
  -- | Warning: during computation, sharing between the elements
  -- of the resulting list is likely to be lost, so it needs to be ensured
  -- by explicit sharing, e.g., 'slet'.
  sunravelToList :: (GoodScalar r, KnownNat n, Sh.Shape sh)
                 => shaped r (n ': sh) -> [shaped r sh]
  sreplicate :: (KnownNat n, Sh.Shape sh, GoodScalar r)
             => shaped r sh -> shaped r (n ': sh)
  sreplicate0N :: forall r sh.
                  (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
               => shaped r '[] -> shaped r sh
  sreplicate0N = sreshape @shaped @r @'[Sh.Size sh] @sh
                 . sreplicate @shaped @(Sh.Size sh)
  sappend :: (GoodScalar r, KnownNat m, KnownNat n, Sh.Shape sh)
          => shaped r (m ': sh) -> shaped r (n ': sh)
          -> shaped r ((m + n) ': sh)
  sslice :: (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, Sh.Shape sh)
         => Proxy i -> Proxy n
         -> shaped r (i + n + k ': sh) -> shaped r (n ': sh)
  suncons :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
          => shaped r (n ': sh) -> Maybe (shaped r sh, shaped r (n - 1 ': sh))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :$: ZSH)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :$: ZSH)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (GoodScalar r, KnownNat n, Sh.Shape sh)
           => shaped r (n ': sh) -> shaped r (n ': sh)
  str :: ( GoodScalar r, KnownNat n, KnownNat m, Sh.Shape sh
         , KnownNat (Sh.Rank sh) )
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose (Proxy @'[1, 0])
  stranspose :: forall perm r sh.
                ( OS.Permutation perm, Sh.Shape perm, Sh.Shape sh
                , KnownNat (Sh.Rank sh), Sh.Shape (Sh.Permute perm sh)
                , Sh.Rank perm <= Sh.Rank sh, GoodScalar r )
             => Proxy perm -> shaped r sh -> shaped r (Sh.Permute perm sh)
  sflatten :: (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
           => shaped r sh -> shaped r '[Sh.Size sh]
  sflatten = sreshape
  sreshape :: ( GoodScalar r, Sh.Shape sh, Sh.Shape sh2
              , Sh.Size sh ~ Sh.Size sh2 )
           => shaped r sh -> shaped r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh.
            (GoodScalar r, Sh.Shape sh, Sh.Shape (Sh.Take m sh))
         => (IndexSh shaped (Sh.Take m sh) -> shaped r (Sh.Drop m sh))
         -> shaped r sh
  sbuild =
    let buildSh
          :: forall sh1.
             ShapeSh sh1 -> ShapeSh (sh1 Sh.++ Sh.Drop m sh)
          -> (IndexSh shaped sh1 -> shaped r (Sh.Drop m sh))
          -> shaped r (sh1 Sh.++ Sh.Drop m sh)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSH, _) -> f ZSH
          (_ :$: sh2, _ :$: sh2m) ->
            let g i = buildSh sh2 sh2m (f . consShaped i)
            in sbuild1 g
    in gcastWith (unsafeCoerce Refl
                  :: sh :~: Sh.Take m sh Sh.++ Sh.Drop m sh)
       $ buildSh (ShapedList.shapeSh @(Sh.Take m sh)) (ShapedList.shapeSh @sh)
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
          => (IntSh shaped n -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: forall r r2 m sh.
          ( GoodScalar r, GoodScalar r2, KnownNat m
          , Sh.Shape sh, Sh.Shape (Sh.Take m sh), Sh.Shape (Sh.Drop m sh) )
       => (shaped r (Sh.Drop m sh) -> shaped r2 (Sh.Drop m sh))
       -> shaped r sh -> shaped r2 sh
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: Sh.Take m sh Sh.++ Sh.Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r r2 sh n.
           (GoodScalar r, GoodScalar r2, KnownNat n, Sh.Shape sh)
        => (shaped r sh -> shaped r2 sh)
        -> shaped r (n ': sh) -> shaped r2 (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ consShaped i ZSH))
  smap0N :: forall r r2 sh.
            (GoodScalar r, GoodScalar r2, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => (shaped r '[] -> shaped r2 '[]) -> shaped r sh -> shaped r2 sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @r2 @(Sh.Rank sh) (f . sindex0 v)
  szipWith :: forall r1 r2 r m sh1 sh2 sh.
              ( GoodScalar r1, GoodScalar r2, GoodScalar r
              , KnownNat m, Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh
              , Sh.Shape (Sh.Take m sh), Sh.Shape (Sh.Drop m sh1)
              , Sh.Shape (Sh.Drop m sh2), Sh.Shape (Sh.Drop m sh)
              , sh1 ~ Sh.Take m sh Sh.++ Sh.Drop m sh1
              , sh2 ~ Sh.Take m sh Sh.++ Sh.Drop m sh2 )
           => (shaped r1 (Sh.Drop m sh1)
               -> shaped r2 (Sh.Drop m sh2)
               -> shaped r (Sh.Drop m sh))
           -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r1 r2 r n sh1 sh2 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r
               , KnownNat n, Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh )
            => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r sh)
            -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
            -> shaped r (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ consShaped i ZSH)
                                     (v !$ consShaped i ZSH))
  szipWith0N :: forall r1 r2 r sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r
                , Sh.Shape sh, KnownNat (Sh.Rank sh) )
             => (shaped r1 '[] -> shaped r2 '[] -> shaped r '[])
             -> shaped r1 sh -> shaped r2 sh -> shaped r sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: Sh.Drop (Sh.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: Sh.Take (Sh.Rank sh) sh :~: sh)
    $ sbuild @shaped @_ @(Sh.Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  szipWith3 :: forall r1 r2 r3 r m sh1 sh2 sh3 sh.
               ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
               , KnownNat m
               , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh3, Sh.Shape sh
               , Sh.Shape (Sh.Take m sh), Sh.Shape (Sh.Drop m sh1)
               , Sh.Shape (Sh.Drop m sh2), Sh.Shape (Sh.Drop m sh3)
               , Sh.Shape (Sh.Drop m sh)
               , sh1 ~ Sh.Take m sh Sh.++ Sh.Drop m sh1
               , sh2 ~ Sh.Take m sh Sh.++ Sh.Drop m sh2
               , sh3 ~ Sh.Take m sh Sh.++ Sh.Drop m sh3 )
            => (shaped r1 (Sh.Drop m sh1)
                -> shaped r2 (Sh.Drop m sh2)
                -> shaped r3 (Sh.Drop m sh3)
                -> shaped r (Sh.Drop m sh))
            -> shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3 -> shaped r sh
  szipWith3 f u v w = sbuild (\ix -> f (u !$ ix) (v !$ ix) (w !$ ix))
  szipWith31 :: forall r1 r2 r3 r n sh1 sh2 sh3 sh.
                ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                , KnownNat n
                , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh3, Sh.Shape sh )
             => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3 -> shaped r sh)
             -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
             -> shaped r3 (n ': sh3)
             -> shaped r (n ': sh)
  szipWith31 f u v w = sbuild1 (\i -> f (u !$ consShaped i ZSH)
                                        (v !$ consShaped i ZSH)
                                        (w !$ consShaped i ZSH))
  szipWith30N :: forall r1 r2 r3 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r
                 , Sh.Shape sh, KnownNat (Sh.Rank sh) )
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
               , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh3, Sh.Shape sh4
               , Sh.Shape sh
               , Sh.Shape (Sh.Take m sh), Sh.Shape (Sh.Drop m sh1)
               , Sh.Shape (Sh.Drop m sh2), Sh.Shape (Sh.Drop m sh3)
               , Sh.Shape (Sh.Drop m sh4), Sh.Shape (Sh.Drop m sh)
               , sh1 ~ Sh.Take m sh Sh.++ Sh.Drop m sh1
               , sh2 ~ Sh.Take m sh Sh.++ Sh.Drop m sh2
               , sh3 ~ Sh.Take m sh Sh.++ Sh.Drop m sh3
               , sh4 ~ Sh.Take m sh Sh.++ Sh.Drop m sh4 )
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
                , Sh.Shape sh1, Sh.Shape sh2, Sh.Shape sh3, Sh.Shape sh4
                , Sh.Shape sh )
             => (shaped r1 sh1 -> shaped r2 sh2 -> shaped r3 sh3
                 -> shaped r4 sh4 -> shaped r sh)
             -> shaped r1 (n ': sh1) -> shaped r2 (n ': sh2)
             -> shaped r3 (n ': sh3) -> shaped r4 (n ': sh4)
             -> shaped r (n ': sh)
  szipWith41 f u v w x = sbuild1 (\i -> f (u !$ consShaped i ZSH)
                                          (v !$ consShaped i ZSH)
                                          (w !$ consShaped i ZSH)
                                          (x !$ consShaped i ZSH))
  szipWith40N :: forall r1 r2 r3 r4 r sh.
                 ( GoodScalar r1, GoodScalar r2, GoodScalar r3, GoodScalar r4
                 , GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh) )
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
       ( GoodScalar r, Sh.Shape sh2, Sh.Shape sh, Sh.Shape (Sh.Take p sh)
       , Sh.Shape (Sh.Drop p sh), Sh.Shape (sh2 Sh.++ Sh.Drop p sh) )
    => shaped r sh
    -> (IndexSh shaped sh2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r (sh2 Sh.++ Sh.Drop p sh)
  sgather1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, Sh.Shape sh, Sh.Shape (Sh.Take p sh)
       , Sh.Shape (Sh.Drop p sh) )
    => shaped r sh
    -> (IntSh shaped n2 -> IndexSh shaped (Sh.Take p sh))
    -> shaped r (n2 ': Sh.Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (ShapedList.unconsContShaped f)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, Sh.Shape sh)
        => shaped r1 sh -> shaped r2 sh
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, Sh.Shape sh)
                => shaped r1 sh -> shaped r2 sh
  sconst :: (GoodScalar r, Sh.Shape sh) => OS.Array sh r -> shaped r sh
  sletHVectorIn :: (Sh.Shape sh, GoodScalar r)
                => VoidHVector
                -> HVectorOf (RankedOf shaped)
                -> (HVector (RankedOf shaped) -> shaped r sh)
                -> shaped r sh
  sfromR :: (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Rank sh))
         => RankedOf shaped r (Sh.Rank sh) -> shaped r sh

  -- ** No serviceable parts beyond this point ** --

  sscaleByScalar
    :: (GoodScalar r, Sh.Shape sh, KnownNat (Sh.Size sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v * sreplicate0N s
  ssumIn :: ( GoodScalar r, Sh.Shape sh, KnownNat n, KnownNat m
            , KnownNat (Sh.Rank sh) )
         => shaped r (n ': m ': sh) -> shaped r (n ': sh)
  ssumIn = ssum . str
    -- TODO: generalize, replace by stride analysis, etc.
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => shaped r '[n, m] -> shaped r '[n, m] -> shaped r '[n]
  sdot1In t u = ssumIn (t * u)
    -- TODO: generalize, replace by stride analysis, etc.
  sletWrap :: (GoodScalar r, Sh.Shape sh)
           => ADShare -> shaped r sh -> shaped r sh
  sletWrap _l u = u
  sletUnwrap :: shaped r sh -> (ADShare, shaped r sh)
  sletUnwrap u = (emptyADShare, u)
  sunlet :: (GoodScalar r, Sh.Shape sh)
         => ADShare -> AstBindingsD (RankedOf shaped) -> shaped r sh
         -> shaped r sh
  sunlet l astBindings = assert (nullADShare l && null astBindings)
  sregister :: (GoodScalar r, Sh.Shape sh)
            => shaped r sh -> AstBindingsD (RankedOf shaped)
            -> (AstBindingsD (RankedOf shaped), shaped r sh)
  sregister r l = (l, r)
  ssharePrimal :: (GoodScalar r, Sh.Shape sh)
               => shaped r sh -> ADShare -> (ADShare, shaped r sh)
  ssharePrimal r l = (l, r)

  -- Primal/dual things.
  sconstant :: (GoodScalar r, Sh.Shape sh)
            => PrimalOf shaped r sh -> shaped r sh
  sprimalPart :: (GoodScalar r, Sh.Shape sh)
              => shaped r sh -> PrimalOf shaped r sh
  sdualPart :: (GoodScalar r, Sh.Shape sh)
            => shaped r sh -> DualOf shaped r sh
  sD :: (GoodScalar r, Sh.Shape sh)
     => PrimalOf shaped r sh -> DualOf shaped r sh -> shaped r sh
  sScale :: (GoodScalar r, Sh.Shape sh)
         => PrimalOf shaped r sh -> DualOf shaped r sh -> DualOf shaped r sh


-- * HVectorTensor class definition

-- This particular fundep really helps with type reconstruction in user code,
-- e.g., in the shaped nested folds tests.
class HVectorTensor (ranked :: RankedTensorType)
                    (shaped :: ShapedTensorType)
                    | ranked -> shaped, shaped -> ranked where
  dshape :: HVectorOf ranked -> VoidHVector
  dmkHVector :: HVector ranked -> HVectorOf ranked
  dunHVector :: VoidHVector -> HVectorOf ranked -> HVector ranked
    -- ^ Warning: this operation easily breaks sharing.
  dletHVectorInHVector
    :: VoidHVector
    -> HVectorOf ranked
    -> (HVector ranked -> HVectorOf ranked)
    -> HVectorOf ranked
  rletInHVector :: (GoodScalar r, KnownNat n)
                => ranked r n
                -> (ranked r n -> HVectorOf ranked)
                -> HVectorOf ranked
  sletInHVector :: (GoodScalar r, Sh.Shape sh)
                => shaped r sh
                -> (shaped r sh -> HVectorOf ranked)
                -> HVectorOf ranked
  dunlet :: ADShare -> AstBindingsD ranked -> HVectorOf ranked
         -> HVectorOf ranked
  dunlet l astBindings = assert (nullADShare l && null astBindings)
  dsharePrimal :: VoidHVector -> HVectorOf ranked -> ADShare
               -> (ADShare, HVector ranked)
  dregister :: VoidHVector -> HVectorOf ranked -> AstBindingsD ranked
            -> (AstBindingsD ranked, HVector ranked)
  dbuild1 :: Int  -- k
          -> (IntOf ranked -> HVectorOf ranked)  -- sh_i
          -> HVectorOf ranked  -- k ': sh_i
  dzipWith1 :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
               , RankedOf (PrimalOf (ShapedOf ranked))
                 ~ RankedOf (PrimalOf ranked) )
            => (HVector ranked -> HVectorOf ranked)
                 -- ^ both hVectors can have arbitrary tensors in them
            -> HVector ranked -> HVectorOf ranked
                 -- ^ each hVector has the same tensor shapes and scalar types
                 -- as its corresponding hVector above, except for the extra
                 -- outermost dimension, which needs to be same in each tensor
                 -- from either of the hVectors; the hVectors can't be empty
  -- The second argument is only used to determine tensor shapes
  -- and the third has to have the same shapes as the second.
  --
  -- The function argument needs to be quantified (or an AST term),
  -- because otherwise in the ADVal instance one could put an illegal
  -- InputR there, confusing two levels of contangents.
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector ranked
       -> HVectorOf ranked
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => HVector f -> f r n)
         -> VoidHVector
         -> HVector ranked
         -> ranked r n  -- ^ incoming cotangent (dt)
         -> HVectorOf ranked
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector ranked
       -> HVector ranked  -- ^ incoming tangent (ds)
       -> ranked r n
  srev :: (GoodScalar r, Sh.Shape sh)
       => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
       -> VoidHVector
       -> HVector ranked
       -> HVectorOf ranked
  srevDt :: (GoodScalar r, Sh.Shape sh)
         => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
         -> VoidHVector
         -> HVector ranked
         -> shaped r sh
         -> HVectorOf ranked
  sfwd :: (GoodScalar r, Sh.Shape sh)
       => (forall f. ADReadyS f => HVector (RankedOf f) -> f r sh)
       -> VoidHVector
       -> HVector ranked
       -> HVector ranked
       -> shaped r sh
  -- The type mentions ADReady, so it's awkward to put this into RankedTensor,
  -- which doesn't know about HVectorTensor.
  -- | A strict left fold.
  rfold :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ranked rn n  -- ^ initial value
        -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
        -> ranked rn n
  rfoldDer :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> ranked rn n  -- ^ initial value
           -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
           -> ranked rn n
  -- | A strict left scan.
  rscan :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ranked rn n
        -> ranked rm (1 + m)
        -> ranked rn (1 + n)
  rscanDer :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> ranked rn n
           -> ranked rm (1 + m)
           -> ranked rn (1 + n)
  -- Library users are encouraged to use dmapAccumL directly, but we keep it,
  -- because we have a lot of good tests for this (including an alternative
  -- delta eval code that uses this).
  -- {-# DEPRECATED rscanZip "Use dmapAccumL instead" #-}
  rscanZip :: forall rn n. (GoodScalar rn, KnownNat n, RankedTensor ranked)
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector  -- shapes of the HVector above, not below
         -> ranked rn n
         -> HVector ranked  -- one rank higher than above
         -> ranked rn (1 + n)
  rscanZip f eShs acc0 es =
    let width = case V.unsnoc es of
          Nothing -> error "rscanZip: can't determine argument width"
          Just (_, d) -> case shapeDynamicF (shapeToList . rshape) d of
            [] -> error "rscanZip: wrong rank of argument"
            w : _shm -> w
        sh = rshape acc0
    in withSNat width $ \snat ->
      rletHVectorIn
        (V.fromList [voidFromSh @rn sh, voidFromSh @rn (width :$ sh)])
        (dmapAccumL
           snat
           (V.singleton $ voidFromSh @rn sh)
           (V.singleton $ voidFromSh @rn sh)
           eShs
           (let g :: forall f. ADReady f
                  => HVector f -> HVector f -> HVectorOf f
                g acc e =
                  rletInHVector
                    (f (rfromD $ acc V.! 0) e)
                    (\res -> dmkHVector
                             $ V.fromList
                                 [ DynamicRanked @rn @n @f res
                                 , DynamicRanked @rn @n @f res ])
            in g)
           (V.singleton $ DynamicRanked acc0)
           es)
        (\res -> rappend (rfromList [acc0]) (rfromD $ res V.! 1))
  -- | A strict left fold.
  sfold :: (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> shaped rn sh
        -> shaped rm (k ': shm)
        -> shaped rn sh
  sfoldDer :: ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> shaped rn sh
           -> shaped rm (k ': shm)
           -> shaped rn sh
  -- | A strict left scan.
  sscan :: (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> shaped rn sh
        -> shaped rm (k ': shm)
        -> shaped rn (1 + k ': sh)
  sscanDer :: ( GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm
              , KnownNat k )
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> shaped rn sh
           -> shaped rm (k ': shm)
           -> shaped rn (1 + k ': sh)
  -- Library users are encouraged to use dmapAccumL directly, but we keep it,
  -- because we have a lot of good tests for this (including an alternative
  -- delta eval code that uses this).
  -- {-# DEPRECATED sscanZip "Use dmapAccumL instead" #-}
  sscanZip :: forall rn sh k.
              ( GoodScalar rn, Sh.Shape sh, KnownNat k, ShapedTensor shaped
              , shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped )
         => (forall f. ADReadyS f
             => f rn sh -> HVector (RankedOf f) -> f rn sh)
         -> VoidHVector
         -> shaped rn sh
         -> HVector ranked
         -> shaped rn (1 + k ': sh)
  sscanZip f eShs acc0 es =
    sletHVectorIn
      (V.fromList [voidFromShS @rn @sh, voidFromShS @rn @(k ': sh)])
      (dmapAccumL
         (SNat @k)
         (V.singleton $ voidFromShS @rn @sh)
         (V.singleton $ voidFromShS @rn @sh)
         eShs
         (let g :: forall f. ADReady f
                => HVector f -> HVector f -> HVectorOf f
              g acc e =
                sletInHVector
                  (f (sfromD $ acc V.! 0) e)
                  (\res -> dmkHVector
                           $ V.fromList
                               [ DynamicShaped @rn @sh @f res
                               , DynamicShaped @rn @sh @f res ])
          in g)
         (V.singleton $ DynamicShaped acc0)
         es)
      (\res -> sappend @_ @_ @1 (sfromList [acc0]) (sfromD $ res V.! 1))
  -- | A strict right macAccum.
  dmapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector ranked
    -> HVector ranked
    -> HVectorOf ranked
  dmapAccumRDer
    :: SNat k
    -> VoidHVector  -- ^ accShs, shapes of acc
    -> VoidHVector  -- ^ bShs, shapes of b
    -> VoidHVector  -- ^ eShs, shapes of e
    -> (forall f. ADReady f
        => HVector f  -- ^ acc, accumulator :: accShs
        -> HVector f  -- ^ e, element of es :: eShs
        -> HVectorOf f)  -- ^ (x, y) :: (accShs, bShs)
    -> (forall f. ADReady f
        => HVector f  -- ^ dacc :: accShs
        -> HVector f  -- ^ de :: eShs
        -> HVector f  -- ^ acc :: accShs
        -> HVector f  -- ^ e :: eShs
        -> HVectorOf f)  -- ^ (dx, dy) :: (accShs, bShs)
    -> (forall f. ADReady f
        => HVector f  -- ^ dx :: accShs
        -> HVector f  -- ^ dy :: bShs
        -> HVector f  -- ^ acc :: accShs
        -> HVector f  -- ^ e :: eShs
        -> HVectorOf f)  -- ^ (dx, de) :: (accShs, eShs)
    -> HVector ranked  -- ^ acc0 :: accShs
    -> HVector ranked  -- ^ es :: k ': eShs
    -> HVectorOf ranked  -- ^ (x, ys) :: (accShs, k ': bShs)
  -- | A strict left macAccum.
  dmapAccumL
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector ranked
    -> HVector ranked
    -> HVectorOf ranked
  dmapAccumLDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f
        -> HVector f
        -> HVector f
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f
        -> HVector f
        -> HVector f
        -> HVector f
        -> HVectorOf f)
    -> HVector ranked
    -> HVector ranked
    -> HVectorOf ranked

-- TODO: find a way to deprecate only in the external API, not in our code.
-- {-# DEPRECATED rscanZip "Use dmapAccumL instead" #-}
-- {-# DEPRECATED sscanZip "Use dmapAccumL instead" #-}

rfromD :: forall r n ranked.
          (RankedTensor ranked, GoodScalar r, KnownNat n)
       => DynamicTensor ranked -> ranked r n
rfromD (DynamicRanked @r2 @n2 t) = case sameNat (Proxy @n2) (Proxy @n) of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "rfromD: scalar mismatch"
  _ -> error $ "rfromD: rank mismatch "
               ++ show (valueOf @n2 :: Int, valueOf @n :: Int)
rfromD (DynamicShaped @r2 @sh2 t) =
  withListShape (Sh.shapeT @sh2) $ \(_ :: ShapeInt n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> gcastWith (unsafeCoerce Refl :: Sh.Rank sh2 :~: n2) $
                     rfromS t
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"
rfromD (DynamicRankedDummy @r2 @sh2 _ _) =
  withListShape (Sh.shapeT @sh2) $ \(sh1 :: ShapeInt n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"
rfromD (DynamicShapedDummy @r2 @sh2 _ _) =
  withListShape (Sh.shapeT @sh2) $ \(sh1 :: ShapeInt n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfromD: scalar mismatch"
      _ -> error "rfromD: rank mismatch"

sfromD :: forall r sh shaped.
          ( ShapedTensor shaped
          , GoodScalar r, Sh.Shape sh
          , ShapedOf (RankedOf shaped) ~ shaped )
       => DynamicTensor (RankedOf shaped) -> shaped r sh
sfromD (DynamicRanked @r2 @n2 t) =
  withListShape (Sh.shapeT @sh) $ \(_ :: ShapeInt n) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> gcastWith (unsafeCoerce Refl :: Sh.Rank sh :~: n) $
                     sfromR t
        _ -> error "sfromD: scalar mismatch"
      _ -> error "sfromD: rank mismatch"
sfromD (DynamicShaped @r2 @sh2 t) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (Sh.shapeT @sh2, Sh.shapeT @sh)
sfromD (DynamicRankedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> 0
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (Sh.shapeT @sh2, Sh.shapeT @sh)
sfromD (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> 0
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (Sh.shapeT @sh2, Sh.shapeT @sh)


-- * The giga-constraint

type ADReady ranked = ADReadyR ranked  -- backward compatibility

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
  , SimpleBoolOf ranked ~ SimpleBoolOf shaped
  , SimpleBoolOf shaped ~ SimpleBoolOf ranked
  , SimpleBoolOf ranked ~ SimpleBoolOf (PrimalOf ranked)
  , SimpleBoolOf (PrimalOf ranked) ~ SimpleBoolOf ranked
  , SimpleBoolOf shaped ~ SimpleBoolOf (PrimalOf shaped)
  , SimpleBoolOf (PrimalOf shaped) ~ SimpleBoolOf shaped
  , Boolean (SimpleBoolOf ranked)
  , IfF ranked, IfF shaped, IfF (PrimalOf ranked), IfF (PrimalOf shaped)
  , EqF ranked, EqF shaped, EqF (PrimalOf ranked), EqF (PrimalOf shaped)
  , OrdF ranked, OrdF shaped, OrdF (PrimalOf ranked), OrdF (PrimalOf shaped)
  , RankedTensor ranked, RankedTensor (PrimalOf ranked)
  , ShapedTensor shaped, ShapedTensor (PrimalOf shaped)
  , CRanked ranked Show, CRanked (PrimalOf ranked) Show
  , CShaped shaped Show, CShaped (PrimalOf shaped) Show
  )

type ADReadyBoth ranked shaped =
  ( ADReadySmall ranked shaped
  , HVectorTensor ranked shaped
  , HVectorTensor (PrimalOf ranked) (PrimalOf shaped) )


-- * Instances for concrete arrays

-- The HVectorTensor instance requires ADVal instance, so it's given elsewhere.

type instance SimpleBoolOf (Flip OR.Array) = Bool

instance EqF (Flip OR.Array) where
  u ==. v = (emptyADShare, u == v)
  u /=. v = (emptyADShare, u /= v)

instance OrdF (Flip OR.Array) where
  u <. v = (emptyADShare, u < v)
  u <=. v = (emptyADShare, u <= v)
  u >. v = (emptyADShare, u > v)
  u >=. v = (emptyADShare, u >= v)

instance IfF (Flip OR.Array) where
  ifF (_, b) v w = if b then v else w

type instance RankedOf (Flip OR.Array) = Flip OR.Array

type instance ShapedOf (Flip OR.Array) = Flip OS.Array

type instance HVectorOf (Flip OR.Array) = HVector (Flip OR.Array)

type instance PrimalOf (Flip OR.Array) = Flip OR.Array

type instance DualOf (Flip OR.Array) = DummyDual

instance RankedTensor (Flip OR.Array) where
  rshape = tshapeR . runFlip
  rminIndex = Flip . tminIndexR . runFlip
  rmaxIndex = Flip . tmaxIndexR . runFlip
  rfloor = Flip . tfloorR . runFlip
  rindex v ix = Flip $ tindexZR (runFlip v) (fromIndexOfR ix)
  rindex0 v ix = Flip . tscalarR $ tindex0R (runFlip v) (fromIndexOfR ix)
  rsum = Flip . tsumR . runFlip
  rsum0 = Flip . tscalarR . tsum0R . runFlip
  rdot0 u v = Flip $ tscalarR $ tdot0R (runFlip u) (runFlip v)
  rmatvecmul m v = Flip $ tmatvecmulR (runFlip m) (runFlip v)
  rmatmul2 m1 m2 = Flip $ tmatmul2R (runFlip m1) (runFlip m2)
  rscatter sh t f = Flip $ tscatterZR sh (runFlip t)
                                         (fromIndexOfR . f . toIndexOfR)
  rscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t)
                                           (fromIndexOfR . f . Flip . tscalarR)
  rfromList = Flip . tfromListR . map runFlip
  rfromList0N sh = Flip . tfromList0NR sh . map (tunScalarR . runFlip)
  rfromVector = Flip . tfromVectorR . V.map runFlip
  rfromVector0N sh = Flip . tfromVector0NR sh . V.map (tunScalarR . runFlip)
  runravelToList = map Flip . tunravelToListR . runFlip
  rreplicate k = Flip . treplicateR k . runFlip
  rreplicate0N sh = Flip . treplicate0NR sh . tunScalarR . runFlip
  rappend u v = Flip $ tappendR (runFlip u) (runFlip v)
  rslice i n = Flip . tsliceR i n . runFlip
  rreverse = Flip . treverseR . runFlip
  rtranspose perm = Flip . ttransposeR perm . runFlip
  rreshape sh = Flip . treshapeR sh . runFlip
  rbuild1 k f = Flip $ tbuild1R k (runFlip . f . Flip . tscalarR)
  rmap0N f t = Flip $ tmap0NR (runFlip . f . Flip) (runFlip t)
  rzipWith0N f t u = Flip $ tzipWith0NR (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  rgather sh t f = Flip $ tgatherZR sh (runFlip t)
                                       (fromIndexOfR . f . toIndexOfR)
  rgather1 k t f = Flip $ tgatherZ1R k (runFlip t)
                                       (fromIndexOfR . f . Flip . tscalarR)
  rcast = Flip . tcastR . runFlip
  rfromIntegral = Flip . tfromIntegralR . runFlip
  rconst = Flip
  rletHVectorIn _ = (&)
  rfromS = Flip . Data.Array.Convert.convert . runFlip

  rscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  rsumIn = Flip . tsumInR . runFlip
  rdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)

  rconstant = id
  rprimalPart = id
  rdualPart _ = DummyDual
  rD u _ = u
  rScale _ _ = DummyDual

type instance SimpleBoolOf (Flip OS.Array) = Bool

instance EqF (Flip OS.Array) where
  u ==. v = (emptyADShare, u == v)
  u /=. v = (emptyADShare, u /= v)

instance OrdF (Flip OS.Array) where
  u <. v = (emptyADShare, u < v)
  u <=. v = (emptyADShare, u <= v)
  u >. v = (emptyADShare, u > v)
  u >=. v = (emptyADShare, u >= v)

instance IfF (Flip OS.Array) where
  ifF (_, b) v w = if b then v else w

type instance RankedOf (Flip OS.Array) = Flip OR.Array

type instance ShapedOf (Flip OS.Array) = Flip OS.Array

type instance PrimalOf (Flip OS.Array) = Flip OS.Array

type instance DualOf (Flip OS.Array) = DummyDual

instance ShapedTensor (Flip OS.Array) where
  sminIndex = Flip . tminIndexS . runFlip
  smaxIndex = Flip . tmaxIndexS . runFlip
  sfloor = Flip . tfloorS . runFlip
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => Flip OS.Array r '[n]  -- from 0 to n - 1
  siota = let n = valueOf @n :: Int
          in Flip $ OS.fromList $ map fromIntegral [0 .. n - 1]
  sindex v ix = Flip $ tindexZS (runFlip v) (fromIndexOfS ix)
  sindex0 v ix = Flip . tscalarS $ tindex0S (runFlip v) (fromIndexOfS ix)
  ssum = Flip . tsumS . runFlip
  ssum0 = Flip . tscalarS . tsum0S . runFlip
  sdot0 u v = Flip $ tscalarS $ tdot0S (runFlip u) (runFlip v)
  smatvecmul m v = Flip $ tmatvecmulS (runFlip m) (runFlip v)
  smatmul2 m1 m2 = Flip $ tmatmul2S (runFlip m1) (runFlip m2)
  sscatter t f = Flip $ tscatterZS (runFlip t)
                                   (fromIndexOfS . f . toIndexOfS)
  sscatter1 t f = Flip $ tscatterZ1S (runFlip t)
                                     (fromIndexOfS . f . shapedNat . Flip
                                      . tscalarR . unShapedNat)
  sfromList = Flip . tfromListS . map runFlip
  sfromList0N = Flip . tfromList0NS . map (tunScalarS . runFlip)
  sfromVector = Flip . tfromVectorS . V.map runFlip
  sfromVector0N = Flip . tfromVector0NS . V.map (tunScalarS . runFlip)
  sunravelToList = map Flip . tunravelToListS . runFlip
  sreplicate = Flip . treplicateS . runFlip
  sreplicate0N = Flip . treplicate0NS . tunScalarS . runFlip
  sappend u v = Flip $ tappendS (runFlip u) (runFlip v)
  sslice (_ :: Proxy i) _ = Flip . tsliceS @i . runFlip
  sreverse = Flip . treverseS . runFlip
  stranspose (_ :: Proxy perm) = Flip . ttransposeS @perm . runFlip
  sreshape = Flip . treshapeS . runFlip
  sbuild1 f = Flip $ tbuild1S (runFlip . f . shapedNat . Flip
                               . tscalarR . unShapedNat)
  smap0N f t = Flip $ tmap0NS (runFlip . f . Flip) (runFlip t)
  szipWith0N f t u = Flip $ tzipWith0NS (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  sgather t f = Flip $ tgatherZS (runFlip t)
                                 (fromIndexOfS . f . toIndexOfS)
  sgather1 t f = Flip $ tgatherZ1S (runFlip t)
                                   (fromIndexOfS . f . shapedNat . Flip
                                    . tscalarR . unShapedNat)
  scast = Flip . tcastS . runFlip
  sfromIntegral = Flip . tfromIntegralS . runFlip
  sconst = Flip
  sletHVectorIn _ = (&)
  sfromR = Flip . Data.Array.Convert.convert . runFlip

  sscaleByScalar s v =
    Flip $ tscaleByScalarS (tunScalarS $ runFlip s) (runFlip v)
  ssumIn = Flip . tsumInS . runFlip
  sdot1In u v = Flip $ tdot1InS (runFlip u) (runFlip v)

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual
