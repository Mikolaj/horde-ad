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
  , RankedTensor(..), ShapedTensor(..), DomainsTensor(..)
  , raddDynamic, saddDynamic, sumDynamicRanked, sumDynamicShaped, rfromD, sfromD
    -- * The related constraints
  , ADReady, ADReadyR, ADReadyS, ADReadySmall, ADReadyBoth
    -- * Concrete array instances auxiliary definitions
  , DomainsOD, sizeDomainsOD, scalarDynamic, shapeDynamic, rankDynamic
  , domainsMatch
  , odFromVar, odFromSh, odFromShS, odFromDynamic, fromDomainsR, fromDomainsS
  , unravelDomains, ravelDomains
  , mapDomainsRanked, mapDomainsRanked01, mapDomainsRanked10, mapDomainsRanked11
  , mapDomainsShaped11, mapDomainsShaped11kk
  , mapRanked, mapRanked01, mapRanked10, mapRanked11
  , index1Domains
  ) where

import Prelude

import qualified Data.Array.Convert
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Function ((&))
import           Data.Kind (Constraint, Type)
import           Data.List (foldl', transpose)
import           Data.Maybe (isJust)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , Nat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  , type (<=)
  )
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)
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
  rletDomainsIn :: (KnownNat n, GoodScalar r)
                => DomainsOD
                -> DomainsOf ranked
                -> (Domains ranked -> ranked r n)
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
  rregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> AstBindingsD ranked
            -> (AstBindingsD ranked, ranked r n)
  rregister r l = (l, r)

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
  -- TODO: we'd probably also need dZero, dIndex0 and all the others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

raddDynamic :: forall ranked r n.
               (RankedTensor ranked, GoodScalar r, KnownNat n)
            => ranked r n -> DynamicTensor ranked -> ranked r n
raddDynamic r (DynamicRanked @r2 @n2 t) = case sameNat (Proxy @n2)
                                                       (Proxy @n) of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> r + t
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"
raddDynamic _ DynamicShaped{} = error "raddDynamic: DynamicShaped"
raddDynamic r (DynamicRankedDummy @r2 @sh2 _ _) = case matchingRank @sh2 @n of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: ranked r2 (Sh.Rank sh2)
    _ -> error "raddDynamic: scalar mismatch"
  _ -> error "raddDynamic: rank mismatch"
raddDynamic _ DynamicShapedDummy{} = error "raddDynamic: DynamicShapedDummy"

saddDynamic :: forall shaped sh r.
               ( ShapedTensor shaped, GoodScalar r, Sh.Shape sh
               , ShapedOf (RankedOf shaped) ~ shaped )
            => shaped r sh -> DynamicTensor (RankedOf shaped) -> shaped r sh
saddDynamic _ DynamicRanked{} = error "saddDynamic: DynamicRanked"
saddDynamic r (DynamicShaped @r2 @sh2 t) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r + t
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"
saddDynamic _ DynamicRankedDummy{} = error "saddDynamic: DynamicRankedDummy"
saddDynamic r (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
    Just Refl -> r :: shaped r2 sh2
    _ -> error "saddDynamic: scalar mismatch"
  _ -> error "saddDynamic: shape mismatch"

sumDynamicRanked :: RankedTensor ranked
                 => [DynamicTensor ranked] -> DynamicTensor ranked
sumDynamicRanked [] = error "sumDynamicRanked: empty list"
sumDynamicRanked (DynamicRanked t : ds) =
  DynamicRanked $ foldl' raddDynamic t ds
sumDynamicRanked (DynamicShaped{} : _) =
  error "sumDynamicRanked: DynamicShaped"
sumDynamicRanked (DynamicRankedDummy @r @sh _ _ : ds) =
  withListShape (Sh.shapeT @sh) $ \sh1 ->
    DynamicRanked @r $ foldl' raddDynamic (rzero sh1) ds
sumDynamicRanked (DynamicShapedDummy{} : _) =
  error "sumDynamicRanked: DynamicShapedDummy"

sumDynamicShaped :: ( ShapedTensor shaped
                    , ShapedOf (RankedOf shaped) ~ shaped )
                 => [DynamicTensor (RankedOf shaped)]
                 -> DynamicTensor (RankedOf shaped)
sumDynamicShaped [] = error "sumDynamicShaped: empty list"
sumDynamicShaped (DynamicRanked{} : _) =
  error "sumDynamicShaped: DynamicRanked"
sumDynamicShaped (DynamicShaped t : ds) =
  DynamicShaped $ foldl' saddDynamic t ds
sumDynamicShaped (DynamicRankedDummy{} : _) =
  error "sumDynamicShaped: DynamicRankedDummy"
sumDynamicShaped (DynamicShapedDummy @r @sh _ _ : ds) =
  DynamicShaped @r @sh $ foldl' saddDynamic 0 ds


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
  sletDomainsIn :: (Sh.Shape sh, GoodScalar r)
                => DomainsOD
                -> DomainsOf (RankedOf shaped)
                -> (Domains (RankedOf shaped) -> shaped r sh)
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
  sregister :: (GoodScalar r, Sh.Shape sh)
            => shaped r sh -> AstBindingsD (RankedOf shaped)
            -> (AstBindingsD (RankedOf shaped), shaped r sh)
  sregister r l = (l, r)

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

rfromD :: forall r n ranked.
          (RankedTensor ranked, GoodScalar r, KnownNat n)
       => DynamicTensor ranked -> ranked r n
rfromD (DynamicRanked @r2 @n2 t) = case sameNat (Proxy @n2) (Proxy @n) of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "rfromD: scalar mismatch"
  _ -> error "rfromD: rank mismatch"
rfromD DynamicShaped{} = error "rfromD: unexpected DynamicShaped"
rfromD (DynamicRankedDummy @r2 @sh2 _ _) =
  withListShape (Sh.shapeT @sh2) $ \(sh1 :: ShapeInt n2) ->
    case sameNat (Proxy @n2) (Proxy @n) of
      Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
        Just Refl -> rzero sh1
        _ -> error "rfrom: scalar mismatch"
      _ -> error "rfromD: rank mismatch"
rfromD DynamicShapedDummy{} = error "rfromD: unexpected DynamicShapedDummy"

sfromD :: forall r sh shaped.
          ( ShapedTensor shaped
          , GoodScalar r, Sh.Shape sh
          , ShapedOf (RankedOf shaped) ~ shaped )
       => DynamicTensor (RankedOf shaped) -> shaped r sh
sfromD DynamicRanked{} = error "sfromD: unexpected DynamicRanked"
sfromD (DynamicShaped @r2 @sh2 t) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> t
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (Sh.shapeT @sh2, Sh.shapeT @sh)
sfromD DynamicRankedDummy{} = error "sfromD: unexpected DynamicRankedDummy"
sfromD (DynamicShapedDummy @r2 @sh2 _ _) = case sameShape @sh2 @sh of
  Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> 0
    _ -> error "sfromD: scalar mismatch"
  _ -> error $ "sfromD: shape mismatch " ++ show (Sh.shapeT @sh2, Sh.shapeT @sh)


-- * DomainsTensor class definition

class DomainsTensor (ranked :: RankedTensorType)
                    (shaped :: ShapedTensorType)
                    | ranked -> shaped, shaped -> ranked where
  dmkDomains :: Domains ranked -> DomainsOf ranked
  dunDomains :: DomainsOD -> DomainsOf ranked -> Domains ranked
    -- ^ Warning: this operation easily breaks sharing.
  dletDomainsInDomains
    :: DomainsOD
    -> DomainsOf ranked
    -> (Domains ranked -> DomainsOf ranked)
    -> DomainsOf ranked
  rletInDomains :: (GoodScalar r, KnownNat n)
                => ranked r n
                -> (ranked r n -> DomainsOf ranked)
                -> DomainsOf ranked
  sletInDomains :: (GoodScalar r, Sh.Shape sh)
                => shaped r sh
                -> (shaped r sh -> DomainsOf ranked)
                -> DomainsOf ranked
  dregister :: DomainsOD -> DomainsOf ranked -> AstBindingsD ranked
            -> (AstBindingsD ranked, Domains ranked)
  dbuild1 :: Int  -- k
          -> (IntOf ranked -> DomainsOf ranked)  -- sh
          -> DomainsOf ranked  -- k ': sh
  dzipWith1 :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
               , RankedOf (PrimalOf (ShapedOf ranked))
                 ~ RankedOf (PrimalOf ranked) )
            => (Domains ranked -> DomainsOf ranked)
                 -- ^ both domains can have arbitrary tensors in them
            -> Domains ranked -> DomainsOf ranked
                 -- ^ each domain has the same tensor shapes and scalar types
                 -- as its corresponding domain above, except for the extra
                 -- outermost dimension, which needs to be same in each tensor
                 -- from either of the domains; the domains can't be empty
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ -> dbuild1 @ranked width (\i -> f (index1Domains u i))
  -- The second argument is only used to determine tensor shapes
  -- and the third has to have the same shapes as the second.
  --
  -- The function argument needs to be quantified (or an AST term),
  -- because otherwise in the ADVal instance one could put an illegal
  -- InputR there, confusing two levels of contangents.
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> Domains ranked
       -> DomainsOf ranked
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains f -> f r n)
         -> DomainsOD
         -> Domains ranked
         -> ranked r n  -- ^ incoming cotangent (dt)
         -> DomainsOf ranked
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> Domains ranked
       -> Domains ranked  -- ^ incoming tangent (ds)
       -> ranked r n
  srev :: (GoodScalar r, Sh.Shape sh)
       => (forall f. ADReadyS f => Domains (RankedOf f) -> f r sh)
       -> DomainsOD
       -> Domains ranked
       -> DomainsOf ranked
  srevDt :: (GoodScalar r, Sh.Shape sh)
         => (forall f. ADReadyS f => Domains (RankedOf f) -> f r sh)
         -> DomainsOD
         -> Domains ranked
         -> shaped r sh
         -> DomainsOf ranked
  sfwd :: (GoodScalar r, Sh.Shape sh)
       => (forall f. ADReadyS f => Domains (RankedOf f) -> f r sh)
       -> DomainsOD
       -> Domains ranked
       -> Domains ranked
       -> shaped r sh
  -- The type mentions ADReady, so it's awkward to put this into RankedTensor,
  -- which doesn't know about DomainsTensor.
  rfold :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ranked rn n  -- ^ initial value
        -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
        -> ranked rn n
  rfoldDer :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> ranked rn n  -- ^ initial value
           -> ranked rm (1 + m)  -- ^ iteration is over the outermost dimension
           -> ranked rn n
  rfoldZip :: (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
         -> DomainsOD  -- shapes of the Domains above, not below
         -> ranked rn n
         -> Domains ranked  -- one rank higher than above
         -> ranked rn n
  rfoldZipDer :: (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> Domains f -> f rn n -> Domains f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> Domains f
                -> DomainsOf f)
            -> DomainsOD
            -> ranked rn n
            -> Domains ranked
            -> ranked rn n
  rscan :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> ranked rn n
        -> ranked rm (1 + m)
        -> ranked rn (1 + n)
  rscanDer :: (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> ranked rn n
           -> ranked rm (1 + m)
           -> ranked rn (1 + n)
  rscanZip :: (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
         -> DomainsOD  -- shapes of the Domains above, not below
         -> ranked rn n
         -> Domains ranked  -- one rank higher than above
         -> ranked rn (1 + n)
  rscanZipDer :: (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> Domains f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> Domains f -> f rn n -> Domains f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> Domains f
                -> DomainsOf f)
            -> DomainsOD
            -> ranked rn n
            -> Domains ranked
            -> ranked rn (1 + n)
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
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf (RankedOf f))
           -> shaped rn sh
           -> shaped rm (k ': shm)
           -> shaped rn sh
  sfoldZip :: (GoodScalar rn, Sh.Shape sh)
         => (forall f. ADReadyS f
             => f rn sh -> Domains (RankedOf f) -> f rn sh)
         -> DomainsOD
         -> shaped rn sh
         -> Domains (RankedOf shaped)
         -> shaped rn sh
  sfoldZipDer :: (GoodScalar rn, Sh.Shape sh)
            => (forall f. ADReadyS f
                => f rn sh -> Domains (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> Domains (RankedOf f) -> f rn sh
                -> Domains (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> Domains (RankedOf f)
                -> DomainsOf (RankedOf f))
            -> DomainsOD
            -> shaped rn sh
            -> Domains (RankedOf shaped)
            -> shaped rn sh
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
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf (RankedOf f))
           -> shaped rn sh
           -> shaped rm (k ': shm)
           -> shaped rn (1 + k ': sh)
  sscanZip :: (GoodScalar rn, Sh.Shape sh, KnownNat k)
         => (forall f. ADReadyS f
             => f rn sh -> Domains (RankedOf f) -> f rn sh)
         -> DomainsOD
         -> shaped rn sh
         -> Domains (RankedOf shaped)
         -> shaped rn (1 + k ': sh)
  sscanZipDer :: (GoodScalar rn, Sh.Shape sh, KnownNat k)
            => (forall f. ADReadyS f
                => f rn sh -> Domains (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> Domains (RankedOf f) -> f rn sh
                -> Domains (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> Domains (RankedOf f)
                -> DomainsOf (RankedOf f))
            -> DomainsOD
            -> shaped rn sh
            -> Domains (RankedOf shaped)
            -> shaped rn (1 + k ': sh)


-- * The giga-constraint

type ADReady ranked = ADReadyR ranked  -- backward compatibility

type ADReadyR ranked = ADReadyBoth ranked (ShapedOf ranked)

type ADReadyS shaped = ADReadyBoth (RankedOf shaped) shaped

-- Here is in other places reflexive closure of type equalities is created
-- manually (and not for all equalities) due to #23333.
type ADReadySmall ranked shaped =
  ( shaped ~ ShapedOf ranked, ranked ~ RankedOf shaped
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
  , DomainsTensor ranked shaped
  , DomainsTensor (PrimalOf ranked) (PrimalOf shaped) )


-- * Instances for concrete arrays

-- The DomainsTensor instance requires ADVal instance, so it's given elsewhere.

type DomainsOD = Domains (Flip OR.Array)

sizeDomainsOD :: DomainsOD -> Int
sizeDomainsOD = let f (DynamicRanked (Flip t)) = OR.size t
                    f (DynamicShaped (Flip t)) = OS.size t
                    f (DynamicRankedDummy _ proxy_sh) = Sh.sizeP proxy_sh
                    f (DynamicShapedDummy _ proxy_sh) = Sh.sizeP proxy_sh
                in V.sum . V.map f

type role DynamicScalar representational
data DynamicScalar (ranked :: RankedTensorType) where
  DynamicScalar :: GoodScalar r
                => Proxy r -> DynamicScalar ranked

instance Show (DynamicScalar ranked) where
  showsPrec d (DynamicScalar (Proxy @t)) =
    showsPrec d (typeRep @t)  -- abuse for better error messages

scalarDynamic :: DynamicTensor ranked -> DynamicScalar ranked
scalarDynamic (DynamicRanked @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShaped @r2 _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicRankedDummy @r2 _ _) = DynamicScalar @r2 Proxy
scalarDynamic (DynamicShapedDummy @r2 _ _) = DynamicScalar @r2 Proxy

shapeDynamic :: RankedTensor ranked
             => DynamicTensor ranked -> [Int]
shapeDynamic (DynamicRanked t) = shapeToList $ rshape t
shapeDynamic (DynamicShaped @_ @sh _) = Sh.shapeT @sh
shapeDynamic (DynamicRankedDummy _ proxy_sh) = Sh.shapeP proxy_sh
shapeDynamic (DynamicShapedDummy _ proxy_sh) = Sh.shapeP proxy_sh

rankDynamic :: DynamicTensor ranked -> Int
rankDynamic (DynamicRanked @_ @n _) = valueOf @n
rankDynamic (DynamicShaped @_ @sh _) = length $ Sh.shapeT @sh
rankDynamic (DynamicRankedDummy _ proxy_sh) = length $ Sh.shapeP proxy_sh
rankDynamic (DynamicShapedDummy _ proxy_sh) = length $ Sh.shapeP proxy_sh

isRankedDynamic :: DynamicTensor ranked -> Bool
isRankedDynamic DynamicRanked{} = True
isRankedDynamic DynamicShaped{} = False
isRankedDynamic DynamicRankedDummy{} = True
isRankedDynamic DynamicShapedDummy{} = False

domainsMatch :: forall f g. (RankedTensor f, RankedTensor g)
             => Domains f -> Domains g -> Bool
domainsMatch v1 v2 =
  let dynamicMatch :: DynamicTensor f -> DynamicTensor g -> Bool
      dynamicMatch t u = case (scalarDynamic @f t, scalarDynamic @g u) of
        (DynamicScalar @ru _, DynamicScalar @rt _) ->
          isJust (testEquality (typeRep @rt) (typeRep @ru))
          && shapeDynamic @f t == shapeDynamic @g u
          && isRankedDynamic @f t == isRankedDynamic @g u
  in V.length v1 == V.length v2
     && and (V.zipWith dynamicMatch v1 v2)

odFromVar :: AstDynamicVarName -> DynamicTensor (Flip OR.Array)
odFromVar (AstDynamicVarName @ty @rD @shD _) =
  case testEquality (typeRep @ty) (typeRep @Nat) of
    Just Refl -> DynamicRankedDummy @rD @shD Proxy Proxy
    _ -> DynamicShapedDummy @rD @shD Proxy Proxy

odFromSh :: forall r n. GoodScalar r
         => ShapeInt n -> DynamicTensor (Flip OR.Array)
odFromSh sh = Sh.withShapeP (shapeToList sh) $ \proxySh ->
              DynamicRankedDummy (Proxy @r) proxySh

odFromShS :: forall r sh. (GoodScalar r, Sh.Shape sh)
          => DynamicTensor (Flip OR.Array)
odFromShS = DynamicShapedDummy @r @sh Proxy Proxy

-- This is useful for when the normal main parameters to an objective
-- function are used to generate the parameter template
-- as well as when generating dummy zero parameters based on a template.
odFromDynamic :: forall ranked ranked2. RankedTensor ranked
              => DynamicTensor ranked -> DynamicTensor ranked2
odFromDynamic (DynamicRanked @r2 @n2 t) =
  let sh = rshape @ranked t
  in Sh.withShapeP (shapeToList sh) $ \(Proxy @sh2) ->
    DynamicRankedDummy @r2 @sh2 Proxy Proxy
odFromDynamic (DynamicShaped @r2 @sh2 _) =
  DynamicShapedDummy @r2 @sh2 Proxy Proxy
odFromDynamic (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
odFromDynamic (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2

fromDomainsR :: forall r n ranked.
                (RankedTensor ranked, GoodScalar r, KnownNat n)
             => Domains ranked
             -> Maybe (ranked r n, Domains ranked)
fromDomainsR params = case V.uncons params of
  Just (DynamicRanked @r2 @n2 t, rest) -> case sameNat (Proxy @n2)
                                                       (Proxy @n) of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> Just (t, rest)
      _ -> error $ "fromDomainsR: scalar mismatch in "
                   ++ show (typeRep @r2, typeRep @r)
    _ -> error "fromDomainsR: rank mismatch"
  Just (DynamicShaped{}, _) -> error "fromDomainsR: ranked from shaped"
  Just (DynamicRankedDummy @r2 @sh2 _ _, rest) -> case matchingRank @sh2 @n of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl ->
         let sh2 = listShapeToShape (Sh.shapeT @sh2)
         in Just (rzero sh2 :: ranked r2 (Sh.Rank sh2), rest)
      _ -> error "fromDomainsR: scalar mismatch"
    _ -> error "fromDomainsR: shape mismatch"
  Just (DynamicShapedDummy{}, _) -> error "fromDomainsR: ranked from shaped"
  Nothing -> Nothing

fromDomainsS :: forall r sh shaped
              . ( ShapedTensor shaped, GoodScalar r, Sh.Shape sh
                , ShapedOf (RankedOf shaped) ~ shaped )
             => Domains (RankedOf shaped)
             -> Maybe (shaped r sh,  Domains (RankedOf shaped))
fromDomainsS params = case V.uncons params of
  Just (DynamicRanked{}, _) -> error "fromDomainsS: shaped from ranked"
  Just (DynamicShaped @r2 @sh2 t, rest) -> case sameShape @sh2 @sh of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl -> Just (t, rest)
      _ -> error "fromDomainsS: scalar mismatch"
    _ -> error "fromDomainsS: shape mismatch"
  Just (DynamicRankedDummy{}, _) -> error "fromDomainsS: shaped from ranked"
  Just (DynamicShapedDummy @r2 @sh2 _ _, rest) -> case sameShape @sh2 @sh of
    Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
      Just Refl ->
        -- The dummy gets removed, so we verify its types before it does.
        Just (0 :: shaped r2 sh2, rest)
      _ -> error "fromDomainsS: scalar mismatch"
    _ -> error "fromDomainsS: shape mismatch"
  Nothing -> Nothing

unravelDynamic
  :: forall ranked. (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => DynamicTensor ranked -> [DynamicTensor ranked]
unravelDynamic (DynamicRanked @rp @p t) =
  case someNatVal $ valueOf @p - 1 of
    Just (SomeNat @p1 _) ->
      gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
      map (DynamicRanked @rp @p1) $ runravelToList t
    Nothing -> error "unravelDynamic: rank 0"
unravelDynamic (DynamicShaped @rp @sh t) = case ShapedList.shapeSh @sh of
  ZSH -> error "unravelDynamic: rank 0"
  _ :$: _ -> map DynamicShaped $ sunravelToList t
unravelDynamic (DynamicRankedDummy @rp @sh _ _) =
  withListShape (Sh.shapeT @sh) $ \(sh :: ShapeInt p) ->
    case someNatVal $ valueOf @p - 1 of
      Just (SomeNat @p1 _) ->
        gcastWith (unsafeCoerce Refl :: p :~: 1 + p1 ) $
        map (DynamicRanked @rp @p1) $ runravelToList (rzero sh)
      Nothing -> error "unravelDynamic: rank 0"
unravelDynamic (DynamicShapedDummy @rp @sh _ _) = case ShapedList.shapeSh @sh of
  ZSH -> error "unravelDynamic: rank 0"
  _ :$: _ -> map DynamicShaped $ sunravelToList (0 :: ShapedOf ranked rp sh)

unravelDomains
  :: forall ranked. (RankedTensor ranked, ShapedTensor (ShapedOf ranked))
  => Domains ranked  -- each tensor has outermost dimension size p
  -> [Domains ranked]  -- p domains; each tensor of one rank lower
unravelDomains = map V.fromList . transpose
                 . map unravelDynamic . V.toList

ravelDynamicRanked
  :: forall ranked. RankedTensor ranked
  => [DynamicTensor ranked] -> DynamicTensor ranked
ravelDynamicRanked ld = case ld of
  [] -> error "ravelDynamicRanked: empty list"
  d : _ -> case ( someNatVal
                  $ toInteger (length $ shapeDynamic d)
                , scalarDynamic d ) of
    (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
      let g :: DynamicTensor ranked -> ranked rp p1
          g (DynamicRanked @rq @q t)
            | Just Refl <- sameNat (Proxy @q) (Proxy @p1)
            , Just Refl <- testEquality (typeRep @rq)
                                        (typeRep @rp) = t
          g DynamicShaped{} =
            error "ravelDynamicRanked: DynamicShaped"
          g (DynamicRankedDummy @rq @shq _ _)
            | Just Refl <- matchingRank @shq @p1
            , Just Refl <- testEquality (typeRep @rq)
                                        (typeRep @rp) =
              withListShape (Sh.shapeT @shq)
              $ \(sh :: ShapeInt q1) ->
                  case sameNat (Proxy @q1) (Proxy @p1) of
                    Just Refl -> rzero @ranked sh
                    Nothing ->
                      error "ravelDynamicRanked: wrong rank"
          g DynamicShapedDummy{} =
            error "ravelDynamicRanked: DynamicShapedDummy"
          g _ = error "ravelDynamicRanked: wrong scalar or rank"
      in DynamicRanked $ rfromList $ map g ld
    _ -> error "ravelDynamicRanked: impossible someNatVal"

ravelDynamicShaped
  :: forall shaped.
     ( RankedTensor (RankedOf shaped), ShapedTensor shaped
     , ShapedOf (RankedOf shaped) ~ shaped )
  => [DynamicTensor (RankedOf shaped)] -> DynamicTensor (RankedOf shaped)
ravelDynamicShaped ld = case ld of
  [] -> error "ravelDynamicShaped: empty list"
  d : _ ->
    let shD = shapeDynamic d
    in Sh.withShapeP shD
       $ \(Proxy @shp) -> case ( someNatVal $ toInteger $ length ld
                               , scalarDynamic d ) of
      (Just (SomeNat @p1 _), DynamicScalar @rp _) ->
        let g :: DynamicTensor (RankedOf shaped) -> shaped rp shp
            g DynamicRanked{} =
              error "ravelDynamicShaped: DynamicRanked"
            g (DynamicShaped @rq @shq t)
              | Just Refl <- sameShape @shq @shp
              , Just Refl <- testEquality (typeRep @rq)
                                          (typeRep @rp) = t
            g DynamicRankedDummy{} =
              error "ravelDynamicShaped: DynamicRankedDummy"
            g (DynamicShapedDummy @rq @shq _ _)
              | Just Refl <- sameShape @shq @shp
              , Just Refl <- testEquality (typeRep @rq)
                                          (typeRep @rp) = 0
            g _ = error "ravelDynamicShaped: wrong scalar or rank"
        in DynamicShaped $ sfromList @_ @_ @p1 $ map g ld
      _ -> error "ravelDynamicShaped: impossible someNatVal"

ravelDynamic
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => [DynamicTensor ranked] -> DynamicTensor ranked
ravelDynamic ld = case ld of
  [] -> error "ravelDynamic: empty list"
  DynamicRanked{} : _ -> ravelDynamicRanked ld
  DynamicShaped{} : _ -> ravelDynamicShaped ld
  DynamicRankedDummy{} : _ -> ravelDynamicRanked ld
  DynamicShapedDummy{} : _ -> ravelDynamicShaped ld

ravelDomains  -- the inverse of unravelDomains
  :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
     , RankedOf (ShapedOf ranked) ~ ranked )
  => [Domains ranked] -> Domains ranked
ravelDomains = V.fromList . map ravelDynamic
               . transpose . map V.toList

mapDomainsRanked
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq q)
  -> Domains ranked -> Domains ranked
mapDomainsRanked f = V.map (mapRanked f)

mapRanked
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq q)
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked f (DynamicRanked t) = DynamicRanked $ f t
mapRanked _ DynamicShaped{} = error "mapRanked: DynamicShaped"
mapRanked f (DynamicRankedDummy @r @sh _ _) =
  withListShape (Sh.shapeT @sh) $ \sh1 ->
    DynamicRanked @r $ f (rzero sh1)
mapRanked _ DynamicShapedDummy{} = error "mapRanked: DynamicShapedDummy"

-- Hindler-Milner polymorphism is not great for existential types programming.
mapDomainsRanked01
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq (1 + q))
  -> Domains ranked -> Domains ranked
mapDomainsRanked01 f = V.map (mapRanked01 f)

mapRanked01
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq q -> ranked rq (1 + q))
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked01 f (DynamicRanked t) = DynamicRanked $ f t
mapRanked01 _ DynamicShaped{} = error "mapRanked01: DynamicShaped"
mapRanked01 f (DynamicRankedDummy @r @sh _ _) =
  withListShape (Sh.shapeT @sh) $ \sh1 ->
    DynamicRanked @r $ f (rzero sh1)
mapRanked01 _ DynamicShapedDummy{} = error "mapRanked01: DynamicShapedDummy"

mapDomainsRanked10
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq q)
  -> Domains ranked -> Domains ranked
mapDomainsRanked10 f = V.map (mapRanked10 f)

mapRanked10
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq q)
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked10 f (DynamicRanked t) = case rshape t of
  ZS -> error "mapRanked10: rank 0"
  _ :$ _ -> DynamicRanked $ f t
mapRanked10 _ _ = error "mapRanked10: not DynamicRanked"

mapDomainsRanked11
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq (1 + q))
  -> Domains ranked -> Domains ranked
mapDomainsRanked11 f = V.map (mapRanked11 f)

mapRanked11
  :: RankedTensor ranked
  => (forall rq q. (GoodScalar rq, KnownNat q)
      => ranked rq (1 + q) -> ranked rq (1 + q))
  -> DynamicTensor ranked -> DynamicTensor ranked
mapRanked11 f (DynamicRanked t) = case rshape t of
  ZS -> error "mapRanked11: rank 0"
  _ :$ _ -> DynamicRanked $ f t
mapRanked11 _ _ = error "mapRanked11: not DynamicRanked"

mapDomainsShaped11
  :: (ShapedTensor shaped, ShapedOf (RankedOf shaped) ~ shaped)
  => (forall rq kq shq. (GoodScalar rq, Sh.Shape shq, KnownNat kq)
      => shaped rq (kq ': shq) -> shaped rq (kq ': shq))
  -> Domains (RankedOf shaped) -> Domains (RankedOf shaped)
mapDomainsShaped11 f = V.map (mapShaped11 f)

mapShaped11
  :: (ShapedTensor shaped, ShapedOf (RankedOf shaped) ~ shaped)
  => (forall rq kq shq. (GoodScalar rq, Sh.Shape shq, KnownNat kq)
      => shaped rq (kq ': shq) -> shaped rq (kq ': shq))
  -> DynamicTensor (RankedOf shaped) -> DynamicTensor (RankedOf shaped)
mapShaped11 f (DynamicShaped @r t) = case sshape t of
  ZSH -> error "mapShaped11: rank 0"
  _ :$: _ -> DynamicShaped $ f t
mapShaped11 _ _ = error "mapShaped11: not DynamicShaped"

mapDomainsShaped11kk
  :: forall k k1 shaped.
     ( ShapedTensor shaped, ShapedOf (RankedOf shaped) ~ shaped
     , KnownNat k, KnownNat k1 )
  => (forall rq shq. (GoodScalar rq, Sh.Shape shq)
      => shaped rq (k ': shq) -> shaped rq (k1 ': shq))
  -> Domains (RankedOf shaped) -> Domains (RankedOf shaped)
mapDomainsShaped11kk f = V.map (mapShaped11kk f)

mapShaped11kk
  :: forall k k1 shaped.
     ( ShapedTensor shaped, ShapedOf (RankedOf shaped) ~ shaped
     , KnownNat k, KnownNat k1 )
  => (forall rq shq. (GoodScalar rq, Sh.Shape shq)
      => shaped rq (k ': shq) -> shaped rq (k1 ': shq))
  -> DynamicTensor (RankedOf shaped) -> DynamicTensor (RankedOf shaped)
mapShaped11kk f (DynamicShaped @r t) = case sshape t of
  ZSH -> error "mapShaped11kk: rank 0"
  (:$:) @n _ _ -> case sameNat (Proxy @n) (Proxy @k) of
    Just Refl -> DynamicShaped $ f t
    Nothing -> error "mapShaped11kk: wrong width"
mapShaped11kk _ _ = error "mapShaped11kk: not DynamicShaped"

index1Domains :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
                 , RankedOf (PrimalOf (ShapedOf ranked))
                   ~ RankedOf (PrimalOf ranked) )
              => Domains ranked -> IntOf ranked -> Domains ranked
index1Domains u i = V.map (`index1Dynamic` i) u

index1Dynamic :: ( RankedTensor ranked, ShapedTensor (ShapedOf ranked)
                 , RankedOf (PrimalOf (ShapedOf ranked))
                   ~ RankedOf (PrimalOf ranked) )
              => DynamicTensor ranked -> IntOf ranked -> DynamicTensor ranked
index1Dynamic u i = case u of
  DynamicRanked t -> case rshape t of
    ZS -> error "index1Dynamic: rank 0"
    _ :$ _ -> DynamicRanked $ t ! singletonIndex i
  DynamicShaped t -> case sshape t of
    ZSH -> error "index1Dynamic: rank 0"
    _ :$: _ -> DynamicShaped $ t !$ ShapedList.singletonShaped i
  DynamicRankedDummy @r @sh _ _ -> case ShapedList.shapeSh @sh of
    ZSH -> error "index1Dynamic: rank 0"
    (:$:) @_ @sh2 _ _ ->
      withListShape (Sh.shapeT @sh2) $ \(sh1 :: ShapeInt n1) ->
        DynamicRanked @r @n1 $ rzero sh1
  DynamicShapedDummy @r @sh _ _ -> case ShapedList.shapeSh @sh of
    ZSH -> error "index1Dynamic: rank 0"
    (:$:) @_ @sh2 _ _ -> DynamicShaped @r @sh2 0

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

type instance DomainsOf (Flip OR.Array) = DomainsOD

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
  rletDomainsIn _ = (&)
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

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains (Flip OR.Array) (Flip OR.Array r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains (Flip OR.Array) (Flip OR.Array Double n) #-}
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains = V.singleton . DynamicRanked
  fromDomains _aInit params = fromDomainsR @r @n params

instance ForgetShape (Flip OR.Array r n) where
  type NoShape (Flip OR.Array r n) = Flip OR.Array r n
  forgetShape = id

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

type instance DomainsOf (Flip OS.Array) = DomainsOD

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
  sletDomainsIn _ = (&)
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

instance (GoodScalar r, Sh.Shape sh)
         => AdaptableDomains (Flip OR.Array) (Flip OS.Array r sh) where
  type Value (Flip OS.Array r sh) = Flip OS.Array r sh
  toDomains = V.singleton . DynamicShaped
  fromDomains _aInit params = fromDomainsS @r @sh @(Flip OS.Array) params

instance Sh.Shape sh
         => ForgetShape (Flip OS.Array r sh) where
  type NoShape (Flip OS.Array r sh) = Flip OR.Array r (Sh.Rank sh)  -- key case
  forgetShape = Flip . Data.Array.Convert.convert . runFlip

instance (Sh.Shape sh, Numeric r, Fractional r, Random r, Num (Vector r))
         => RandomDomains (Flip OS.Array r sh) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * realToFrac range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) g1
    in (Flip arr, g2)

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- TODO2: benchmark this used for any scalar via @V.map realToFrac@
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         KnownNat n
         => AdaptableDomains (OR.Array n Double) where
  randomVals range g =
    let -- Note that hmatrix produces numbers from the range open at the top,
        -- unlike package random.
        createRandomVector n seedInt =
          LA.scale (2 * range)
          $ LA.randomVector seedInt LA.Uniform n - LA.scalar 0.5
        (i, g2) = random g
        arr = OR.fromVector $ createRandomVector (OR.sizeP (Proxy @n)) i
    in (arr, g2)
-}
