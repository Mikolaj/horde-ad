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
  , RankedTensor(..), ShapedTensor(..), ConvertTensor(..), DomainsTensor(..)
    -- * The related constraints
  , ADReady, ADReadyR, ADReadyS, ADReadySmall, ADReadyBoth, CRanked, CShaped
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Function ((&))
import           Data.Int (Int64)
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, OrderingI (..), cmpNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.Types
import           HordeAd.Internal.TensorOps
import           HordeAd.Util.ShapedList
  (ShapeSh, ShapedList (..), consShaped, shapedNat, unShapedNat)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Ranked tensor class definition

class (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRanked ranked c where
instance (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
         => CRanked ranked c where

type TensorSupports :: (Type -> Constraint) -> TensorKind k -> Constraint
type TensorSupports c f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => (c r, c (Vector r)) => c (f r y)

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Integral (IntOf ranked), CRanked ranked Num
      , TensorSupports RealFloat ranked, TensorSupports Integral ranked )
      => RankedTensor (ranked :: RankedTensorKind) where

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
  rzipWith :: ( GoodScalar r, GoodScalar r2, GoodScalar r3
              , KnownNat m, KnownNat n )
           => (ranked r n -> ranked r2 n -> ranked r3 n)
           -> ranked r (m + n) -> ranked r2 (m + n) -> ranked r3 (m + n)
  rzipWith f u v = rbuild (rshape v) (\ix -> f (u ! ix) (v ! ix))
  rzipWith1 :: (GoodScalar r, GoodScalar r2, GoodScalar r3, KnownNat n)
            => (ranked r n -> ranked r2 n -> ranked r3 n)
            -> ranked r (1 + n) -> ranked r2 (1 + n) -> ranked r3 (1 + n)
  rzipWith1 f u v = rbuild1 (rlength u) (\i -> f (u ! [i]) (v ! [i]))
  rzipWith0N :: (GoodScalar r, GoodScalar r2, GoodScalar r3, KnownNat n)
             => (ranked r 0 -> ranked r2 0 -> ranked r3 0)
             -> ranked r n -> ranked r2 n -> ranked r3 n
  rzipWith0N f u v = rbuild (rshape v) (\ix -> f (rindex0 u ix) (rindex0 v ix))
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
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => ranked r n -> DynamicExists (DynamicOf ranked)
              -> DynamicExists (DynamicOf ranked)
  rregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> AstBindings ranked
            -> (AstBindings ranked, ranked r n)
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


-- * Shaped tensor class definition

class (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where
instance
      (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CShaped shaped c where

class ( Integral (IntOf shaped), CShaped shaped Num
      , TensorSupports RealFloat shaped, TensorSupports Integral shaped )
      => ShapedTensor (shaped :: ShapedTensorKind) where

  slet :: (OS.Shape sh, OS.Shape sh2, GoodScalar r, GoodScalar r2)
       => shaped r sh -> (shaped r sh -> shaped r2 sh2)
       -> shaped r2 sh2
  slet a f = f a

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, OS.Shape sh)
         => shaped r sh -> ShapeSh sh
  sshape _ = ShapedList.shapeSh @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (OS.Rank sh))
        => shaped r sh -> Int
  srank _ = valueOf @(OS.Rank sh)
  ssize :: forall sh r. (GoodScalar r, OS.Shape sh) => shaped r sh -> Int
  ssize _ = OS.sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => shaped r (n ': sh) -> Int
  slength _ = valueOf @n
  sminIndex :: ( GoodScalar r, GoodScalar r2, OS.Shape sh, KnownNat n
               , OS.Shape (OS.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (OS.Init (n ': sh))
  smaxIndex :: ( GoodScalar r, GoodScalar r2, OS.Shape sh, KnownNat n
               , OS.Shape (OS.Init (n ': sh)) )  -- partial
            => shaped r (n ': sh) -> shaped r2 (OS.Init (n ': sh))
  sfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, OS.Shape sh)
         => shaped r sh -> shaped r2 sh
    -- not IntSh, because the integer can be negative
    -- TODO: shall we make it abs (floor v)?
  siota :: forall n r. (GoodScalar r, KnownNat n)
        => shaped r '[n]  -- from 0 to n - 1

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- indicates the rank of the codomain, if bounded.
  sindex, (!$) :: forall r sh1 sh2.
                  ( GoodScalar r, OS.Shape sh1, OS.Shape sh2
                  , OS.Shape (sh1 OS.++ sh2) )
               => shaped r (sh1 OS.++ sh2) -> IndexSh shaped sh1
               -> shaped r sh2
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, OS.Shape sh1)
          => shaped r sh1 -> IndexSh shaped sh1
          -> shaped r '[]
  sindex0 = gcastWith (unsafeCoerce Refl :: sh1 OS.++ '[] :~: sh1)
              sindex
  ssum :: forall r n sh. (GoodScalar r, KnownNat n, OS.Shape sh)
       => shaped r (n ': sh) -> shaped r sh
  ssum0 :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
        => shaped r sh -> shaped r '[]
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
        => shaped r sh -> shaped r sh -> shaped r '[]
  sdot0 t u = ssum (sflatten (t * u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ consShaped i ZSH))
  smatmul2 :: forall r n m p. (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Proxy @'[2, 1, 0]) (sreplicate @shaped @r @p m1)
          * stranspose (Proxy @'[1, 0]) (sreplicate @shaped @r @m m2))
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, OS.Shape sh2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh), OS.Shape (sh2 OS.++ OS.Drop p sh) )
    => shaped r (sh2 OS.++ OS.Drop p sh)
    -> (IndexSh shaped sh2 -> IndexSh shaped (OS.Take p sh))
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh) )
    => shaped r (n2 ': OS.Drop p sh)
    -> (IntSh shaped n2 -> IndexSh shaped (OS.Take p sh))
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (ShapedList.unconsContShaped f)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  sfromList :: (GoodScalar r, KnownNat n, OS.Shape sh)
            => [shaped r sh] -> shaped r (n ': sh)
  sfromList0N :: forall r sh.
                 (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
              => [shaped r '[]] -> shaped r sh
  sfromList0N = sreshape @shaped @r @'[OS.Size sh] @sh . sfromList
  sfromVector :: (GoodScalar r, KnownNat n, OS.Shape sh)
              => Data.Vector.Vector (shaped r sh) -> shaped r (n ': sh)
  sfromVector v = sfromList (V.toList v)  -- horribly inefficient for large vs
  sfromVector0N :: forall r sh.
                   (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
                => Data.Vector.Vector (shaped r '[])
                -> shaped r sh
  sfromVector0N = sreshape @shaped @r @'[OS.Size sh] @sh . sfromVector
  sunravelToList :: (GoodScalar r, KnownNat n, OS.Shape sh)
                 => shaped r (n ': sh) -> [shaped r sh]
  sreplicate :: (GoodScalar r, KnownNat n, OS.Shape sh)
             => shaped r sh -> shaped r (n ': sh)
  sreplicate0N :: forall r sh.
                  (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
               => shaped r '[] -> shaped r sh
  sreplicate0N = sreshape @shaped @r @'[OS.Size sh] @sh
                 . sreplicate @shaped @r @(OS.Size sh)
  sappend :: (GoodScalar r, KnownNat m, KnownNat n, OS.Shape sh)
          => shaped r (m ': sh) -> shaped r (n ': sh)
          -> shaped r ((m + n) ': sh)
  sslice :: (GoodScalar r, KnownNat i, KnownNat n, KnownNat k, OS.Shape sh)
         => Proxy i -> Proxy n
         -> shaped r (i + n + k ': sh) -> shaped r (n ': sh)
  suncons :: forall r n sh. (GoodScalar r, KnownNat n, OS.Shape sh)
          => shaped r (n ': sh) -> Maybe (shaped r sh, shaped r (n - 1 ': sh))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just ( v !$ (0 :$: ZSH)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    LTI -> Just ( v !$ (0 :$: ZSH)
                , sslice @shaped @r @1 @(n - 1) @0 Proxy Proxy v )
    _ -> Nothing
  sreverse :: (GoodScalar r, KnownNat n, OS.Shape sh)
           => shaped r (n ': sh) -> shaped r (n ': sh)
  str :: ( GoodScalar r, KnownNat n, KnownNat m, OS.Shape sh
         , KnownNat (OS.Rank sh) )
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose (Proxy @'[1, 0])
  stranspose :: forall perm r sh.
                ( OS.Permutation perm, OS.Shape perm, OS.Shape sh
                , KnownNat (OS.Rank sh), OS.Shape (OS.Permute perm sh)
                , OS.Rank perm <= OS.Rank sh, GoodScalar r )
             => Proxy perm -> shaped r sh -> shaped r (OS.Permute perm sh)
  sflatten :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[OS.Size sh]
  sflatten = sreshape
  sreshape :: ( GoodScalar r, OS.Shape sh, OS.Shape sh2
              , OS.Size sh ~ OS.Size sh2 )
           => shaped r sh -> shaped r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  sbuild :: forall r m sh.
            (GoodScalar r, OS.Shape sh, OS.Shape (OS.Take m sh))
         => (IndexSh shaped (OS.Take m sh) -> shaped r (OS.Drop m sh))
         -> shaped r sh
  sbuild =
    let buildSh
          :: forall sh1.
             ShapeSh sh1 -> ShapeSh (sh1 OS.++ OS.Drop m sh)
          -> (IndexSh shaped sh1 -> shaped r (OS.Drop m sh))
          -> shaped r (sh1 OS.++ OS.Drop m sh)
        buildSh sh1 sh1m f = case (sh1, sh1m) of
          (ZSH, _) -> f ZSH
          (_ :$: sh2, _ :$: sh2m) ->
            let g i = buildSh sh2 sh2m (f . consShaped i)
            in sbuild1 g
    in gcastWith (unsafeCoerce Refl
                  :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
       $ buildSh (ShapedList.shapeSh @(OS.Take m sh)) (ShapedList.shapeSh @sh)
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, OS.Shape sh)
          => (IntSh shaped n -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: forall r r2 m sh.
          ( GoodScalar r, GoodScalar r2, KnownNat m
          , OS.Shape sh, OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
       => (shaped r (OS.Drop m sh) -> shaped r2 (OS.Drop m sh))
       -> shaped r sh -> shaped r2 sh
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r r2 sh n.
           (GoodScalar r, GoodScalar r2, KnownNat n, OS.Shape sh)
        => (shaped r sh -> shaped r2 sh)
        -> shaped r (n ': sh) -> shaped r2 (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ consShaped i ZSH))
  smap0N :: forall r r2 sh.
            (GoodScalar r, GoodScalar r2, OS.Shape sh, KnownNat (OS.Rank sh))
         => (shaped r '[] -> shaped r2 '[]) -> shaped r sh -> shaped r2 sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ sbuild @shaped @r2 @(OS.Rank sh) (f . sindex0 v)
  szipWith :: forall r r2 r3 m sh.
              ( GoodScalar r, GoodScalar r2, GoodScalar r3
              , KnownNat m, OS.Shape sh
              , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
           => (shaped r (OS.Drop m sh)
               -> shaped r2 (OS.Drop m sh)
               -> shaped r3 (OS.Drop m sh))
           -> shaped r sh -> shaped r2 sh -> shaped r3 sh
  szipWith f u v = gcastWith (unsafeCoerce Refl
                              :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
                   $ sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r r2 r3 sh n.
               ( GoodScalar r, GoodScalar r2, GoodScalar r3
               , KnownNat n, OS.Shape sh )
            => (shaped r sh -> shaped r2 sh -> shaped r3 sh)
            -> shaped r (n ': sh) -> shaped r2 (n ': sh) -> shaped r3 (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ consShaped i ZSH)
                                     (v !$ consShaped i ZSH))
  szipWith0N :: forall r r2 r3 sh.
                ( GoodScalar r, GoodScalar r2, GoodScalar r3
                , OS.Shape sh, KnownNat (OS.Rank sh) )
             => (shaped r '[] -> shaped r2 '[] -> shaped r3 '[])
             -> shaped r sh -> shaped r2 sh -> shaped r3 sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ sbuild @shaped @r3 @(OS.Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  sgather
    :: forall r sh2 p sh.
       ( GoodScalar r, OS.Shape sh2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh), OS.Shape (sh2 OS.++ OS.Drop p sh) )
    => shaped r sh
    -> (IndexSh shaped sh2 -> IndexSh shaped (OS.Take p sh))
    -> shaped r (sh2 OS.++ OS.Drop p sh)
  sgather1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh) )
    => shaped r sh
    -> (IntSh shaped n2 -> IndexSh shaped (OS.Take p sh))
    -> shaped r (n2 ': OS.Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (ShapedList.unconsContShaped f)
  scast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, OS.Shape sh)
        => shaped r1 sh -> shaped r2 sh
  sfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, OS.Shape sh)
                => shaped r1 sh -> shaped r2 sh
  sconst :: (GoodScalar r, OS.Shape sh) => OS.Array sh r -> shaped r sh

  -- ** No serviceable parts beyond this point ** --

  sscaleByScalar
    :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v * sreplicate0N s
  ssumIn :: ( GoodScalar r, OS.Shape sh, KnownNat n, KnownNat m
            , KnownNat (OS.Rank sh) )
         => shaped r (n ': m ': sh) -> shaped r (n ': sh)
  ssumIn = ssum . str
    -- TODO: generalize, replace by stride analysis, etc.
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => shaped r '[n, m] -> shaped r '[n, m] -> shaped r '[n]
  sdot1In t u = ssumIn (t * u)
    -- TODO: generalize, replace by stride analysis, etc.
  sletWrap :: (GoodScalar r, OS.Shape sh)
           => ADShare -> shaped r sh -> shaped r sh
  sletWrap _l u = u
  sletUnwrap :: shaped r sh -> (ADShare, shaped r sh)
  sletUnwrap u = (emptyADShare, u)
  saddDynamic :: forall sh r. (GoodScalar r, OS.Shape sh)
              => shaped r sh -> DynamicExists (DynamicOf shaped)
              -> DynamicExists (DynamicOf shaped)
  sregister :: (GoodScalar r, OS.Shape sh)
            => shaped r sh -> AstBindings shaped
            -> (AstBindings shaped, shaped r sh)
  sregister r l = (l, r)

  -- Primal/dual things.
  sconstant :: (GoodScalar r, OS.Shape sh)
            => PrimalOf shaped r sh -> shaped r sh
  sprimalPart :: (GoodScalar r, OS.Shape sh)
              => shaped r sh -> PrimalOf shaped r sh
  sdualPart :: (GoodScalar r, OS.Shape sh)
            => shaped r sh -> DualOf shaped r sh
  sD :: (GoodScalar r, OS.Shape sh)
     => PrimalOf shaped r sh -> DualOf shaped r sh -> shaped r sh
  sScale :: (GoodScalar r, OS.Shape sh)
         => PrimalOf shaped r sh -> DualOf shaped r sh -> DualOf shaped r sh


-- * ConvertTensor and DomainsTensor class definitions

class ( DynamicOf ranked ~ DynamicOf shaped
      , DynamicOf shaped ~ DynamicOf ranked )
      => ConvertTensor (ranked :: RankedTensorKind)
                       (shaped :: ShapedTensorKind)
                       | ranked -> shaped, shaped -> ranked where
  tfromD :: (GoodScalar r, KnownNat n)
         => DynamicOf ranked r -> ranked r n
  tfromS :: (GoodScalar r, OS.Shape sh)
         => shaped r sh -> ranked r (OS.Rank sh)
  dfromR :: (GoodScalar r, KnownNat n)
         => ranked r n -> DynamicOf ranked r
  dfromS :: (GoodScalar r, OS.Shape sh)
         => shaped r sh -> DynamicOf shaped r
  sfromR :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => ranked r (OS.Rank sh) -> shaped r sh
  sfromD :: (GoodScalar r, OS.Shape sh)
         => DynamicOf shaped r -> shaped r sh
  ddummy :: Numeric r => DynamicOf ranked r
  dshape :: GoodScalar r => DynamicOf ranked r -> [Int]

class DomainsTensor (ranked :: RankedTensorKind)
                    (shaped :: ShapedTensorKind)
                    | ranked -> shaped, shaped -> ranked where
  dmkDomains :: Domains (DynamicOf ranked) -> DomainsOf ranked
  rletDomainsOf :: KnownNat n
                => DomainsOf ranked
                -> (DomainsOf ranked -> ranked r n)
                -> ranked r n
  rletToDomainsOf :: (GoodScalar r, KnownNat n)
                  => ranked r n
                  -> (ranked r n -> DomainsOf ranked)
                  -> DomainsOf ranked
  sletDomainsOf :: OS.Shape sh
                => DomainsOf ranked
                -> (DomainsOf ranked -> ShapedOf ranked r sh)
                -> ShapedOf ranked r sh
  sletToDomainsOf :: (GoodScalar r, OS.Shape sh)
                  => ShapedOf ranked r sh
                  -> (ShapedOf ranked r sh -> DomainsOf ranked)
                  -> DomainsOf ranked
  -- The second argument is only used to determine tensor shapes
  -- and the third has to have the same shapes as the second.
  --
  -- The function argument needs to be quantified (or an AST term),
  -- because otherwise in the ADVal instance one could put an illegal
  -- InputR there, confusing two levels of contangents.
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> Domains (DynamicOf ranked)
       -> DomainsOf ranked


-- * The giga-constraint

class (forall yc. KnownNat yc => c (f r yc)) => YRanked f r c where
instance
      (forall yc. KnownNat yc => c (f r yc)) => YRanked f r c where

class (forall yd. OS.Shape yd => c (f r yd)) => YShaped f r c where
instance
      (forall yd. OS.Shape yd => c (f r yd)) => YShaped f r c where

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
  , ConvertTensor ranked shaped
  , ConvertTensor (PrimalOf ranked) (PrimalOf shaped)
  , CRanked ranked Show, CRanked (PrimalOf ranked) Show
  , CShaped shaped Show, CShaped (PrimalOf shaped) Show
  , YRanked ranked Int64 Integral, YShaped shaped Int64 Integral
  )

type ADReadyBoth ranked shaped =
  ( ADReadySmall ranked shaped
-- TODO: this doesn't type-check and not because rrev uses it,
-- but probably because ADVal instance of DomainsTensor uses ADReady
-- at one more ADVal nesting level:
--, DomainsTensor ranked shaped
-- so we can't nest rrev right now
  , DomainsTensor (PrimalOf ranked) (PrimalOf shaped) )


-- * Instances for concrete dynamic arrays

type instance RankedOf (Clown OD.Array) = Flip OR.Array

type instance ShapedOf (Clown OD.Array) = Flip OS.Array

type instance DynamicOf (Clown OD.Array) = OD.Array

type instance DomainsOf (Clown OD.Array) = DomainsOD


-- * Ranked tensor class instance for concrete arrays

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

type instance DynamicOf (Flip OR.Array) = OD.Array

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

  rscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  rsumIn = Flip . tsumInR . runFlip
  rdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  rconst = Flip
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => Flip OR.Array r n -> DynamicExists OD.Array
              -> DynamicExists OD.Array
  raddDynamic r (DynamicExists @r2 d) = DynamicExists $
    if isTensorDummyD d then dfromR r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromR @(Flip OR.Array) @(Flip OS.Array) @r r + d
      _ -> error "raddDynamic: type mismatch"

  rconstant = id
  rprimalPart = id
  rdualPart _ = DummyDual
  rD u _ = u
  rScale _ _ = DummyDual

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains OD.Array (Flip OR.Array r n) where
  {-# SPECIALIZE instance
      KnownNat n
      => AdaptableDomains OD.Array (Flip OR.Array Double n) #-}
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains a = V.singleton $ DynamicExists $ dfromR a
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if isTensorDummyD a then Just (rzero (rshape aInit), rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> let !aR = tfromD @(Flip OR.Array) @(Flip OS.Array) @r a
                       in Just (aR, rest)
          _ -> error $ "fromDomains: type mismatch: "
                       ++ show (typeRep @r) ++ " " ++ show (typeRep @r2)
    Nothing -> Nothing

instance ForgetShape (Flip OR.Array r n) where
  type NoShape (Flip OR.Array r n) = Flip OR.Array r n
  forgetShape = id


-- * Shaped tensor class instance for concrete arrays

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

type instance DynamicOf (Flip OS.Array) = OD.Array

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

  sscaleByScalar s v =
    Flip $ tscaleByScalarS (tunScalarS $ runFlip s) (runFlip v)
  ssumIn = Flip . tsumInS . runFlip
  sdot1In u v = Flip $ tdot1InS (runFlip u) (runFlip v)
  sconst = Flip
  saddDynamic :: forall r sh. (GoodScalar r, OS.Shape sh)
              => Flip OS.Array r sh -> DynamicExists OD.Array
              -> DynamicExists OD.Array
  saddDynamic r (DynamicExists @r2 d) = DynamicExists $
    if isTensorDummyD d then dfromS r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromS @(Flip OR.Array) @(Flip OS.Array) @r r + d
      _ -> error "saddDynamic: type mismatch"

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual

instance (GoodScalar r, OS.Shape sh)
         => AdaptableDomains OD.Array (Flip OS.Array r sh) where
  type Value (Flip OS.Array r sh) = Flip OS.Array r sh
  toDomains a = V.singleton $ DynamicExists $ dfromS a
  fromDomains _aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if isTensorDummyD a then Just (0, rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> let !aS = sfromD @(Flip OR.Array) @(Flip OS.Array) @r a
                       in Just (aS, rest)
          _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

instance OS.Shape sh
         => ForgetShape (Flip OS.Array r sh) where
  type NoShape (Flip OS.Array r sh) = Flip OR.Array r (OS.Rank sh)  -- key case
  forgetShape = Flip . Data.Array.Convert.convert . runFlip

instance (OS.Shape sh, Numeric r, Fractional r, Random r, Num (Vector r))
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


-- * ConvertTensor and DomainsTensor instances for concrete arrays

instance ConvertTensor (Flip OR.Array) (Flip OS.Array) where
  tfromD = Flip . Data.Array.Convert.convert
  tfromS = Flip . Data.Array.Convert.convert . runFlip
  dfromR = Data.Array.Convert.convert . runFlip
  dfromS = Data.Array.Convert.convert . runFlip
  sfromR = Flip . Data.Array.Convert.convert . runFlip
  sfromD = Flip . Data.Array.Convert.convert
  ddummy = dummyTensorD
  dshape = OD.shapeL

instance DomainsTensor (Flip OR.Array) (Flip OS.Array) where
  dmkDomains = id
  rletDomainsOf = (&)
  rletToDomainsOf = (&)
  sletDomainsOf = (&)
  sletToDomainsOf = (&)

  rrev _ = undefined  -- TODO?
