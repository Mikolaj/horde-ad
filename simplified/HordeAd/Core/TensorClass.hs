{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
{-# LANGUAGE ImpredicativeTypes #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( ShapeInt, ShapeSh, DynamicOf
  , ShapedTensor(..), RankedTensor(..), ConvertTensor(..), DomainsTensor(..)
  , ADReady, ADReadyS, ADRanked, ADShaped
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
import           Data.Kind (Constraint, Type)
import           Data.List (foldl1')
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
import           HordeAd.Core.ShapedList
  (ShapeSh, ShapedList (..), consShaped, shapedNat, unShapedNat)
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorOps
import           HordeAd.Core.Types

-- * Ranked tensor class definition

class (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRankedR ranked c where
instance (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
         => CRankedR ranked c where

type family DynamicOf (f :: TensorKind k) :: Type -> Type

type instance DynamicOf (Clown OD.Array) = OD.Array

type instance DynamicOf (Clown (AstDynamic s)) = AstDynamic s

type instance RankedOf (Clown OD.Array) = Flip OR.Array

type instance ShapedOf (Clown OD.Array) = Flip OS.Array

type TensorSupports :: (Type -> Constraint) -> TensorKind k -> Constraint
type TensorSupports c f =
  forall r y. (GoodScalar r, HasSingletonDict y)
              => (c r, c (Vector r)) => c (f r y)

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class ( Integral (IntOf ranked), CRankedR ranked Num
      , TensorSupports RealFloat ranked, TensorSupports Integral ranked )
      => RankedTensor (ranked :: RankedTensorKind) where

  tlet :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2)
       => ranked r n -> (ranked r n -> ranked r2 m)
       -> ranked r2 m
  tlet a f = f a

  -- Integer codomain
  tshape :: (GoodScalar r, KnownNat n) => ranked r n -> ShapeInt n
  trank :: forall r n. (GoodScalar r, KnownNat n) => ranked r n -> Int
  trank _ = valueOf @n
  tsize :: (GoodScalar r, KnownNat n) => ranked r n -> Int
  tsize = sizeShape . tshape
  tlength :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> Int
  tlength v = case tshape v of
    ZS -> error "tlength: impossible pattern needlessly required"
    k :$ _ -> k
  tminIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  tmaxIndex :: (GoodScalar r, GoodScalar r2, KnownNat n)
            => ranked r (1 + n) -> ranked r2 n  -- partial
  tfloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
         => ranked r n -> ranked r2 n
  tiota :: ranked r 1  -- 0, 1 .. infinity
  tiota = undefined  -- infinite, hence diverges; don't override

  -- Typically scalar (rank 0) codomain or a generalization of such
  -- an operation, often a tensor reduction. A number suffix in the name
  -- may indicate the rank of the codomain, if bounded.
  tindex, (!) :: (GoodScalar r, KnownNat m, KnownNat n)
              => ranked r (m + n) -> IndexOf ranked m -> ranked r n
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
  tindex0 :: (GoodScalar r, KnownNat m)
          => ranked r m -> IndexOf ranked m -> ranked r 0
  tindex0 = tindex
  tsum :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r n
  tsum0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 0
  tsum0 = tsum . tflatten
  tdot0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r n -> ranked r 0
  tdot0 t u = tsum (tflatten (t * u))
  tmatvecmul :: GoodScalar r => ranked r 2 -> ranked r 1 -> ranked r 1
-- How to generalize (#69)? The few straightforward generalizations
-- differ in types but all are far from matmul2.
  tmatvecmul m v = tbuild1 (tlength m) (\i -> tdot0 v (m ! [i]))
-- tmatvecmul m v = tflatten $ tmap1 (treplicate 1 . tdot0 v) m
  tmatmul2 :: GoodScalar r
           => ranked r 2 -> ranked r 2 -> ranked r 2
-- How to generalize to tmatmul (#69)?
-- Just tmatmul2 the two outermost dimensions?
-- tmatmul2 m1 m2 = tmap1 (tmatvecmul (ttr m2)) m1
-- tmatmul2 m1 m2 = tbuild1 (tlength m1) (\i -> tmatvecmul (ttr m2) (m1 ! [i]))
  tmatmul2 m1 m2 = case tshape m2 of
    _ :$ width2 :$ ZS -> tsum (ttranspose [2,1,0] (treplicate width2 m1)
                               * ttranspose [1,0] (treplicate (tlength m1) m2))
    _ -> error "impossible pattern needlessly required"
  tscatter :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> ranked r (m + n)
           -> (IndexOf ranked m -> IndexOf ranked p)
           -> ranked r (p + n)
  tscatter1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
            => ShapeInt (p + n) -> ranked r (1 + n)
            -> (IntOf ranked -> IndexOf ranked p)
            -> ranked r (p + n)
  tscatter1 sh v f = tscatter @ranked @r @1 sh v
                              (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined).
  tfromList :: (GoodScalar r, KnownNat n)
            => [ranked r n] -> ranked r (1 + n)
  tfromList0N :: (GoodScalar r, KnownNat n)
              => ShapeInt n -> [ranked r 0] -> ranked r n
  tfromList0N sh = treshape sh . tfromList
  tfromVector :: (GoodScalar r, KnownNat n)
              => Data.Vector.Vector (ranked r n) -> ranked r (1 + n)
  tfromVector v = tfromList (V.toList v)  -- horribly inefficient for large vs
  tfromVector0N :: (GoodScalar r, KnownNat n)
                => ShapeInt n -> Data.Vector.Vector (ranked r 0) -> ranked r n
  tfromVector0N sh = treshape sh . tfromVector
  treplicate :: (GoodScalar r, KnownNat n)
             => Int -> ranked r n -> ranked r (1 + n)
  treplicate0N :: (GoodScalar r, KnownNat n)
               => ShapeInt n -> ranked r 0 -> ranked r n
  treplicate0N sh = treshape sh . treplicate (sizeShape sh)
  tappend :: (GoodScalar r, KnownNat n)
          => ranked r (1 + n) -> ranked r (1 + n) -> ranked r (1 + n)
  tconcat :: (GoodScalar r, KnownNat n)
          => [ranked r (1 + n)] -> ranked r (1 + n)
  tconcat = foldr1 tappend
  tslice :: (GoodScalar r, KnownNat n)
         => Int -> Int -> ranked r (1 + n) -> ranked r (1 + n)
  tuncons :: (GoodScalar r, KnownNat n)
          => ranked r (1 + n) -> Maybe (ranked r n, ranked r (1 + n))
  tuncons v = case tshape v of
                ZS -> Nothing
                len :$ _ -> Just (v ! [0], tslice 1 (len - 1) v)
  treverse :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r (1 + n)
  ttr :: (GoodScalar r, KnownNat n) => ranked r (2 + n) -> ranked r (2 + n)
  ttr = ttranspose [1, 0]
  ttranspose :: (GoodScalar r, KnownNat n)
             => Permutation -> ranked r n -> ranked r n
  tflatten :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 1
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ranked r n -> ranked r m
  tbuild :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
         => ShapeInt (m + n) -> (IndexOf ranked m -> ranked r n)
         -> ranked r (m + n)
  tbuild sh0 f0 =
    let buildSh :: KnownNat m1
                => ShapeInt m1 -> (IndexOf ranked m1 -> ranked r n)
                -> ranked r (m1 + n)
        buildSh ZS f = f ZI
        buildSh (k :$ sh) f =
          let g i = buildSh sh (\ix -> f (i :. ix))
          in tbuild1 k g
    in buildSh (takeShape @m @n sh0) f0
  tbuild1 :: (GoodScalar r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf ranked -> ranked r n) -> ranked r (1 + n)
  tmap :: (GoodScalar r, GoodScalar r2, KnownNat m, KnownNat n)
       => (ranked r n -> ranked r2 n)
       -> ranked r (m + n) -> ranked r2 (m + n)
  tmap f v = tbuild (tshape v) (\ix -> f (v ! ix))
  tmap1 :: (GoodScalar r, GoodScalar r2, KnownNat n)
        => (ranked r n -> ranked r2 n)
        -> ranked r (1 + n) -> ranked r2 (1 + n)
  tmap1 f u = tbuild1 (tlength u) (\i -> f (u ! [i]))
  tmap0N :: (GoodScalar r, GoodScalar r2, KnownNat n)
         => (ranked r 0 -> ranked r2 0) -> ranked r n -> ranked r2 n
  tmap0N f v = tbuild (tshape v) (\ix -> f $ tindex0 v ix)
  tzipWith :: ( GoodScalar r, GoodScalar r2, GoodScalar r3
              , KnownNat m, KnownNat n )
           => (ranked r n -> ranked r2 n -> ranked r3 n)
           -> ranked r (m + n) -> ranked r2 (m + n) -> ranked r3 (m + n)
  tzipWith f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tzipWith1 :: (GoodScalar r, GoodScalar r2, GoodScalar r3, KnownNat n)
            => (ranked r n -> ranked r2 n -> ranked r3 n)
            -> ranked r (1 + n) -> ranked r2 (1 + n) -> ranked r3 (1 + n)
  tzipWith1 f u v = tbuild1 (tlength u) (\i -> f (u ! [i]) (v ! [i]))
  tzipWith0N :: (GoodScalar r, GoodScalar r2, GoodScalar r3, KnownNat n)
             => (ranked r 0 -> ranked r2 0 -> ranked r3 0)
             -> ranked r n -> ranked r2 n -> ranked r3 n
  tzipWith0N f u v = tbuild (tshape v) (\ix -> f (tindex0 u ix) (tindex0 v ix))
  tgather :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
          => ShapeInt (m + n) -> ranked r (p + n)
          -> (IndexOf ranked m -> IndexOf ranked p)
          -> ranked r (m + n)
  tgather1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
           => Int -> ranked r (p + n)
           -> (IntOf ranked -> IndexOf ranked p)
           -> ranked r (1 + n)
  tgather1 k v f = tgather @ranked @r @1 (k :$ dropShape (tshape v)) v
                           (\(i :. ZI) -> f i)
  tcast :: (RealFrac r1, RealFrac r2, GoodScalar r1, GoodScalar r2, KnownNat n)
        => ranked r1 n -> ranked r2 n
  tfromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                => ranked r1 n -> ranked r2 n
  tconst :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n

  -- Prevents wrong shape in @0@ with ranked (but not shaped) tensors
  -- at any rank greater than zero.
  tzero :: (GoodScalar r, KnownNat n)
        => ShapeInt n -> ranked r n
  tzero sh = treplicate0N sh 0

  -- ** No serviceable parts beyond this point ** --

  tsumOfList :: (GoodScalar r, KnownNat n)
             => [ranked r n] -> ranked r n  -- TODO: declare nonempty
  tsumOfList [] = 0
  tsumOfList l = foldl1' (+) l  -- avoid unknown shape of @0@ in @sum@
  tscaleByScalar :: (GoodScalar r, KnownNat n)
                 => ranked r 0 -> ranked r n -> ranked r n
  tscaleByScalar s v = v * treplicate0N (tshape v) s
  tsumIn :: (GoodScalar r, KnownNat n) => ranked r (2 + n) -> ranked r (1 + n)
  tsumIn = tsum . ttr
    -- TODO: generalize, replace by stride analysis, etc.
  tdot1In :: GoodScalar r => ranked r 2 -> ranked r 2 -> ranked r 1
  tdot1In t u = tsumIn (t * u)
    -- TODO: generalize, replace by stride analysis, etc.
  tletWrap :: (GoodScalar r, KnownNat n)
           => ADShare -> ranked r n -> ranked r n
  tletWrap _l u = u
  tletUnwrap :: ranked r n -> (ADShare, ranked r n)
  tletUnwrap u = (emptyADShare, u)
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => ranked r n -> DynamicExists (DynamicOf ranked)
              -> DynamicExists (DynamicOf ranked)
  tregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> [(AstId, DynamicExists (DynamicOf ranked))]
            -> ([(AstId, DynamicExists (DynamicOf ranked))], ranked r n)
  tregister r l = (l, r)

  -- Primal/dual things.
  tconstant :: (GoodScalar r, KnownNat n) => PrimalOf ranked r n -> ranked r n
  tprimalPart :: (GoodScalar r, KnownNat n)
              => ranked r n -> PrimalOf ranked r n
  tdualPart :: (GoodScalar r, KnownNat n)
            => ranked r n -> DualOf ranked r n
  tD :: (GoodScalar r, KnownNat n)
     => PrimalOf ranked r n -> DualOf ranked r n -> ranked r n
  tScale :: (GoodScalar r, KnownNat n)
         => PrimalOf ranked r n -> DualOf ranked r n -> DualOf ranked r n
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?


-- * Shaped tensor class definition

class (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CRankedS shaped c where
instance
      (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CRankedS shaped c where

class ( Integral (IntOf shaped), CRankedS shaped Num
      , TensorSupports RealFloat shaped, TensorSupports Integral shaped )
      => ShapedTensor (shaped :: ShapedTensorKind) where

  slet :: (OS.Shape sh, OS.Shape sh2, GoodScalar r)
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
            $ sindex
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
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (consShaped i ZSH)))
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
  smap1 f u = sbuild1 (\i -> f (u !$ (consShaped i ZSH)))
  smap0N :: forall r r2 sh.
            (GoodScalar r, GoodScalar r2, OS.Shape sh, KnownNat (OS.Rank sh))
         => (shaped r '[] -> shaped r2 '[]) -> shaped r sh -> shaped r2 sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ sbuild @shaped @r2 @(OS.Rank sh) (\ix -> f $ sindex0 v ix)
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
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (consShaped i ZSH))
                                     (v !$ (consShaped i ZSH)))
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

  ssumOfList :: (GoodScalar r, OS.Shape sh)
             => [shaped r sh] -> shaped r sh  -- TODO: declare nonempty
  ssumOfList = sum
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
            => shaped r sh -> [(AstId, DynamicExists (DynamicOf shaped))]
            -> ([(AstId, DynamicExists (DynamicOf shaped))], shaped r sh)
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

class ( RankedOf shaped ~ ranked, ShapedOf ranked ~ shaped
      , DynamicOf ranked ~ DynamicOf shaped
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
  disDummy :: Numeric r => DynamicOf ranked r -> Bool
  dshape :: GoodScalar r => DynamicOf ranked r -> [Int]

class DomainsTensor (ranked :: RankedTensorKind)
                    (shaped :: ShapedTensorKind)
                    (domainsOf :: Type)
                    | ranked -> shaped domainsOf
                    , shaped -> ranked domainsOf
                    , domainsOf -> ranked shaped where
  dmkDomains :: Domains (DynamicOf ranked) -> domainsOf
  rletDomainsOf :: KnownNat n
                => domainsOf -> (domainsOf -> ranked r n)-> ranked r n
  rletToDomainsOf :: (GoodScalar r, KnownNat n)
                  => ranked r n -> (ranked r n -> domainsOf) -> domainsOf
  sletDomainsOf :: OS.Shape sh
                => domainsOf -> (domainsOf -> shaped r sh) -> shaped r sh
  sletToDomainsOf :: (GoodScalar r, OS.Shape sh)
                  => shaped r sh -> (shaped r sh -> domainsOf) -> domainsOf


-- * The giga-constraint

type ADReady ranked r = ADRanked ranked r  -- backward compatibility

type ADRanked ranked r = (ADReadyR ranked r, ADReadyS (ShapedOf ranked) r)

type ADShaped shaped r = (ADReadyR (RankedOf shaped) r, ADReadyS shaped r)

type ADReadyR ranked r =
  ( RankedTensor ranked, GoodScalar r, RankedTensor (PrimalOf ranked)
  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked
  , PrimalOf (PrimalOf ranked) ~ PrimalOf ranked
  , IfF ranked, IfF (ShapedOf ranked), IfF (PrimalOf ranked)
  , EqF ranked, EqF (ShapedOf ranked), EqF (PrimalOf ranked)
  , OrdF ranked, OrdF (ShapedOf ranked), OrdF (PrimalOf ranked)
  , Boolean (BoolOf ranked)
  , BoolOf ranked ~ BoolOf (ShapedOf ranked)
  , BoolOf ranked ~ BoolOf (PrimalOf ranked)
  )

type ADReadyS shaped r =
  ( ShapedTensor shaped, GoodScalar r, ShapedTensor (PrimalOf shaped)
  , ShapedOf (PrimalOf shaped) ~ PrimalOf shaped
  , PrimalOf (PrimalOf shaped) ~ PrimalOf shaped
  , PrimalOf (PrimalOf (RankedOf shaped)) ~ PrimalOf (RankedOf shaped)
  , RankedOf (PrimalOf (RankedOf shaped)) ~ PrimalOf (RankedOf shaped)
  , IfF shaped, IfF (RankedOf shaped), IfF (PrimalOf shaped)
  , IfF (PrimalOf (RankedOf shaped))
  , EqF shaped, EqF (RankedOf shaped), EqF (PrimalOf shaped)
  , EqF (PrimalOf (RankedOf shaped))
  , OrdF shaped, OrdF (RankedOf shaped), OrdF (PrimalOf shaped)
  , OrdF (PrimalOf (RankedOf shaped))
  , Boolean (BoolOf shaped)
  , BoolOf shaped ~ BoolOf (RankedOf shaped)
  , BoolOf shaped ~ BoolOf (PrimalOf shaped)
  , BoolOf shaped ~ BoolOf (PrimalOf (RankedOf shaped))
  , ConvertTensor (RankedOf shaped) shaped
  , ConvertTensor (PrimalOf (RankedOf shaped)) (PrimalOf shaped)
  , RankedTensor (RankedOf shaped)
  , RankedTensor (PrimalOf (RankedOf shaped))
  )


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

type instance PrimalOf (Flip OR.Array) = Flip OR.Array

type instance DualOf (Flip OR.Array) = DummyDual

type instance DynamicOf (Flip OR.Array) = OD.Array

type instance DynamicOf (AstRanked s) = AstDynamic s

type instance RankedOf (Flip OR.Array) = Flip OR.Array

type instance ShapedOf (Flip OR.Array) = Flip OS.Array

instance RankedTensor (Flip OR.Array) where
  tshape = tshapeR . runFlip
  tminIndex = Flip . tminIndexR . runFlip
  tmaxIndex = Flip . tmaxIndexR . runFlip
  tfloor = Flip . tfloorR . runFlip
  tindex v ix = Flip $ tindexZR (runFlip v) (fromIndexOfR ix)
  tindex0 v ix = Flip . tscalarR $ tindex0R (runFlip v) (fromIndexOfR ix)
  tsum = Flip . tsumR . runFlip
  tsum0 = Flip . tscalarR . tsum0R . runFlip
  tdot0 u v = Flip $ tscalarR $ tdot0R (runFlip u) (runFlip v)
  tmatvecmul m v = Flip $ tmatvecmulR (runFlip m) (runFlip v)
  tmatmul2 m1 m2 = Flip $ tmatmul2R (runFlip m1) (runFlip m2)
  tscatter sh t f = Flip $ tscatterZR sh (runFlip t)
                                         (fromIndexOfR . f . toIndexOfR)
  tscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t)
                                           (fromIndexOfR . f . Flip . tscalarR)
  tfromList = Flip . tfromListR . map runFlip
  tfromList0N sh = Flip . tfromList0NR sh . map (tunScalarR . runFlip)
  tfromVector = Flip . tfromVectorR . V.map runFlip
  tfromVector0N sh = Flip . tfromVector0NR sh . V.map (tunScalarR . runFlip)
  treplicate k = Flip . treplicateR k . runFlip
  treplicate0N sh = Flip . treplicate0NR sh . tunScalarR . runFlip
  tappend u v = Flip $ tappendR (runFlip u) (runFlip v)
  tslice i n = Flip . tsliceR i n . runFlip
  treverse = Flip . treverseR . runFlip
  ttranspose perm = Flip . ttransposeR perm . runFlip
  treshape sh = Flip . treshapeR sh . runFlip
  tbuild1 k f = Flip $ tbuild1R k (runFlip . f . Flip . tscalarR)
  tmap0N f t = Flip $ tmap0NR (runFlip . f . Flip) (runFlip t)
  tzipWith0N f t u = Flip $ tzipWith0NR (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  tgather sh t f = Flip $ tgatherZR sh (runFlip t)
                                       (fromIndexOfR . f . toIndexOfR)
  tgather1 k t f = Flip $ tgatherZ1R k (runFlip t)
                                       (fromIndexOfR . f . Flip . tscalarR)
  tcast = Flip . tcastR . runFlip
  tfromIntegral = Flip . tfromIntegralR . runFlip

  tscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  tsumIn = Flip . tsumInR . runFlip
  tdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  tconst = Flip
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => Flip OR.Array r n -> DynamicExists OD.Array
              -> DynamicExists OD.Array
  raddDynamic r (DynamicExists @r2 d) = DynamicExists $
    if isTensorDummy d then dfromR r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromR r + d
      _ -> error "raddDynamic: type mismatch"

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains OD.Array (Flip OR.Array r n) where
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains a = V.singleton $ DynamicExists $ dfromR a
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if disDummy @(Flip OR.Array) a then Just (tzero (tshape aInit), rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> Just (tfromD a, rest)
          _ -> error $ "fromDomains: type mismatch: "
                       ++ show (typeRep @r) ++ " " ++ show (typeRep @r2)
    Nothing -> Nothing

instance ( GoodScalar r, KnownNat n
         , RankedTensor (AstRanked s), ConvertTensor (AstRanked s) (AstShaped s) )
         => AdaptableDomains (AstDynamic s) (AstRanked s r n) where
  type Value (AstRanked s r n) = Flip OR.Array r n
  toDomains = undefined
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if disDummy @(AstRanked s) a then Just (tzero (tshape aInit), rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> Just (tfromD a, rest)
          _ -> error $ "fromDomains: type mismatch: "
                       ++ show (typeRep @r) ++ " " ++ show (typeRep @r2)
    Nothing -> Nothing

instance RandomDomains (Flip OR.Array r n) where
  randomVals = undefined
  toValue = id


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

type instance PrimalOf (Flip OS.Array) = Flip OS.Array

type instance DualOf (Flip OS.Array) = DummyDual

type instance DynamicOf (Flip OS.Array) = OD.Array

type instance DynamicOf (AstShaped s) = AstDynamic s

type instance RankedOf (Flip OS.Array) = Flip OR.Array

type instance ShapedOf (Flip OS.Array) = Flip OS.Array

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
    if isTensorDummy d then dfromS r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromS r + d
      _ -> error "saddDynamic: type mismatch"

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual

instance (GoodScalar r, OS.Shape sh)
         => AdaptableDomains OD.Array (Flip OS.Array r sh) where
  type Value (Flip OS.Array r sh) = Flip OR.Array r (OS.Rank sh) -- ! not shaped
  toDomains a = V.singleton $ DynamicExists $ dfromS a
  fromDomains _aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if disDummy @(Flip OR.Array) a then Just (0, rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> Just (sfromD a, rest)
          _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

instance ( GoodScalar r, OS.Shape sh
         , ShapedTensor (AstShaped s), ConvertTensor (AstRanked s) (AstShaped s) )
         => AdaptableDomains (AstDynamic s) (AstShaped s r sh) where
  type Value (AstShaped s r sh) = Flip OS.Array r sh
  toDomains = undefined
  fromDomains _aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if disDummy @(AstRanked s) a then Just (0, rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> Just (sfromD a, rest)
          _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

instance (OS.Shape sh, Numeric r, Fractional r, Random r, Num (Vector r))
         => RandomDomains (Flip OS.Array r sh) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * realToFrac range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) g1
    in (Flip arr, g2)
  toValue = Flip . Data.Array.Convert.convert . runFlip

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


-- * ConvertTensor instance for concrete arrays

instance ConvertTensor (Flip OR.Array) (Flip OS.Array) where
  tfromD = Flip . Data.Array.Convert.convert
  tfromS = Flip . Data.Array.Convert.convert . runFlip
  dfromR = Data.Array.Convert.convert . runFlip
  dfromS = Data.Array.Convert.convert . runFlip
  sfromR = Flip . Data.Array.Convert.convert . runFlip
  sfromD = Flip . Data.Array.Convert.convert
  ddummy = dummyTensor
  disDummy = isTensorDummy
  dshape = OD.shapeL
