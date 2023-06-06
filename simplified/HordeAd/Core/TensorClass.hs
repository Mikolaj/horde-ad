{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( IntOf, IndexOf, ShapeInt
  , PrimalOf, DualOf, DynamicOf
  , ShapedTensor(..), Tensor(..), ConvertTensor(..), DomainsTensor(..), ADReady
  , GoodScalar, DummyDual(..), ttoRankedOrDummy
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Boolean
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits
  (KnownNat, Nat, SomeNat (..), someNatVal, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Internal.TensorOps

-- * Ranked tensor class definition

-- @IntOf a@ as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.

type family IntOf a

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf a n = Index n (IntOf a)

type GoodScalar r = (ShowAst r, RealFloat r, Floating (Vector r), RowSum r)

class Integral (IntOf a) => IntegralIntOf a where
instance Integral (IntOf a) => IntegralIntOf a where

class (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRankedR ranked c where
instance (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
         => CRankedR ranked c where

class (forall r20. GoodScalar r20 => c (ranked r20 0))
      => CRankedRR ranked c where
instance (forall r20. GoodScalar r20 => c (ranked r20 0))
         => CRankedRR ranked c where

class (forall r31. GoodScalar r31 => c (shaped r31 '[]))
      => CRankedSS shaped c where
instance
      (forall r31. GoodScalar r31 => c (shaped r31 '[]))
      => CRankedSS shaped c where

-- k is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family PrimalOf (tensor :: Type -> k -> Type) :: Type -> k -> Type

type family DualOf (tensor :: Type -> k -> Type) :: Type -> k -> Type

type family DynamicOf (tensor :: Type -> k -> Type) :: Type -> Type

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class (CRankedRR ranked IntegralIntOf, CRankedR ranked RealFloat)
      => Tensor (ranked :: Type -> Nat -> Type) where

  -- TODO: type Scalar r = ranked r 0
  -- is a macro/TH the only way?

  tlet :: (KnownNat n, KnownNat m, GoodScalar r)
       => ranked r n -> (ranked r n -> ranked r m)
       -> ranked r m
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
  tminIndex0 :: GoodScalar r => ranked r 1 -> IntOf (ranked r 0)  -- partial
  tminIndex :: (KnownNat n, GoodScalar r)
            => ranked r n -> IndexOf (ranked r 0) n
  tminIndex t = fromLinearIdx (tshape t) (tminIndex0 (tflatten t))
  tmaxIndex0 :: GoodScalar r => ranked r 1 -> IntOf (ranked r 0)  -- partial
  tmaxIndex :: (GoodScalar r, KnownNat n)
            => ranked r n -> IndexOf (ranked r 0) n
  tmaxIndex t = fromLinearIdx (tshape t) (tmaxIndex0 (tflatten t))
  tfloor :: GoodScalar r => ranked r 0 -> IntOf (ranked r 0)

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  tindex, (!) :: (GoodScalar r, KnownNat m, KnownNat n)
              => ranked r (m + n) -> IndexOf (ranked r 0) m -> ranked r n
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
  tindex0 :: (GoodScalar r, KnownNat m)
          => ranked r m -> IndexOf (ranked r 0) m -> ranked r 0
  tindex0 = tindex
  tsum :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r n
  tsum0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r 0
  tsum0 = tsum . tflatten
  tdot0 :: (GoodScalar r, KnownNat n) => ranked r n -> ranked r n -> ranked r 0
  tdot0 t u = tsum (tflatten (t `tmult` u))
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
  tminimum :: (GoodScalar r, KnownNat n)
           => ranked r n -> ranked r 0
  tminimum t = tindex0 t (tminIndex t)
  tmaximum :: (GoodScalar r, KnownNat n)
           => ranked r n -> ranked r 0
  tmaximum t = tindex0 t (tmaxIndex t)
  tfromIndex0 :: GoodScalar r => IntOf (ranked r 0) -> ranked r 0
  tfromIndex1 :: GoodScalar r => IndexOf (ranked r 0) n -> ranked r 1
  tfromIndex1 = tfromList . map tfromIndex0 . indexToList
  tscatter :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> ranked r (m + n)
           -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
           -> ranked r (p + n)
  tscatter1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
            => ShapeInt (p + n) -> ranked r (1 + n)
            -> (IntOf (ranked r 0) -> IndexOf (ranked r 0) p)
            -> ranked r (p + n)
  tscatter1 sh v f = tscatter @ranked @r @1 sh v
                              (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
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
         => ShapeInt (m + n) -> (IndexOf (ranked r 0) m -> ranked r n)
         -> ranked r (m + n)
  tbuild sh0 f0 =
    let buildSh :: KnownNat m1
                => ShapeInt m1 -> (IndexOf (ranked r 0) m1 -> ranked r n)
                -> ranked r (m1 + n)
        buildSh ZS f = f ZI
        buildSh (k :$ sh) f = tbuild1 k (\i -> buildSh sh (\ix -> f (i :. ix)))
    in buildSh (takeShape @m @n sh0) f0
  tbuild1 :: (GoodScalar r, KnownNat n)  -- this form needs less typeapps
          => Int -> (IntOf (ranked r 0) -> ranked r n) -> ranked r (1 + n)
  tmap :: (GoodScalar r, KnownNat m, KnownNat n)
       => (ranked r n -> ranked r n)
       -> ranked r (m + n) -> ranked r (m + n)
  tmap f v = tbuild (tshape v) (\ix -> f (v ! ix))
  tmap1 :: (GoodScalar r, KnownNat n)
        => (ranked r n -> ranked r n)
        -> ranked r (1 + n) -> ranked r (1 + n)
  tmap1 f u = tbuild1 (tlength u) (\i -> f (u ! [i]))
  tmap0N :: (GoodScalar r, KnownNat n)
         => (ranked r 0 -> ranked r 0) -> ranked r n -> ranked r n
  tmap0N f v = tbuild (tshape v) (\ix -> f $ tindex0 v ix)
  tzipWith :: (GoodScalar r, KnownNat m, KnownNat n)
           => (ranked r n -> ranked r n -> ranked r n)
           -> ranked r (m + n) -> ranked r (m + n) -> ranked r (m + n)
  tzipWith f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tzipWith1 :: (GoodScalar r, KnownNat n)
            => (ranked r n -> ranked r n -> ranked r n)
            -> ranked r (1 + n) -> ranked r (1 + n) -> ranked r (1 + n)
  tzipWith1 f u v = tbuild1 (tlength u) (\i -> f (u ! [i]) (v ! [i]))
  tzipWith0N :: (GoodScalar r, KnownNat n)
             => (ranked r 0 -> ranked r 0 -> ranked r 0)
             -> ranked r n -> ranked r n -> ranked r n
  tzipWith0N f u v = tbuild (tshape v) (\ix -> f (tindex0 u ix) (tindex0 v ix))
  tgather :: (GoodScalar r, KnownNat m, KnownNat n, KnownNat p)
          => ShapeInt (m + n) -> ranked r (p + n)
          -> (IndexOf (ranked r 0) m -> IndexOf (ranked r 0) p)
          -> ranked r (m + n)
  tgather1 :: forall r n p. (GoodScalar r, KnownNat n, KnownNat p)
           => Int -> ranked r (p + n)
           -> (IntOf (ranked r 0) -> IndexOf (ranked r 0) p)
           -> ranked r (1 + n)
  tgather1 k v f = tgather @ranked @r @1 (k :$ dropShape (tshape v)) v
                           (\(i :. ZI) -> f i)

  -- ** No serviceable parts beyond this point ** --

  -- Needed to avoid Num (ranked r n) constraints all over the place
  -- and also wrong shape in @0@ with ranked (not shaped) tensors.
  tzero :: (GoodScalar r, KnownNat n)
        => ShapeInt n -> ranked r n
  tzero sh = treplicate0N sh 0
  tsumOfList :: (GoodScalar r, KnownNat n)
             => [ranked r n] -> ranked r n  -- TODO: declare nonempty
  tsumOfList = sum
  tmult :: (GoodScalar r, KnownNat n)
        => ranked r n -> ranked r n -> ranked r n
  tmult = (*)
  tscaleByScalar :: (GoodScalar r, KnownNat n)
                 => ranked r 0 -> ranked r n -> ranked r n
  tscaleByScalar s v = v `tmult` treplicate0N (tshape v) s
  tsumIn :: (GoodScalar r, KnownNat n) => ranked r (2 + n) -> ranked r (1 + n)
  tsumIn = tsum . ttr
    -- TODO: generalize, replace by stride analysis, etc.
  tdot1In :: GoodScalar r => ranked r 2 -> ranked r 2 -> ranked r 1
  tdot1In t u = tsumIn (t `tmult` u)
    -- TODO: generalize, replace by stride analysis, etc.
  tconst :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  tconstBare :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  tconstBare = tconst
  tletWrap :: ADShare r -> ranked r n -> ranked r n
  tletWrap _l u = u
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => ranked r n -> DynamicOf ranked r -> DynamicOf ranked r
  tregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> [(AstVarId, DynamicOf ranked r)]
            -> ([(AstVarId, DynamicOf ranked r)], ranked r n)
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

class DomainsTensor (ranked :: Type -> Nat -> Type)
                    (domainsOf :: Type -> Type)
                    | ranked -> domainsOf, domainsOf -> ranked where
  tletDomains :: (GoodScalar r, KnownNat n)
              => domainsOf r
              -> (domainsOf r -> ranked r n)
              -> ranked r n
  dmkDomains :: Domains (DynamicOf ranked) r -> domainsOf r
  dlet :: (GoodScalar r, KnownNat n)
       => ranked r n -> (ranked r n -> domainsOf r)
       -> domainsOf r


-- * Shaped tensor class definition

class (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CRankedS shaped c where
instance
      (forall r30 y30. (OS.Shape y30, GoodScalar r30) => c (shaped r30 y30))
      => CRankedS shaped c where

class (CRankedSS shaped IntegralIntOf, CRankedS shaped RealFloat)
      => ShapedTensor (shaped :: Type -> [Nat] -> Type) where

  slet :: (OS.Shape sh, OS.Shape sh2, GoodScalar r)
       => shaped r sh -> (shaped r sh -> shaped r sh2)
       -> shaped r sh2
  slet a f = f a

  -- Integer codomain
  sshape :: forall sh r. (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => shaped r sh -> ShapeInt (OS.Rank sh)
  sshape _ = listShapeToShape $ OS.shapeT @sh
  srank :: forall sh r. (GoodScalar r, KnownNat (OS.Rank sh))
        => shaped r sh -> Int
  srank _ = valueOf @(OS.Rank sh)
  ssize :: forall sh r. (GoodScalar r, OS.Shape sh) => shaped r sh -> Int
  ssize _ = OS.sizeT @sh
  slength :: forall r n sh. (GoodScalar r, KnownNat n)
          => shaped r (n ': sh) -> Int
  slength _ = valueOf @n
  sminIndex0 :: GoodScalar r => shaped r '[n] -> IntOf (shaped r '[]) -- partial
  sminIndex :: ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
               , KnownNat (OS.Size sh) )
            => shaped r sh -> IndexOf (shaped r '[]) (OS.Rank sh)
  sminIndex t = fromLinearIdx (sshape t) (sminIndex0 (sflatten t))
  smaxIndex0 :: GoodScalar r => shaped r '[n] -> IntOf (shaped r '[]) -- partial
  smaxIndex :: ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
               , KnownNat (OS.Size sh) )
            => shaped r sh -> IndexOf (shaped r '[]) (OS.Rank sh)
  smaxIndex t = fromLinearIdx (sshape t) (smaxIndex0 (sflatten t))
  sfloor :: GoodScalar r => shaped r '[] -> IntOf (shaped r '[])

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  sindex, (!$) :: forall r m sh. (GoodScalar r, OS.Shape sh)
               => shaped r sh
               -> IndexOf (shaped r '[]) m
               -> shaped r (OS.Drop m sh)
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh2.
             (GoodScalar r, OS.Shape sh2, OS.Drop (OS.Rank sh2) sh2 ~ '[])
          => shaped r sh2 -> IndexOf (shaped r '[]) (OS.Rank sh2)
          -> shaped r '[]
  sindex0 = sindex
  ssum :: (GoodScalar r, OS.Shape sh) => shaped r (n ': sh) -> shaped r sh
  ssum0 :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
        => shaped r sh -> shaped r '[]
  ssum0 = ssum . sflatten
  sdot0 :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
        => shaped r sh -> shaped r sh -> shaped r '[]
  sdot0 t u = ssum (sflatten (t `smult` u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (i :. ZI)))
  smatmul2 :: (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 = case sshape m2 of
    _ :$ width2 :$ ZS ->
      ssum (stranspose @shaped @'[2,1,0] (sreplicate width2 m1)
            * stranspose @shaped @'[1,0] (sreplicate (slength m1) m2))
    _ -> error "impossible pattern needlessly required"
  sminimum :: forall r sh.
              ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
              , KnownNat (OS.Size sh) )
           => shaped r sh -> shaped r '[]
  sminimum t = gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
               $ t !$ sminIndex t
  smaximum :: forall r sh.
              ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
              , KnownNat (OS.Size sh) )
           => shaped r sh -> shaped r '[]
  smaximum t = gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
               $ t !$ smaxIndex t
  sfromIndex0 :: GoodScalar r => IntOf (shaped r '[]) -> shaped r '[]
  sfromIndex1 :: GoodScalar r => IndexOf (shaped r '[]) n -> shaped r '[n]
  sfromIndex1 = sfromList . map sfromIndex0 . indexToList
  sscatter
    :: forall r sh2 p sh. GoodScalar r
    => shaped r (sh2 OS.++ OS.Drop p sh)
    -> (IndexOf (shaped r '[]) (OS.Rank sh2) -> IndexOf (shaped r '[]) p)
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh. GoodScalar r
    => shaped r (n2 ': OS.Drop p sh)
    -> (IntOf (shaped r '[]) -> IndexOf (shaped r '[]) p)
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
  sfromList :: (GoodScalar r, OS.Shape sh)
            => [shaped r sh] -> shaped r (n ': sh)
  sfromList0N :: forall r sh.
                 ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
                 , KnownNat (OS.Size sh) )
              => [shaped r '[]] -> shaped r sh
  sfromList0N = sreshape @shaped @r @'[OS.Size sh] @sh . sfromList
  sfromVector :: (GoodScalar r, OS.Shape sh)
              => Data.Vector.Vector (shaped r sh) -> shaped r (n ': sh)
  sfromVector v = sfromList (V.toList v)  -- horribly inefficient for large vs
  sfromVector0N :: forall r sh.
                   ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
                   , KnownNat (OS.Size sh) )
                => Data.Vector.Vector (shaped r '[])
                -> shaped r sh
  sfromVector0N = sreshape @shaped @r @'[OS.Size sh] @sh . sfromVector
  sreplicate :: (GoodScalar r, OS.Shape sh)
             => Int -> shaped r sh -> shaped r (n ': sh)
  sreplicate0N :: forall r sh.
                  ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
                  , KnownNat (OS.Size sh) )
               => shaped r '[] -> shaped r sh
  sreplicate0N = sreshape @shaped @r @'[OS.Size sh] @sh
                 . sreplicate (OS.sizeT @sh)
  sappend :: (GoodScalar r, OS.Shape sh)
          => shaped r (n ': sh) -> shaped r (n ': sh) -> shaped r (n ': sh)
  sconcat :: (GoodScalar r, OS.Shape sh)
          => [shaped r (n ': sh)] -> shaped r (n ': sh)
  sconcat = foldr1 sappend
  sslice :: (GoodScalar r, OS.Shape sh)
         => Int -> Int -> shaped r (n ': sh) -> shaped r (n ': sh)
  suncons :: (GoodScalar r, KnownNat n, OS.Shape sh, KnownNat (OS.Rank sh))
          => shaped r (n ': sh) -> Maybe (shaped r sh, shaped r (n ': sh))
  suncons v = case sshape v of
                ZS -> Nothing
                len :$ _ -> Just (v !$ (0 :. ZI), sslice 1 (len - 1) v)
  sreverse :: (GoodScalar r, OS.Shape sh)
           => shaped r (n ': sh) -> shaped r (n ': sh)
  str :: (GoodScalar r, OS.Shape sh, KnownNat n, KnownNat m)
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose @shaped @'[1, 0]
  stranspose :: (OS.Permutation perm, GoodScalar r, OS.Shape sh)
             => shaped r sh -> shaped r (OS.Permute perm sh)
  sflatten :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[OS.Size sh]
  sflatten = sreshape
  sreshape :: (GoodScalar r, OS.Shape sh, OS.Shape sh2)
           => shaped r sh -> shaped r sh2
  sbuild :: forall r m sh.
            ( GoodScalar r, KnownNat m, OS.Shape sh
            , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
         => (IndexOf (shaped r '[]) m -> shaped r (OS.Drop m sh))
         -> shaped r sh
  sbuild =
    -- TODO : this is quite terrible. How to present this better?
    -- Rewrite orthotope in singletons?
    let shM = OS.shapeT @(OS.Drop m sh)
        buildSh
          :: forall (sh1 :: [Nat]). OS.Shape sh1
          => (IndexOf (shaped r '[]) (OS.Rank sh1) -> shaped r (OS.Drop m sh))
          -> shaped r (sh1 OS.++ OS.Drop m sh)
        buildSh f = case OS.shapeT @sh1 of
          [] -> gcastWith (unsafeCoerce Refl :: sh1 :~: '[])
                $ f ZI
          n : sh2 -> OS.withShapeP sh2 $ \(_proxy :: Proxy sh2) ->
                     OS.withShapeP (sh2 ++ shM) $ \(_proxyP :: Proxy shP) ->
            case someNatVal $ toInteger n of
              Just (SomeNat (_proxy :: Proxy n)) ->
                case someNatVal $ toInteger $ length sh2 of
                  Just (SomeNat (_proxy :: Proxy m2)) ->
                    gcastWith (unsafeCoerce Refl :: sh1 :~: n ': sh2)
                    $ gcastWith (unsafeCoerce Refl
                                 :: OS.Rank sh2 :~: m2)
                    $ gcastWith (unsafeCoerce Refl
                                 :: sh2 OS.++ OS.Drop m sh :~: shP)
                    $ sbuild1 @shaped @r @n @shP
                              (\i -> buildSh @sh2 (\ix -> f (i :. ix)))
                  Nothing -> error "sbuild: impossible someNatVal error"
              Nothing -> error "sbuild: impossible someNatVal error"
    in gcastWith (unsafeCoerce Refl :: m :~: OS.Rank (OS.Take m sh))
       $ gcastWith (unsafeCoerce Refl
                    :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
       $ buildSh @(OS.Take m sh)
  sbuild1 :: forall r n sh. (GoodScalar r, OS.Shape sh)
          => (IntOf (shaped r '[]) -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: ( GoodScalar r, KnownNat m, OS.Shape sh
          , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
       => (shaped r (OS.Drop m sh) -> shaped r (OS.Drop m sh))
       -> shaped r sh -> shaped r sh
  smap f v = sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r sh n. (GoodScalar r, OS.Shape sh, KnownNat n)
        => (shaped r sh -> shaped r sh)
        -> shaped r (n ': sh) -> shaped r (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ (i :. ZI)))
  smap0N :: forall r sh.
            ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
            , OS.Shape (OS.Take (OS.Rank sh) sh) )
         => (shaped r '[] -> shaped r '[]) -> shaped r sh -> shaped r sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ sbuild (\ix -> f $ sindex0 v ix)
  szipWith :: ( GoodScalar r, KnownNat m, OS.Shape sh
              , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
           => (shaped r (OS.Drop m sh)
               -> shaped r (OS.Drop m sh)
               -> shaped r (OS.Drop m sh))
           -> shaped r sh -> shaped r sh -> shaped r sh
  szipWith f u v = sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r sh n. (GoodScalar r, OS.Shape sh, KnownNat n)
            => (shaped r sh -> shaped r sh -> shaped r sh)
            -> shaped r (n ': sh) -> shaped r (n ': sh) -> shaped r (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (i :. ZI))
                                     (v !$ (i :. ZI)))
  szipWith0N :: forall r sh.
                ( GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh)
                , OS.Shape (OS.Take (OS.Rank sh) sh) )
             => (shaped r '[] -> shaped r '[] -> shaped r '[])
             -> shaped r sh -> shaped r sh -> shaped r sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ sbuild (\ix -> f (sindex0 u ix) (sindex0 v ix))
  sgather
    :: forall r sh2 p sh. GoodScalar r
    => shaped r sh
    -> (IndexOf (shaped r '[]) (OS.Rank sh2) -> IndexOf (shaped r '[]) p)
    -> shaped r (sh2 OS.++ OS.Drop p sh)
  sgather1
    :: forall r n2 p sh. GoodScalar r
    => shaped r sh
    -> (IntOf (shaped r '[]) -> IndexOf (shaped r '[]) p)
    -> shaped r (n2 ': OS.Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (\(i :. ZI) -> f i)

  -- ** No serviceable parts beyond this point ** --

  ssumOfList :: (GoodScalar r, OS.Shape sh)
             => [shaped r sh] -> shaped r sh  -- TODO: declare nonempty
  ssumOfList = sum
  smult :: (GoodScalar r, OS.Shape sh)
        => shaped r sh -> shaped r sh -> shaped r sh
  smult = (*)
  sscaleByScalar
    :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh), KnownNat (OS.Size sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v `smult` sreplicate0N s
  ssumIn :: (GoodScalar r, OS.Shape sh, KnownNat n, KnownNat m)
         => shaped r (n ': m ': sh) -> shaped r (n ': sh)
  ssumIn = ssum . str
    -- TODO: generalize, replace by stride analysis, etc.
  sdot1In :: (GoodScalar r, KnownNat n, KnownNat m)
          => shaped r '[n, m] -> shaped r '[n, m] -> shaped r '[n]
  sdot1In t u = ssumIn (t `smult` u)
    -- TODO: generalize, replace by stride analysis, etc.
  sconst :: (GoodScalar r, OS.Shape sh) => OS.Array sh r -> shaped r sh
  sconstBare :: (GoodScalar r, OS.Shape sh) => OS.Array sh r -> shaped r sh
  sconstBare = sconst
  sletWrap :: ADShare r -> shaped r sh -> shaped r sh
  sletWrap _l u = u

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


-- * ConvertTensor class definition

class ( DynamicOf ranked ~ DynamicOf shaped
      , DynamicOf shaped ~ DynamicOf ranked )
      => ConvertTensor (ranked :: Type -> Nat -> Type)
                       (shaped :: Type -> [Nat] -> Type)
                       | ranked -> shaped, shaped -> ranked where
  tfromD :: (GoodScalar r, KnownNat n)
         => DynamicOf ranked r -> ranked r n
  tfromS :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => shaped r sh -> ranked r (OS.Rank sh)
  dfromR :: (GoodScalar r, KnownNat n)
         => ranked r n -> DynamicOf ranked r
  dfromS :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => shaped r sh -> DynamicOf shaped r
  sfromR :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => ranked r (OS.Rank sh) -> shaped r sh
  sfromD :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => DynamicOf shaped r -> shaped r sh
  ddummy :: Numeric r => DynamicOf ranked r
  disDummy :: Numeric r => DynamicOf ranked r -> Bool
  dshape :: GoodScalar r => DynamicOf ranked r -> [Int]


-- * The giga-constraint

type Many ranked (f :: Type -> Constraint) r = (f (ranked r 0), f (ranked r 1), f (ranked r 2), f (ranked r 3), f (ranked r 4), f (ranked r 5), f (ranked r 6), f (ranked r 7), f (ranked r 8), f (ranked r 9), f (ranked r 10), f (ranked r 11), f (ranked r 12))

type ADReady ranked r =
  ( Tensor ranked, GoodScalar r, Tensor (PrimalOf ranked)
  , IfB (IntOf (ranked r 0)), Many ranked IfB r
  , Many (PrimalOf ranked) IfB r
  , EqB r, EqB (IntOf (ranked r 0)), Many ranked EqB r
  , Many (PrimalOf ranked) EqB r
  , OrdB r, OrdB (IntOf (ranked r 0)), Many ranked OrdB r
  , Many (PrimalOf ranked) OrdB r
  , Boolean (BooleanOf (IntOf (ranked r 0)))
  , ( BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 1)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 2)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 3)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 4)
{- TODO: GHC 9.4 and 9.6 can't cope with too many of these:
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 5)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 6) -}
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 7)
{-
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 8)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 9)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 10)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 11)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 12) -} )
  , ( BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 0)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 1)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 2)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 3)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 4)
{-
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 5)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 6)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 7)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 8)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 9)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 10)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 11)
    , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (PrimalOf ranked r 12) -} )
  , BooleanOf (IntOf (ranked r 0)) ~ BooleanOf (ranked r 0)
      -- placing this last gives better errors
  )


-- * Ranked tensor class instance for concrete arrays

type instance IntOf (Flip OR.Array r n) = CInt

type instance PrimalOf (Flip OR.Array) = Flip OR.Array

type instance DualOf (Flip OR.Array) = DummyDual

type instance DynamicOf (Flip OR.Array) = OD.Array

instance Tensor (Flip OR.Array) where
  tshape = tshapeR . runFlip
  tminIndex0 = tminIndexR . runFlip
  tmaxIndex0 = tmaxIndexR . runFlip
  tfloor = floor . tunScalarR . runFlip
  tindex v ix = Flip $ tindexZR (runFlip v) ix
  tindex0 v ix = Flip . tscalarR $ tindex0R (runFlip v) ix
  tsum = Flip . tsumR . runFlip
  tsum0 = Flip . tscalarR . tsum0R . runFlip
  tdot0 u v = Flip $ tscalarR $ tdot0R (runFlip u) (runFlip v)
  tmatvecmul m v = Flip $ tmatvecmulR (runFlip m) (runFlip v)
  tmatmul2 m1 m2 = Flip $ tmatmul2R (runFlip m1) (runFlip m2)
  tfromIndex0 = Flip . tscalarR . fromIntegral
  tscatter sh t f = Flip $ tscatterZR sh (runFlip t) f
  tscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t) f
  tfromList = Flip . tfromListR . map runFlip
  tfromList0N sh = Flip . tfromList0NR sh . map (tunScalarR . runFlip)
  tfromVector = Flip . tfromVectorR . V.map runFlip
  tfromVector0N sh = Flip . tfromVector0NR sh . V.map (tunScalarR . runFlip)
  treplicate k = Flip . treplicateR k . runFlip
  treplicate0N sh = Flip . treplicate0NR sh . tunScalarR . runFlip
  tappend u v = Flip $ tappendR (runFlip u) (runFlip v)
  tslice i k = Flip . tsliceR i k . runFlip
  treverse = Flip . treverseR . runFlip
  ttranspose perm = Flip . ttransposeR perm . runFlip
  treshape sh = Flip . treshapeR sh . runFlip
  tbuild sh f = Flip $ tbuildNR sh (runFlip . f)
  tbuild1 k f = Flip $ tbuild1R k (runFlip . f)
  tmap0N f t = Flip $ tmap0NR (runFlip . f . Flip) (runFlip t)
  tzipWith0N f t u = Flip $ tzipWith0NR (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  tgather sh t f = Flip $ tgatherZR sh (runFlip t) f
  tgather1 k t f = Flip $ tgatherZ1R k (runFlip t) f
  tscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  tsumIn = Flip . tsumInR . runFlip
  tdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  tconst = Flip
  raddDynamic r d = if isTensorDummy d then dfromR r else dfromR r + d

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

data DummyDual a (b :: k) = DummyDual

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains OD.Array (Flip OR.Array r n) where
  type Underlying (Flip OR.Array r n) = r
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains a = V.singleton (dfromR a)
  fromDomains aInit params = case V.uncons params of
    Just (a, rest) ->
      Just (ttoRankedOrDummy (tshape aInit) a, rest)
    Nothing -> Nothing

ttoRankedOrDummy
  :: forall ranked shaped n r.
     (KnownNat n, Tensor ranked, GoodScalar r, ConvertTensor ranked shaped)
  => ShapeInt n -> DynamicOf ranked r -> ranked r n
ttoRankedOrDummy sh x = if disDummy @ranked x
                        then tzero sh
                        else tfromD x

instance KnownNat n
         => RandomDomains (Flip OR.Array r n) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OR.fromVector undefined
              $ createRandomVector (OR.size undefined) g1  -- TODO, or just remove the instance
    in (Flip arr, g2)
  type ToRanked (Flip OR.Array r n) = Flip OR.Array r n
  toRanked = id


-- * Shaped tensor class instance for concrete arrays

type instance IntOf (Flip OS.Array r sh) = CInt

type instance PrimalOf (Flip OS.Array) = Flip OS.Array

type instance DualOf (Flip OS.Array) = DummyDual

type instance DynamicOf (Flip OS.Array) = OD.Array

instance ShapedTensor (Flip OS.Array) where

type instance IntOf (AstShaped r sh) = AstInt r

instance ShapedTensor AstShaped where

instance (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => AdaptableDomains OD.Array (Flip OS.Array r sh) where
  type Underlying (Flip OS.Array r sh) = r
  type Value (Flip OS.Array r sh) = Flip OS.Array r sh
  toDomains a = V.singleton (dfromS a)
  fromDomains _aInit params = case V.uncons params of
    Just (a, rest) -> Just (stoRankedOrDummy a, rest)
    Nothing -> Nothing

stoRankedOrDummy
  :: forall ranked shaped sh r.
     ( OS.Shape sh, KnownNat (OS.Rank sh), ShapedTensor shaped, GoodScalar r
     , ConvertTensor ranked shaped )
  => DynamicOf shaped r -> shaped r sh
stoRankedOrDummy x = if disDummy @ranked x
                        then 0
                        else sfromD x

instance OS.Shape sh
         => RandomDomains (Flip OS.Array r sh) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OS.fromVector $ createRandomVector (OS.sizeP (Proxy @sh)) g1
    in (Flip arr, g2)
  type ToRanked (Flip OS.Array r sh) = Flip OR.Array r (OS.Rank sh)
  toRanked = Flip . Data.Array.Convert.convert . runFlip

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
