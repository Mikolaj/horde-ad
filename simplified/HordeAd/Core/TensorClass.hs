{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( ShapeInt, IntOf, IndexOf, ShapeSh, IntSh, IndexSh
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
  (KnownNat, Nat, OrderingI (..), cmpNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.ShapedList
  (ShapeSh, ShapedList (..), ShapedNat, consShaped)
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorOps

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

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IntSh a (n :: Nat) = ShapedNat n (IntOf a)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh a (sh :: [Nat]) = ShapedList sh (IntOf a)

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
        buildSh (k :$ sh) f =
          let g i = buildSh sh (\ix -> f (i :. ix))
          in tbuild1 k g
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
  sminIndex0 :: (GoodScalar r, KnownNat n)
             => shaped r '[n] -> IntSh (shaped r '[]) n  -- partial
  sminIndex :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
            => shaped r sh -> IndexSh (shaped r '[]) sh
  sminIndex t = ShapedList.fromLinearIdx (sshape t) (sminIndex0 (sflatten t))
  smaxIndex0 :: (GoodScalar r, KnownNat n)
             => shaped r '[n] -> IntSh (shaped r '[]) n  -- partial
  smaxIndex :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
            => shaped r sh -> IndexSh (shaped r '[]) sh
  smaxIndex t = ShapedList.fromLinearIdx (sshape t) (smaxIndex0 (sflatten t))
  sfloor :: GoodScalar r => shaped r '[] -> IntOf (shaped r '[])
    -- not IntSh, because the integer can be negative
    -- TODO: shall we make it abs (floor v)?

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  sindex, (!$) :: forall r sh1 sh2.
                  (GoodScalar r, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2))
               => shaped r (sh1 OS.++ sh2) -> IndexSh (shaped r '[]) sh1
               -> shaped r sh2
  infixl 9 !$
  (!$) = sindex  -- prefix form better when type applications are necessary
  sindex0 :: forall r sh1. (GoodScalar r, OS.Shape sh1)
          => shaped r sh1 -> IndexSh (shaped r '[]) sh1
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
  sdot0 t u = ssum (sflatten (t `smult` u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (consShaped i ZSH)))
  smatmul2 :: forall r n m p. (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Proxy @'[2,1,0]) (sreplicate @shaped @r @p m1)
          * stranspose (Proxy @'[1,0]) (sreplicate @shaped @r @m m2))
  sminimum :: forall r sh. (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[]
  sminimum t = gcastWith (unsafeCoerce Refl :: (sh OS.++ '[])  :~: sh)
               $ t !$ sminIndex t
  smaximum :: forall r sh.(GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[]
  smaximum t = gcastWith (unsafeCoerce Refl :: (sh OS.++ '[])  :~: sh)
               $ t !$ smaxIndex t
  sfromIndex0 :: forall n r. (GoodScalar r, KnownNat n)
              => IntSh (shaped r '[]) n -> shaped r '[]
  sfromIndex1 :: forall r sh. (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
              => IndexSh (shaped r '[]) sh -> shaped r '[OS.Rank sh]
  sfromIndex1 =
    let go :: IndexSh (shaped r '[]) sh1 -> [shaped r '[]]
        go ZSH = []
        go ((:$:) @n i rest) = sfromIndex0 @shaped @n (ShapedList.shapedNat i)
                               : go rest
    in sfromList . go
  sscatter
    :: forall r sh2 p sh.
       ( GoodScalar r, OS.Shape sh2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh), OS.Shape (sh2 OS.++ OS.Drop p sh) )
    => shaped r (sh2 OS.++ OS.Drop p sh)
    -> (IndexSh (shaped r '[]) sh2 -> IndexSh (shaped r '[]) (OS.Take p sh))
    -> shaped r sh
  sscatter1
    :: forall r n2 p sh.
       ( GoodScalar r, KnownNat n2, OS.Shape sh, OS.Shape (OS.Take p sh)
       , OS.Shape (OS.Drop p sh) )
    => shaped r (n2 ': OS.Drop p sh)
    -> (IntSh (shaped r '[]) n2 -> IndexSh (shaped r '[]) (OS.Take p sh))
    -> shaped r sh
  sscatter1 v f = sscatter @shaped @r @'[n2] v (ShapedList.unconsContShaped f)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
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
  sslice :: (GoodScalar r, KnownNat i, KnownNat k, KnownNat n, OS.Shape sh)
         => Proxy i -> Proxy k
         -> shaped r (i + n + k ': sh) -> shaped r (n ': sh)
  suncons :: forall r n sh. (GoodScalar r, KnownNat n, OS.Shape sh)
          => shaped r (n ': sh) -> Maybe (shaped r sh, shaped r (n - 1 ': sh))
  suncons v = case cmpNat (Proxy @1) (Proxy @n) of
    EQI -> Just (v !$ (0 :$: ZSH), sslice (Proxy @1) (Proxy @0) v)
    LTI -> Just (v !$ (0 :$: ZSH), sslice (Proxy @1) (Proxy @0) v)
    _ -> Nothing
  sreverse :: (GoodScalar r, KnownNat n, OS.Shape sh)
           => shaped r (n ': sh) -> shaped r (n ': sh)
  str :: ( GoodScalar r, KnownNat n, KnownNat m, OS.Shape sh
         , KnownNat (OS.Rank sh) )
      => shaped r (n ': m ': sh) -> shaped r (m ': n ': sh)
  str = stranspose (Proxy @'[1, 0])
  stranspose :: forall perm r sh.
                ( OS.Permutation perm, OS.Shape perm, GoodScalar r
                , OS.Shape sh, KnownNat (OS.Rank sh)
                , OS.Rank perm <= OS.Rank sh )
             => Proxy perm -> shaped r sh -> shaped r (OS.Permute perm sh)
  sflatten :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[OS.Size sh]
  sflatten = sreshape
  sreshape :: ( GoodScalar r, OS.Shape sh, OS.Shape sh2
              , OS.Size sh ~ OS.Size sh2 )
           => shaped r sh -> shaped r sh2
  sbuild :: forall r m sh.
            (GoodScalar r, KnownNat m, OS.Shape sh, OS.Shape (OS.Take m sh))
         => (IndexSh (shaped r '[]) (OS.Take m sh) -> shaped r (OS.Drop m sh))
         -> shaped r sh
  sbuild =
    let buildSh
          :: forall sh1.
             ShapeSh sh1 -> ShapeSh (sh1 OS.++ OS.Drop m sh)
          -> (IndexSh (shaped r '[]) sh1 -> shaped r (OS.Drop m sh))
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
          => (IntSh (shaped r '[]) n -> shaped r sh)
          -> shaped r (n ': sh)
  smap :: forall r m sh. ( GoodScalar r, KnownNat m, OS.Shape sh
                         , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
       => (shaped r (OS.Drop m sh) -> shaped r (OS.Drop m sh))
       -> shaped r sh -> shaped r sh
  smap f v = gcastWith (unsafeCoerce Refl
                        :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
             $ sbuild (\ix -> f (v !$ ix))
  smap1 :: forall r sh n. (GoodScalar r, KnownNat n, OS.Shape sh)
        => (shaped r sh -> shaped r sh)
        -> shaped r (n ': sh) -> shaped r (n ': sh)
  smap1 f u = sbuild1 (\i -> f (u !$ (consShaped i ZSH)))
  smap0N :: forall r sh.
            (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => (shaped r '[] -> shaped r '[]) -> shaped r sh -> shaped r sh
  smap0N f v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ sbuild @shaped @r @(OS.Rank sh) (\ix -> f $ sindex0 v ix)
  szipWith :: forall r m sh.
              ( GoodScalar r, KnownNat m, OS.Shape sh
              , OS.Shape (OS.Take m sh), OS.Shape (OS.Drop m sh) )
           => (shaped r (OS.Drop m sh)
               -> shaped r (OS.Drop m sh)
               -> shaped r (OS.Drop m sh))
           -> shaped r sh -> shaped r sh -> shaped r sh
  szipWith f u v = gcastWith (unsafeCoerce Refl
                              :: sh :~: OS.Take m sh OS.++ OS.Drop m sh)
                   $ sbuild (\ix -> f (u !$ ix) (v !$ ix))
  szipWith1 :: forall r sh n. (GoodScalar r, KnownNat n, OS.Shape sh)
            => (shaped r sh -> shaped r sh -> shaped r sh)
            -> shaped r (n ': sh) -> shaped r (n ': sh) -> shaped r (n ': sh)
  szipWith1 f u v = sbuild1 (\i -> f (u !$ (consShaped i ZSH))
                                     (v !$ (consShaped i ZSH)))
  szipWith0N :: forall r sh.
                (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
             => (shaped r '[] -> shaped r '[] -> shaped r '[])
             -> shaped r sh -> shaped r sh -> shaped r sh
  szipWith0N f u v =
    gcastWith (unsafeCoerce Refl :: OS.Drop (OS.Rank sh) sh :~: '[])
    $ gcastWith (unsafeCoerce Refl :: OS.Take (OS.Rank sh) sh :~: sh)
    $ sbuild @shaped @r @(OS.Rank sh) (\ix -> f (sindex0 u ix) (sindex0 v ix))
  sgather
    :: forall r sh2 p sh.
       ( GoodScalar r, OS.Shape sh2, OS.Shape sh, OS.Shape (OS.Drop p sh)
       , OS.Shape (sh2 OS.++ OS.Drop p sh) )
    => shaped r sh
    -> (IndexSh (shaped r '[]) sh2 -> IndexSh (shaped r '[]) (OS.Take p sh))
    -> shaped r (sh2 OS.++ OS.Drop p sh)
  sgather1
    :: forall r n2 p sh.
       (GoodScalar r, KnownNat n2, OS.Shape sh, OS.Shape (OS.Drop p sh))
    => shaped r sh
    -> (IntSh (shaped r '[]) n2 -> IndexSh (shaped r '[]) (OS.Take p sh))
    -> shaped r (n2 ': OS.Drop p sh)
  sgather1 v f = sgather @shaped @r @'[n2] v (ShapedList.unconsContShaped f)

  -- ** No serviceable parts beyond this point ** --

  ssumOfList :: (GoodScalar r, OS.Shape sh)
             => [shaped r sh] -> shaped r sh  -- TODO: declare nonempty
  ssumOfList = sum
  smult :: (GoodScalar r, OS.Shape sh)
        => shaped r sh -> shaped r sh -> shaped r sh
  smult = (*)
  sscaleByScalar
    :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
    => shaped r '[] -> shaped r sh -> shaped r sh
  sscaleByScalar s v = v `smult` sreplicate0N s
  ssumIn :: ( GoodScalar r, OS.Shape sh, KnownNat n, KnownNat m
            , KnownNat (OS.Rank sh) )
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
  saddDynamic :: forall r sh. (GoodScalar r, OS.Shape sh)
              => shaped r sh -> DynamicOf shaped r -> DynamicOf shaped r
  sregister :: (GoodScalar r, OS.Shape sh)
            => shaped r sh -> [(AstVarId, DynamicOf shaped r)]
            -> ([(AstVarId, DynamicOf shaped r)], shaped r sh)
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
      => ConvertTensor (ranked :: Type -> Nat -> Type)
                       (shaped :: Type -> [Nat] -> Type)
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
  sfromD :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
         => DynamicOf shaped r -> shaped r sh
  ddummy :: Numeric r => DynamicOf ranked r
  disDummy :: Numeric r => DynamicOf ranked r -> Bool
  dshape :: GoodScalar r => DynamicOf ranked r -> [Int]

class DomainsTensor (ranked :: Type -> Nat -> Type)
                    (shaped :: Type -> [Nat] -> Type)
                    (domainsOf :: Type -> Type)
                    | ranked -> shaped domainsOf
                    , shaped -> ranked domainsOf
                    , domainsOf -> ranked shaped where
  dmkDomains :: Domains (DynamicOf ranked) r -> domainsOf r
  rletDomainsOf :: (GoodScalar r, KnownNat n)
              => domainsOf r
              -> (domainsOf r -> ranked r n)
              -> ranked r n
  rletToDomainsOf :: (GoodScalar r, KnownNat n)
       => ranked r n -> (ranked r n -> domainsOf r)
       -> domainsOf r
  sletDomainsOf :: (GoodScalar r, OS.Shape sh)
              => domainsOf r
              -> (domainsOf r -> shaped r sh)
              -> shaped r sh
  sletToDomainsOf :: (GoodScalar r, OS.Shape sh)
       => shaped r sh -> (shaped r sh -> domainsOf r)
       -> domainsOf r


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
  tminIndex0 = tminIndex0R . runFlip
  tmaxIndex0 = tmaxIndex0R . runFlip
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
  sminIndex0 = tminIndex0S . runFlip
  smaxIndex0 = tmaxIndex0S . runFlip
  sfloor = floor . tunScalarS . runFlip
  sindex v ix = Flip $ tindexZS (runFlip v) ix
  sindex0 v ix = Flip . tscalarS $ tindex0S (runFlip v) ix
  ssum = Flip . tsumS . runFlip
  ssum0 = Flip . tscalarS . tsum0S . runFlip
  sdot0 u v = Flip $ tscalarS $ tdot0S (runFlip u) (runFlip v)
  smatvecmul m v = Flip $ tmatvecmulS (runFlip m) (runFlip v)
  smatmul2 m1 m2 = Flip $ tmatmul2S (runFlip m1) (runFlip m2)
  sfromIndex0 = Flip . tscalarS . fromIntegral . ShapedList.unShapedNat
  sscatter t f = Flip $ tscatterZS (runFlip t) f
  sscatter1 t f = Flip $ tscatterZ1S (runFlip t) f
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
  sbuild1 f = Flip $ tbuild1S (runFlip . f)
  smap0N f t = Flip $ tmap0NS (runFlip . f . Flip) (runFlip t)
  szipWith0N f t u = Flip $ tzipWith0NS (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  sgather t f = Flip $ tgatherZS (runFlip t) f
  sgather1 t f = Flip $ tgatherZ1S (runFlip t) f

  sscaleByScalar s v =
    Flip $ tscaleByScalarS (tunScalarS $ runFlip s) (runFlip v)
  ssumIn = Flip . tsumInS . runFlip
  sdot1In u v = Flip $ tdot1InS (runFlip u) (runFlip v)
  sconst = Flip
  saddDynamic r d = if isTensorDummy d then dfromS r else dfromS r + d

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual

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
